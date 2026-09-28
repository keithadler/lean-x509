// Go crypto/x509: parse, then Verify with the corpus's anchor, intermediates, host and time.
package main

import (
	"crypto/x509"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"
)

type Case struct {
	ID     string   `json:"id"`
	Leaf   string   `json:"leaf"`
	Chain  []string `json:"chain"`
	Anchor string   `json:"anchor"`
	Host   string   `json:"host"`
}

type Manifest struct {
	Now   int64  `json:"now"`
	Cases []Case `json:"cases"`
}

func load(dir, name string) (*x509.Certificate, error) {
	b, err := os.ReadFile(filepath.Join(dir, name))
	if err != nil {
		return nil, err
	}
	return x509.ParseCertificate(b)
}

func run(dir string, now time.Time, c Case) error {
	leaf, err := load(dir, c.Leaf)
	if err != nil {
		return fmt.Errorf("parse leaf: %w", err)
	}
	roots, inters := x509.NewCertPool(), x509.NewCertPool()
	a, err := load(dir, c.Anchor)
	if err != nil {
		return fmt.Errorf("parse anchor: %w", err)
	}
	roots.AddCert(a)
	for _, n := range c.Chain {
		ic, err := load(dir, n)
		if err != nil {
			return fmt.Errorf("parse intermediate: %w", err)
		}
		inters.AddCert(ic)
	}
	_, err = leaf.Verify(x509.VerifyOptions{DNSName: c.Host, Roots: roots, Intermediates: inters,
		CurrentTime: now, KeyUsages: []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth}})
	return err
}

func main() {
	dir := os.Args[1]
	var m Manifest
	b, _ := os.ReadFile(filepath.Join(dir, "manifest.json"))
	if err := json.Unmarshal(b, &m); err != nil {
		panic(err)
	}
	now := time.Unix(m.Now, 0).UTC()
	for _, c := range m.Cases {
		err := run(dir, now, c)
		out := map[string]any{"id": c.ID, "ok": err == nil}
		if err != nil {
			out["err"] = err.Error()
		}
		j, _ := json.Marshal(out)
		fmt.Println(string(j))
	}
}
