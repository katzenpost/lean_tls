"""Extract the RFC 8448 §3 (simple 1-RTT) trace into named hex values.

Usage: python3 -I scripts/extract_rfc8448.py rfc8448.txt > testdata/rfc8448_1rtt.json
"""
import json, re, sys

text = open(sys.argv[1]).read().splitlines()
start = next(i for i, l in enumerate(text) if l.startswith("3.  Simple 1-RTT Handshake"))
end = next(i for i, l in enumerate(text) if l.startswith("4.  Resumed 0-RTT Handshake"))
lines = [l for l in text[start:end] if not l.startswith("RFC 8448") and not l.startswith("Thomson")]

entries, ctx, cur = [], None, None
for l in lines:
    m = re.match(r"^   \{(client|server)\}\s+(.*?):?$", l)
    if m:
        ctx, cur = m.group(1) + ": " + m.group(2), None
        continue
    m = re.match(r"^      (.+?) \((\d+) octets\):\s+([0-9a-f ]+)$", l)
    if m:
        cur = {"ctx": ctx, "name": m.group(1), "size": int(m.group(2)), "hex": m.group(3).replace(" ", "")}
        entries.append(cur)
        continue
    m = re.match(r"^\s{8,}([0-9a-f]{2}( [0-9a-f]{2})*)\s*$", l)
    if m and cur is not None:
        cur["hex"] += m.group(1).replace(" ", "")
        continue
    if l.strip():
        cur = None

for e in entries:
    assert len(e["hex"]) == 2 * e["size"], e

def pick(ctx, name, nth=0):
    hits = [e["hex"] for e in entries if e["ctx"].startswith(ctx) and e["name"] == name]
    return hits[nth]

v = {
    "client_x25519_private": pick("client: create an ephemeral x25519 key pair", "private key"),
    "client_x25519_public": pick("client: create an ephemeral x25519 key pair", "public key"),
    "server_x25519_private": pick("server: create an ephemeral x25519 key pair", "private key"),
    "server_x25519_public": pick("server: create an ephemeral x25519 key pair", "public key"),
    "client_hello": pick("client: construct a ClientHello", "ClientHello"),
    "server_hello": pick("server: construct a ServerHello", "ServerHello"),
    "encrypted_extensions": pick("server: construct an EncryptedExtensions", "EncryptedExtensions"),
    "certificate": pick("server: construct a Certificate", "Certificate"),
    "certificate_verify": pick("server: construct a CertificateVerify", "CertificateVerify"),
    "server_finished": pick("server: construct a Finished", "Finished"),
    "client_finished": pick("client: construct a Finished", "Finished"),
    "early_secret": pick('server: extract secret "early"', "secret"),
    "ecdhe": pick('server: extract secret "handshake"', "IKM"),
    "handshake_secret": pick('server: extract secret "handshake"', "secret"),
    "client_handshake_traffic": pick('server: derive secret "tls13 c hs traffic"', "expanded"),
    "server_handshake_traffic": pick('server: derive secret "tls13 s hs traffic"', "expanded"),
    "master_secret": pick('server: extract secret "master"', "secret"),
    "client_application_traffic": pick('server: derive secret "tls13 c ap traffic"', "expanded"),
    "server_application_traffic": pick('server: derive secret "tls13 s ap traffic"', "expanded"),
    "server_handshake_key": pick("server: derive write traffic keys for handshake data", "key expanded"),
    "server_handshake_iv": pick("server: derive write traffic keys for handshake data", "iv expanded"),
}
json.dump({"source": "RFC 8448 §3 Simple 1-RTT Handshake", "vectors": v}, sys.stdout, indent=1)
print()
