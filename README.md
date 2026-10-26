# lean_tls

*TLS 1.3 for QUIC, in Lean 4.*

This library has not been audited by any third party.

lean_tls is the TLS 1.3 handshake (RFC 8446) as QUIC carries it (RFC 9001): handshake messages
over three encryption levels and the key schedule that yields each level's secrets. There is no
record layer, no TLS 1.2 and no DTLS; QUIC protects its own packets. The handshake is a pure state
machine with no IO and no randomness of its own: it is given CRYPTO stream bytes and a 32-byte
seed per connection, and answers with bytes to send and secrets to install. Its primitives come
from [Cryptlib](https://github.com/katzenpost/cryptlib).

## What it negotiates

* Key exchange: `X25519MLKEM768` (0x11ec, draft-ietf-tls-ecdhe-mlkem), the hybrid of ML-KEM-768
  and X25519. `x25519` and `MLKEM768` are also defined.
* Cipher suites: `TLS_CHACHA20_POLY1305_SHA256`, preferred, and `TLS_AES_128_GCM_SHA256`.
* Authentication: the server signs with Ed25519; the client pins `SHA-256(SubjectPublicKeyInfo)`
  of its certificate, as katzenpost's QUIC transport does. Certificates are self-signed in the
  shape of katzenpost's `epochCertificate`. No chain validation, no client certificates.
* 1-RTT only: no PSK, no resumption, no 0-RTT, no HelloRetryRequest. Session tickets from the
  server are ignored.

## Laws in the types

As in Cryptlib, the correctness of a building block is a field of its type, so a composition
carries the laws of its parts.

* `KeyShare` is a named group with the law `agree`: an honest client completes the secret the
  server derived from its share. `KeyShare.ofNIKE` takes `agree` from a NIKE's commutativity,
  `KeyShare.ofKEM` from a KEM's round trip, and `KeyShare.concat` assembles it from two groups'.
  `x25519mlkem768` is `concat mlkem768 x25519` and needs no proof of its own.
* `CipherSuite` carries a Cryptlib `AEAD` and with it that AEAD's laws.
* `WireLaws`, `MessageLaws`: parsers read back what writers write. `RT w p x n` says the writer
  `w` writes at most `n` bytes from which `p` reads `x`; it composes like the do-blocks it
  describes, and holds for extensions, ClientHello, ServerHello, Certificate, CertificateVerify,
  key shares and ALPN lists. `splitMessages_frames` splits framed messages back apart.
* `Client.Established` is the client's evidence that the server is authenticated: its constructor
  is private to the client handshake, and it holds a proof that the server's SPKI hash is one of
  the pins and that the CertificateVerify signature verified. `Server.Established` likewise holds
  the check of the client's Finished.
* Handshake phases carry only what has been established so far, so a message out of order has no
  transition.

`make axioms` lists the axioms every theorem depends on. Beyond Lean's own, those built on X25519 use
Cryptlib's `p_prime` and `liftX_isSome_of_exists`.

## Tests

```bash
make test
```

* `LeanTLS.Tests.RFC8448`: the RFC 8448 §3 trace byte for byte: the X25519 exchange, every
  secret of the key schedule, both Finished messages, and a parse and re-encode of every message.
  `testdata/rfc8448_1rtt.json` is extracted from the RFC's text by `scripts/extract_rfc8448.py`.
* `LeanTLS.Tests.Handshake`: a client and a server run against each other over X25519MLKEM768,
  with whole flights and one byte at a time; refusals of a wrong pin, wrong ALPN, a tampered
  Finished and signature, truncated, malformed and oversized messages; and the certificate check
  against one produced by katzenpost's Go `epochCertificate`.

The handshake is exercised against Go's crypto/tls and quic-go by
[lean_quic](https://github.com/katzenpost/lean_quic)'s interop tests.
