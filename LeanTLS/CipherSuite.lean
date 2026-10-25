/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Primitives.Cipher.AEAD
import Cryptlib.Primitives.Cipher.AES
import Cryptlib.Primitives.Cipher.AESGCM
import Cryptlib.Primitives.Cipher.ChaChaPoly
import Cryptlib.Util.Bytes

namespace LeanTLS

open Cryptlib.Primitives.Cipher
open Cryptlib.Primitives.Cipher.AEAD (AEAD)
open Cryptlib.Util.Bytes (toVecN)

/-! # Cipher suites

A TLS 1.3 cipher suite is an AEAD and a hash; lean_tls's suites both use SHA-256. For QUIC each
also names a header protection function (RFC 9001 §5.4), which turns a key and a 16-byte sample of
ciphertext into a 5-byte mask. The AEAD's laws come with it. -/

structure CipherSuite where
  id   : Nat
  name : String
  aead : AEAD
  nonce_size : aead.nonceSize = 12
  hpMask : ByteArray → Vector UInt8 16 → Vector UInt8 5

namespace CipherSuite

def key (cs : CipherSuite) (b : ByteArray) : cs.aead.Key := cs.aead.keyFromBytes (toVecN _ b)

def nonce (cs : CipherSuite) (b : Vector UInt8 12) : Vector UInt8 cs.aead.nonceSize :=
  b.cast cs.nonce_size.symm

end CipherSuite

private def first5 (b : Vector UInt8 16) : Vector UInt8 5 := Vector.ofFn fun i => b[i.val]

/-- `TLS_AES_128_GCM_SHA256`; header protection is AES-128 on the sample (RFC 9001 §5.4.3). -/
def aes128gcm : CipherSuite where
  id := 0x1301
  name := "TLS_AES_128_GCM_SHA256"
  aead := AESGCM.Scheme128
  nonce_size := rfl
  hpMask hp sample := first5 (AES.encryptBlockWithKey128 (toVecN 16 hp) sample)

/-- `TLS_CHACHA20_POLY1305_SHA256`; header protection is one ChaCha20 block with the sample's
first four bytes as the little-endian counter and the rest as the nonce (RFC 9001 §5.4.4). -/
def chacha20poly1305 : CipherSuite where
  id := 0x1303
  name := "TLS_CHACHA20_POLY1305_SHA256"
  aead := ChaChaPoly.Scheme
  nonce_size := rfl
  hpMask hp sample :=
    let counter := sample[0].toUInt32 ||| (sample[1].toUInt32 <<< 8) |||
      (sample[2].toUInt32 <<< 16) ||| (sample[3].toUInt32 <<< 24)
    let nonce : Vector UInt8 12 := Vector.ofFn fun i => sample[i.val + 4]
    let block := ChaChaPoly.block (toVecN 32 hp) nonce counter
    Vector.ofFn fun i => block[i.val]!

/-- The suites by name, for handshake state that must stay in `Type`. -/
inductive Suite where
  | chacha20poly1305
  | aes128gcm
deriving DecidableEq, Repr, Inhabited

def Suite.cipherSuite : Suite → CipherSuite
  | .chacha20poly1305 => LeanTLS.chacha20poly1305
  | .aes128gcm => LeanTLS.aes128gcm

def Suite.id (s : Suite) : Nat := s.cipherSuite.id

/-- In preference order: ChaCha20-Poly1305 first, being much faster here than AES-GCM. -/
def cipherSuites : List Suite := [.chacha20poly1305, .aes128gcm]

end LeanTLS
