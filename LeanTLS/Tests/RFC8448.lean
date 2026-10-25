import Lean.Data.Json
import LeanTLS
import Cryptlib.Util.HexBytes

open Lean
open LeanTLS
open LeanTLS.KeySchedule
open LeanTLS.Messages
open Cryptlib.Util.HexBytes (hexStringToByteArray byteArrayToHex)
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! The RFC 8448 §3 simple 1-RTT trace, byte for byte: the X25519 exchange through the
`KeyShare` interface, every secret of the key schedule, both Finished messages, and a parse and
re-encode of every handshake message. -/

def load (path : String) : IO (String → IO ByteArray) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let v ← IO.ofExcept (j.getObjVal? "vectors")
  pure fun k => do
    let s ← IO.ofExcept ((← IO.ofExcept (v.getObjVal? k)).getStr?)
    match hexStringToByteArray s with
    | some b => pure b
    | none => throw (IO.userError s!"{k}: bad hex")

def check (failures : IO.Ref Nat) (name : String) (got want : ByteArray) : IO Unit := do
  if got == want then IO.println s!"  ok    {name}"
  else
    failures.modify (· + 1)
    IO.println s!"  FAIL  {name}\n        got  {byteArrayToHex got}\n        want {byteArrayToHex want}"

def reencode {α : Type} (p : Wire.Parser α) (w : α → Wire.Writer Unit) (msg : ByteArray) :
    Except Alert ByteArray := do
  let body := msg.extract 4 msg.size
  frame (msg.get! 0) (w (← Wire.Parser.run p body))

def main : IO UInt32 := do
  let v ← load "testdata/rfc8448_1rtt.json"
  let failures ← IO.mkRef 0
  let ch ← v "client_hello"
  let sh ← v "server_hello"
  let ee ← v "encrypted_extensions"
  let cert ← v "certificate"
  let cv ← v "certificate_verify"
  let sfin ← v "server_finished"
  let cfin ← v "client_finished"

  IO.println "X25519 through KeyShare"
  let ec := toVecN 32 (← v "client_x25519_private")
  let es := toVecN 32 (← v "server_x25519_private")
  let (secret, share) := x25519.clientGen ec
  check failures "client share" (ofVector share) (← v "client_x25519_public")
  match x25519.serverRespond es share with
  | none => check failures "server accepts the client share" ByteArray.empty ⟨#[1]⟩
  | some (ss, k) =>
    check failures "server share" (ofVector ss) (← v "server_x25519_public")
    check failures "server secret" (ofVector k) (← v "ecdhe")
    check failures "client secret" ((x25519.clientFinish secret ss).map ofVector |>.getD ByteArray.empty)
      (← v "ecdhe")

  IO.println "key schedule"
  check failures "early secret" earlySecret (← v "early_secret")
  let hs := handshakeSecret (← v "ecdhe")
  check failures "handshake secret" hs (← v "handshake_secret")
  let hts := handshakeTraffic hs (ch ++ sh)
  check failures "client handshake traffic" hts.client (← v "client_handshake_traffic")
  check failures "server handshake traffic" hts.server (← v "server_handshake_traffic")
  check failures "server handshake key" (expandLabel hts.server "key" ByteArray.empty 16)
    (← v "server_handshake_key")
  check failures "server handshake iv" (expandLabel hts.server "iv" ByteArray.empty 12)
    (← v "server_handshake_iv")
  let ms := masterSecret hs
  check failures "master secret" ms (← v "master_secret")
  let throughCV := ch ++ sh ++ ee ++ cert ++ cv
  check failures "server Finished" (⟨#[20, 0, 0, 32]⟩ ++ finishedData hts.server throughCV) sfin
  let throughSFin := throughCV ++ sfin
  check failures "client Finished" (⟨#[20, 0, 0, 32]⟩ ++ finishedData hts.client throughSFin) cfin
  let ats := applicationTraffic ms throughSFin
  check failures "client application traffic" ats.client (← v "client_application_traffic")
  check failures "server application traffic" ats.server (← v "server_application_traffic")

  IO.println "parse and re-encode"
  let rt (name : String) (r : Except Alert ByteArray) (want : ByteArray) : IO Unit :=
    match r with
    | .ok b => check failures name b want
    | .error a => do failures.modify (· + 1); IO.println s!"  FAIL  {name}: {repr a}"
  rt "ClientHello" (reencode clientHello writeClientHello ch) ch
  rt "ServerHello" (reencode serverHello writeServerHello sh) sh
  rt "EncryptedExtensions" (reencode extensions writeExtensions ee) ee
  rt "Certificate" (reencode certificate writeCertificate cert) cert
  rt "CertificateVerify" (reencode certificateVerify writeCertificateVerify cv) cv
  let split := match splitMessages (ch ++ sh ++ ee.extract 0 10) with
    | .ok (msgs, rest) => msgs.size == 2 && rest.size == 10
    | .error _ => false
  check failures "split two messages and a partial one" ⟨#[if split then 1 else 0]⟩ ⟨#[1]⟩

  let n ← failures.get
  IO.println (if n == 0 then "all RFC 8448 checks passed" else s!"{n} RFC 8448 checks failed")
  pure (if n == 0 then 0 else 1)
