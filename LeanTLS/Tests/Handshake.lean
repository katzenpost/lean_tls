import LeanTLS
import Cryptlib.Util.HexBytes

open LeanTLS
open LeanTLS.Handshake
open Cryptlib.Util.HexBytes (hexStringToByteArray byteArrayToHex)
open Cryptlib.Util.Bytes (toVecN ofVector)

/-! A client and a server handshake run against each other in process, over X25519MLKEM768,
with each CRYPTO stream's bytes handed straight across. Then the ways the peers must refuse each
other: a wrong pin, wrong ALPN, a tampered flight, malformed and truncated messages. And the
certificate check against one katzenpost's Go `epochCertificate` produced. -/

def hex! (s : String) : ByteArray := (hexStringToByteArray s).getD ByteArray.empty

def seedA : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat i.val
def seedB : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat (100 + i.val)
def identity : Vector UInt8 32 := Vector.ofFn fun i => UInt8.ofNat i.val

def serverKey : ByteArray := ofVector (ed25519.pub identity)

def serverCert : ByteArray :=
  X509.selfSigned (fun m => ofVector (Cryptlib.Primitives.Sign.Ed25519Math.signNative identity m)) serverKey
    ⟨Array.replicate 16 7⟩ 1761433200 1761436800

def serverPin : ByteArray :=
  match X509.parseLeaf serverCert with
  | .ok leaf => KeySchedule.hash leaf.spki
  | .error _ => ByteArray.empty

def h3 : ByteArray := "h3".toUTF8

def serverCfg : Server.Config :=
  { alpn := h3, transportParams := ⟨#[1, 2, 3]⟩, signingKey := identity, certificate := serverCert }

def clientCfg : Client.Config := { alpn := h3, transportParams := ⟨#[4, 5]⟩, pins := [serverPin] }

/-- The Ed25519 key a certificate holds, if that is its kind. -/
def edKey : Option AuthKey → Option ByteArray
  | some (.ed25519 k) => some (ofVector k)
  | _ => none

def sends (out : Array Output) : Array (Level × ByteArray) :=
  out.filterMap fun | .send l d => some (l, d) | _ => none

def installs (out : Array Output) : Array (Level × Suite × Secrets) :=
  out.filterMap fun | .install l s k => some (l, s, k) | _ => none

/-- Deliver each send to the other side, in order. -/
def toServer (s : Server.State) (msgs : Array (Level × ByteArray)) (cfg : Server.Config := serverCfg) :
    Except Alert (Server.State × Array Output) := do
  let mut st := s
  let mut out := #[]
  for (l, d) in msgs do
    let (st', o) ← Server.recv cfg seedB st l d
    st := st'
    out := out ++ o
  pure (st, out)

def toClient {cfg : Client.Config} (s : Client.State cfg) (msgs : Array (Level × ByteArray)) :
    Except Alert (Client.State cfg × Array Output) := do
  let mut st := s
  let mut out := #[]
  for (l, d) in msgs do
    let (st', o) ← Client.recv st l d
    st := st'
    out := out ++ o
  pure (st, out)

/-- The same bytes, one at a time, as a QUIC stream could deliver them. -/
def bytewise (msgs : Array (Level × ByteArray)) : Array (Level × ByteArray) :=
  msgs.flatMap fun (l, d) => (Array.range d.size).map fun i => (l, d.extract i (i + 1))

def failures : IO (IO.Ref Nat) := IO.mkRef 0

def ok (r : IO.Ref Nat) (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  ok    {name}" else
    r.modify (· + 1)
    IO.println s!"  FAIL  {name}"

def alertOf {α : Type} : Except Alert α → Option Alert
  | .error a => some a
  | .ok _ => none

def main : IO UInt32 := do
  let r ← failures
  IO.println "certificate"
  let goCert := hex! "3081bb306fa003020102021100ed43f3d11ebc41c871560fca639f33ef300506032b65703000301e170d3236313032353232343030305a170d3236313032353233343030305a3000302a300506032b657003210003a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8300506032b65700341002ce2f8d5ca30ef133abbe64e0a352e6ddfd9df1f4fc7dc0e023ee8b1a9822779fbfe68ea6653bd7c31856a4842fb0c6c8618322c9e4aa4c647a7ff24b7732c02"
  let goPin := hex! "a050837d85070582ccf7394b0988847cc312cb88259b894899f6f239cf1791a5"
  let goKey := hex! "03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8"
  match X509.parseLeaf goCert with
  | .ok leaf =>
    ok r "Go epochCertificate: pin" (KeySchedule.hash leaf.spki == goPin)
    ok r "Go epochCertificate: Ed25519 key" (edKey leaf.key == some goKey)
  | .error _ => ok r "Go epochCertificate parses" false
  ok r "our key from the same seed is Go's" (serverKey == goKey)
  ok r "our certificate has Go's pin" (serverPin == goPin)
  ok r "our certificate's tbs is signed" (match X509.readTLV serverCert 0 with
    | .ok (outer, _) => match X509.children outer.content with
      | .ok parts => parts.size == 3 &&
          ed25519.verify (toVecN 32 serverKey) parts[0]!.raw (toVecN 64 (parts[2]!.content.extract 1 65))
      | .error _ => false
    | .error _ => false)

  IO.println "handshake"
  let run (deliver : Array (Level × ByteArray) → Array (Level × ByteArray)) :
      Except Alert (Client.State clientCfg × Server.State × Array Output × Array Output × Array Output) := do
    let (c0, o0) ← Client.start clientCfg seedA
    let (s1, o1) ← toServer Server.init (deliver (sends o0))
    let (c1, o2) ← toClient c0 (deliver (sends o1))
    let (s2, o3) ← toServer s1 (deliver (sends o2))
    pure (c1, s2, o1, o2, o3)
  for (name, deliver) in [("whole flights", id), ("one byte at a time", bytewise)] do
    match run deliver with
    | .error a => ok r s!"{name}: completes ({repr a})" false
    | .ok (c, s, o1, o2, o3) =>
      ok r s!"{name}: client connected" c.established?.isSome
      ok r s!"{name}: server connected" s.established?.isSome
      let srv := installs o1
      let cli := installs o2
      ok r s!"{name}: both install handshake and application keys" (srv.size == 2 && cli.size == 2)
      let agree (a b : Level × Suite × Secrets) :=
        a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.read == b.2.2.write && a.2.2.write == b.2.2.read
      ok r s!"{name}: keys agree" (srv.size == 2 && cli.size == 2 && agree srv[0]! cli[0]! && agree srv[1]! cli[1]!)
      ok r s!"{name}: ChaCha20-Poly1305 chosen" (cli.all (·.2.1 == .chacha20poly1305))
      ok r s!"{name}: server sends nothing after Finished" (o3.size == 0)
      match c.established? with
      | some e => do
        ok r s!"{name}: client has the server's transport parameters" (e.peerTransportParams == ⟨#[1, 2, 3]⟩)
        ok r s!"{name}: client pinned the server" (e.spki.size > 0)
      | none => pure ()
      match s.established? with
      | some e => ok r s!"{name}: server has the client's transport parameters" (e.peerTransportParams == ⟨#[4, 5]⟩)
      | none => pure ()

  IO.println "the correctness theorem's hypotheses, for this client and server"
  let share := clientCfg.share
  let ec := drawVec seedA "key share" share.entropySize
  let es := drawVec seedB "key share" share.entropySize
  ok r "same group and ALPN" (clientCfg.group == serverCfg.group && clientCfg.alpn == serverCfg.alpn)
  ok r "a common cipher suite" (serverCfg.suites.any (clientCfg.suites.contains ·))
  ok r "the client's sizes" (0 < clientCfg.alpn.size && clientCfg.alpn.size < 256 &&
    clientCfg.transportParams.size ≤ 16384 && clientCfg.serverName.isNone && clientCfg.suites.length ≤ 64)
  ok r "the server's sizes" (0 < serverCfg.alpn.size && serverCfg.alpn.size < 256 &&
    serverCfg.transportParams.size ≤ 16384 && serverCfg.certificate.size ≤ 30000)
  ok r "the server accepts the client's share" (share.serverRespond es (share.clientGen ec).2).isSome
  ok r "the server random is not a HelloRetryRequest's" (draw seedB "server random" 32 != Messages.helloRetryRandom)
  ok r "the certificate holds the signing key and is pinned" (match X509.parseLeaf serverCfg.certificate with
    | .ok leaf => edKey leaf.key == some (ofVector (ed25519.pub serverCfg.signingKey)) &&
        clientCfg.pins.contains (KeySchedule.hash leaf.spki)
    | .error _ => false)

  IO.println "ML-DSA-65 authentication"
  match X509.certificateFor .mldsa65 (ofVector identity) (ofVector seedB) ⟨Array.replicate 16 7⟩
      1761433200 1761436800 with
  | .error a => ok r s!"ML-DSA-65 certificate ({repr a})" false
  | .ok pqCert =>
    let pqPin := match X509.parseLeaf pqCert with
      | .ok leaf => KeySchedule.hash leaf.spki
      | .error _ => ByteArray.empty
    let pqServer : Server.Config := { serverCfg with scheme := .mldsa65, certificate := pqCert }
    let pqClient : Client.Config := { clientCfg with pins := [pqPin], schemes := [.mldsa65] }
    ok r s!"ML-DSA-65 certificate parses ({pqCert.size} bytes)" (pqPin.size == 32)
    let pq : Except Alert (Client.State pqClient × Server.State × Array Output × Array Output) := do
      let (c0, o0) ← Client.start pqClient seedA
      let (s1, o1) ← toServer Server.init (sends o0) pqServer
      let (c1, o2) ← toClient c0 (sends o1)
      let (s2, _) ← toServer s1 (sends o2) pqServer
      pure (c1, s2, o1, o2)
    match pq with
    | .error a => ok r s!"ML-DSA-65 handshake completes ({repr a})" false
    | .ok (c, s, o1, o2) =>
      let srv := installs o1
      let cli := installs o2
      let agree (a b : Level × Suite × Secrets) :=
        a.1 == b.1 && a.2.1 == b.2.1 && a.2.2.read == b.2.2.write && a.2.2.write == b.2.2.read
      ok r "ML-DSA-65: both connected" (c.established?.isSome && s.established?.isSome)
      ok r "ML-DSA-65: keys agree" (srv.size == 2 && cli.size == 2 && agree srv[0]! cli[0]! && agree srv[1]! cli[1]!)
      ok r "ML-DSA-65: the client verified an ML-DSA-65 signature"
        (c.established?.any (·.serverKey.scheme == .mldsa65))
      let flight := (sends o1).foldl (fun n (_, d) => n + d.size) 0
      ok r s!"ML-DSA-65: the server's flight is {flight} bytes" (flight > 8000)
    let tampered : Except Alert Unit := do
      let (c0, o0) ← Client.start pqClient seedA
      let (_, o1) ← toServer Server.init (sends o0) pqServer
      let flipped := (sends o1).map fun (l, d) =>
        if l == .handshake then (l, d.set! (d.size - 100) (d.get! (d.size - 100) ^^^ 1)) else (l, d)
      discard <| toClient c0 flipped
    ok r "ML-DSA-65: a tampered CertificateVerify signature: decrypt_error"
      (alertOf tampered == some .decryptError)
  let pqOnly : Client.Config := { clientCfg with schemes := [.mldsa65] }
  let r5 : Except Alert Unit := do
    let (_, o0) ← Client.start pqOnly seedA
    discard <| toServer Server.init (sends o0)
  ok r "a client accepting only ML-DSA-65 is refused by an Ed25519 server: handshake_failure"
    (alertOf r5 == some .handshakeFailure)

  IO.println "refusals"
  let flight1 : Except Alert (Client.State clientCfg × Array (Level × ByteArray)) := do
    let (c0, o0) ← Client.start clientCfg seedA
    let (_, o1) ← toServer Server.init (sends o0)
    pure (c0, sends o1)
  match flight1 with
  | .error a => ok r s!"first flight ({repr a})" false
  | .ok (c0, msgs) =>
    let wrongPin : Client.Config := { clientCfg with pins := [⟨Array.replicate 32 0⟩] }
    let r1 : Except Alert Unit := do
      let (c, _) ← Client.start wrongPin seedA
      discard <| toClient c msgs
    ok r "wrong pin: bad_certificate" (alertOf r1 == some .badCertificate)
    let flip (i : Nat) := msgs.map fun (l, d) =>
      if l == .handshake then (l, d.set! (d.size - i) (d.get! (d.size - i) ^^^ 1)) else (l, d)
    ok r "tampered server Finished: decrypt_error" (alertOf (toClient c0 (flip 1)) == some .decryptError)
    ok r "tampered CertificateVerify signature: decrypt_error" (alertOf (toClient c0 (flip 50)) == some .decryptError)
    let truncated := (msgs.filter (·.1 == .initial)).map fun (l, d) => (l, d.extract 0 (d.size - 1))
    ok r "truncated ServerHello: waits, does not fail" (match toClient c0 truncated with
      | .ok (c, _) => c.established?.isNone
      | .error _ => false)
    let junk := #[(Level.initial, (⟨#[2, 0, 0, 3, 3, 3, 1]⟩ : ByteArray))]
    ok r "truncated ServerHello body: decode_error" (alertOf (toClient c0 junk) == some .decodeError)
    let badVersion := #[(Level.initial, (⟨#[2, 0, 0, 3, 1, 2, 3]⟩ : ByteArray))]
    ok r "ServerHello with a bad legacy version: protocol_version"
      (alertOf (toClient c0 badVersion) == some .protocolVersion)
    let huge := #[(Level.initial, (⟨#[2, 0xff, 0xff, 0xff]⟩ : ByteArray))]
    ok r "oversized message: decode_error" (alertOf (toClient c0 huge) == some .decodeError)
    ok r "ServerHello at the handshake level: unexpected_message"
      (alertOf (toClient c0 (msgs.map fun (_, d) => (Level.handshake, d))) == some .unexpectedMessage)
  let wrongAlpn : Client.Config := { clientCfg with alpn := "h2".toUTF8 }
  let r2 : Except Alert Unit := do
    let (_, o0) ← Client.start wrongAlpn seedA
    discard <| toServer Server.init (sends o0)
  ok r "wrong ALPN: no_application_protocol" (alertOf r2 == some .noApplicationProtocol)
  let x25519Only : Client.Config := { clientCfg with group := .x25519 }
  let r3 : Except Alert Unit := do
    let (_, o0) ← Client.start x25519Only seedA
    discard <| toServer Server.init (sends o0)
  ok r "client without the server's group: handshake_failure" (alertOf r3 == some .handshakeFailure)
  let aesOnly : Client.Config := { clientCfg with suites := [.aes128gcm] }
  let r4 : Except Alert Bool := do
    let (c0, o0) ← Client.start aesOnly seedA
    let (_, o1) ← toServer Server.init (sends o0)
    let (_, o2) ← toClient c0 (sends o1)
    pure ((installs o2).all (·.2.1 == .aes128gcm))
  ok r "client offering only AES-128-GCM gets it" (r4 == .ok true)
  let exts (typs : List Nat) := Wire.Writer.run (Messages.writeExtensions
    (typs.map fun t => (⟨t, ⟨#[UInt8.ofNat t]⟩⟩ : Messages.Extension)).toArray)
  ok r "distinct extensions parse back" (match exts [1, 2, 3] with
    | .ok b => (Wire.Parser.run Messages.extensions b).toOption.map (·.map (·.typ)) == some #[1, 2, 3]
    | .error _ => false)
  ok r "duplicate extension: illegal_parameter" (match exts [1, 2, 1] with
    | .ok b => alertOf (Wire.Parser.run Messages.extensions b) == some .illegalParameter
    | .error _ => false)

  let n ← r.get
  IO.println (if n == 0 then "all handshake checks passed" else s!"{n} handshake checks failed")
  pure (if n == 0 then 0 else 1)
