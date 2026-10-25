/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace LeanTLS

/-! # Alerts

The RFC 8446 §6.2 alerts a handshake can end with. Over QUIC an alert is not sent as a record:
it becomes the connection error `0x0100 + code` (RFC 9001 §4.8). -/

inductive Alert where
  | unexpectedMessage
  | handshakeFailure
  | badCertificate
  | illegalParameter
  | decodeError
  | decryptError
  | protocolVersion
  | internalError
  | missingExtension
  | unsupportedExtension
  | noApplicationProtocol
deriving DecidableEq, Repr, Inhabited

namespace Alert

def code : Alert → UInt8
  | unexpectedMessage     => 10
  | handshakeFailure      => 40
  | badCertificate        => 42
  | illegalParameter      => 47
  | decodeError           => 50
  | decryptError          => 51
  | protocolVersion       => 70
  | internalError         => 80
  | missingExtension      => 109
  | unsupportedExtension  => 110
  | noApplicationProtocol => 120

end Alert

end LeanTLS
