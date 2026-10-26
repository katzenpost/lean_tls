#!/usr/bin/env bash
# Print the axioms behind lean_tls's laws and fail on anything beyond Lean's own
# (propext, Classical.choice, Quot.sound) and, for definitions built on Cryptlib's X25519,
# that module's two axioms (p_prime, liftX_isSome_of_exists).
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -p "${TMPDIR:-.}" --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
{
  echo "import LeanTLS"
  for n in KeySchedule.expandLabel_size KeyShare.nikeFinish_derived KeyShare.nikeAgree \
           KeyShare.kemAgree KeyShare.left_append KeyShare.right_append KeyShare.concat \
           KeyShare.ofNIKE KeyShare.ofKEM mlkem768 x25519 x25519mlkem768 \
           Agreement.keys_agree Handshake.Client.recv Handshake.Server.recv; do
    echo "#print axioms LeanTLS.$n"
  done
} >"$tmp"
out=$(lake env lean "$tmp" 2>&1 | sed -e ':a' -e 'N' -e '$!ba' -e 's/,\n */, /g')
echo "$out"
allowed='propext\|Classical.choice\|Quot.sound\|Cryptlib.Primitives.NIKE.X25519.p_prime\|Cryptlib.Primitives.NIKE.X25519.liftX_isSome_of_exists'
if grep -v "depends on axioms: \[\($allowed\)\(, \($allowed\)\)*\]$\|does not depend on any axioms" <<<"$out" | grep -q .; then
  echo "FAIL: a law depends on an unexpected axiom" >&2
  exit 1
fi
echo "no unexpected axioms"
