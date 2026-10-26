#!/usr/bin/env bash
# Print the axioms behind every theorem written in LeanTLS, and the definitions carrying laws,
# and fail on anything beyond Lean's own (propext, Classical.choice, Quot.sound) and, for those
# built on Cryptlib's X25519, that module's two axioms (p_prime, liftX_isSome_of_exists).
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -p "${TMPDIR:-.}" --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
cat >"$tmp" <<'LEAN'
import LeanTLS
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut names := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if let some m := env.getModuleIdxFor? n then
        if (env.header.moduleNames[m.toNat]!).getRoot == `LeanTLS && !n.isInternal then
          -- Only theorems written in the source, not generated equations and injectivity lemmas.
          if (← findDeclarationRanges? n).isSome then
            names := names.push n
  -- Definitions that carry laws as proof fields.
  names := names ++ #[`LeanTLS.KeyShare.concat, `LeanTLS.KeyShare.ofNIKE, `LeanTLS.KeyShare.ofKEM,
    `LeanTLS.mlkem768, `LeanTLS.x25519, `LeanTLS.x25519mlkem768, `LeanTLS.Handshake.Client.recv,
    `LeanTLS.Handshake.Server.recv]
  for n in names.qsort (·.toString < ·.toString) do
    let axs ← collectAxioms n
    IO.println s!"{n}: {axs.qsort (·.toString < ·.toString) |>.toList}"
LEAN
out=$(lake env lean "$tmp" 2>&1)
echo "$out"
allowed='propext\|Classical.choice\|Quot.sound\|Cryptlib.Primitives.NIKE.X25519.p_prime\|Cryptlib.Primitives.NIKE.X25519.liftX_isSome_of_exists'
if grep -v ": \[\(\($allowed\)\(, \($allowed\)\)*\)\?\]$" <<<"$out" | grep -q .; then
  echo "FAIL: a theorem depends on an unexpected axiom" >&2
  exit 1
fi
echo "$(wc -l <<<"$out") laws, no unexpected axioms"
