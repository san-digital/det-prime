#!/usr/bin/env bash
set -euo pipefail

# Compiles all DetPrime Lean 4 modules against a Mathlib checkout and replays
# the resulting .olean environment through Lean's standalone kernel checker
# (`leanchecker`), followed by an explicit `#print axioms` audit.
#
# Environment variables:
#   MATHLIB_DIR          Path to a compiled Mathlib4 workspace (required if `lake`
#                        is not invoked inside an existing Mathlib workspace).
#   LEAN_BIN_DIR         Optional directory prepended to PATH for `lean`, `lake`,
#                        and `leanchecker`.
#   ALPOGE_STATEMENTS    Optional path to Alpoge's `Statements.lean`; when set,
#                        checks definitional equality (`rfl`) of
#                        `DirichletLNonvanishingRightOfHalf` and `RiemannZetaZerosOnLine`.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_SRC="$REPO_ROOT/lean"

if [[ -n "${LEAN_BIN_DIR:-}" ]]; then
  export PATH="$LEAN_BIN_DIR:$PATH"
fi

if [[ -z "${MATHLIB_DIR:-}" ]]; then
  echo "error: set MATHLIB_DIR to a compiled mathlib4 directory" >&2
  exit 1
fi

if [[ -n "${ALPOGE_STATEMENTS:-}" && ! -f "${ALPOGE_STATEMENTS}" ]]; then
  echo "error: ALPOGE_STATEMENTS=${ALPOGE_STATEMENTS} is not a file" >&2
  exit 1
fi

BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/det-prime-lean.XXXXXX")"
trap 'rm -rf "$BUILD_DIR"' EXIT
mkdir -p "$BUILD_DIR/DetPrime"

cd "$MATHLIB_DIR"

lake env bash -c '
  set -euo pipefail
  export LEAN_PATH="'"$BUILD_DIR"':${LEAN_PATH:-}"
  for mod in LogBounds PrimeWitness TonelliShanks BridgeAudit; do
    echo "[lean] compiling DetPrime.${mod}"
    lean -R "'"$LEAN_SRC"'" -o "'"$BUILD_DIR"'/DetPrime/${mod}.olean" "'"$LEAN_SRC"'/DetPrime/${mod}.lean"
  done

  echo "[leanchecker] replaying DetPrime modules"
  leanchecker -v DetPrime.LogBounds DetPrime.PrimeWitness DetPrime.TonelliShanks DetPrime.BridgeAudit

  echo "[axioms] checking foundational axiom footprint"
  AXIOM_OUT="$(lean --stdin <<'"'"'EOS'"'"'
import DetPrime.BridgeAudit
#print axioms DetPrime.lnUpperScaled_strict_bound
#print axioms DetPrime.bachBound_sound
#print axioms DetPrime.llsBound_sound
#print axioms DetPrime.bachBound_u256_max
#print axioms DetPrime.prime_witness_of_coprime_witness
#print axioms DetPrime.prime_is_strong_probable_prime
#print axioms DetPrime.odd_composite_exists_euler_jacobi_witness
#print axioms DetPrime.strong_liar_mem_euler_jacobi
#print axioms DetPrime.tonelli_shanks_init
#print axioms DetPrime.tonelli_shanks_step
#print axioms DetPrime.tonelli_shanks_done
#print axioms DetPrime.sqrt_three_mod_four
#print axioms DetPrime.prime_nonresidue_witness
#print axioms DetPrime.miller_bach_prime_iff_all_prime_bases
#print axioms DetPrime.least_nonresidue_has_prime_witness
EOS
)"
  echo "$AXIOM_OUT"
  # Long axiom lists wrap across lines, so join the output before extracting each list.
  # Anything outside the three standard axioms (sorryAx, Lean.ofReduceBool from
  # native_decide, or a custom axiom) fails the audit.
  NONSTANDARD="$(printf "%s\n" "$AXIOM_OUT" | tr "\n" " " | grep -o "\[[^]]*\]" | tr -d "[]" \
    | tr "," "\n" | sed "s/^ *//; s/ *$//" \
    | grep -v -x -e "" -e "propext" -e "Classical.choice" -e "Quot.sound" || true)"
  if [[ -n "$NONSTANDARD" ]]; then
    echo "error: non-standard axioms in footprint: $(echo $NONSTANDARD)" >&2
    exit 1
  fi
'

if [[ -n "${ALPOGE_STATEMENTS:-}" ]]; then
  echo "[statements] verifying definitional equality with ${ALPOGE_STATEMENTS}"
  cp "${ALPOGE_STATEMENTS}" "$BUILD_DIR/UpstreamStatements.lean"
  lake env bash -c '
    set -euo pipefail
    export LEAN_PATH="'"$BUILD_DIR"':${LEAN_PATH:-}"
    lean -R "'"$BUILD_DIR"'" -o "'"$BUILD_DIR"'/UpstreamStatements.olean" "'"$BUILD_DIR"'/UpstreamStatements.lean"
    lean --stdin <<'"'"'EOS'"'"'
import UpstreamStatements
import DetPrime.BridgeAudit

example : DetPrime.RiemannZetaZerosOnLine = _root_.RiemannZetaZerosOnLine := rfl
example : DetPrime.DirichletLNonvanishingRightOfHalf = _root_.DirichletLNonvanishingRightOfHalf := rfl
EOS
  '
  echo "[statements] rfl check passed"
fi

echo "[ok] all DetPrime Lean 4 modules compiled, kernel-replayed, and axiom-audited"
