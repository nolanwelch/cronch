#!/bin/sh
# From a clean clone, no arguments: build three artifacts, check them, replay
# them, revoke a host, and print the exact affected set.
#
# The point is the last step. Because every dependency is hash-pinned and
# recorded in a receipt, "this host turned out to be compromised" is a query
# with an exact answer -- not an advisory to go and check your dependencies.
set -eu

cd "$(dirname "$0")/.."
OUT="${TMPDIR:-/tmp}/cronch-demo-revocation.$$"
trap 'rm -rf "$OUT"' EXIT
mkdir -p "$OUT"

# The host that `effectful` holds a result on the authority of.
HOST=ed25519:a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1

RUN="gleam run --no-print-progress -m cronch/cli --"

echo "== 1. check =================================================="
echo "Three artifacts of three trust shapes, plus the host procedure's"
echo "declared signature. Each check emits a receipt."
echo
$RUN check demo/artifacts.cronch --emit-receipts "$OUT"

echo
echo "== 2. replay ================================================="
echo "Every receipt is re-derived from scratch and compared byte for byte."
echo "Nothing is trusted here -- verifying a receipt IS recomputing it."
echo
$RUN replay "$OUT"

echo
echo "== 3. audit =================================================="
$RUN audit --ledger "$OUT" || true

echo
echo "== 4. revoke ================================================="
echo "The host is compromised. Which artifacts lose their warrant?"
echo
echo "  KILLED    effectful  -- names the host directly"
echo "  KILLED    downstream -- reaches it transitively, names no host itself"
echo "  SURVIVES  purist     -- no host, no axiom, no rule set: nothing to revoke"
echo "  SURVIVES  fetch      -- an ordinary definition, not a host result"
echo
# revoke exits 1 when anything loses warrant, which is the whole point here.
$RUN revoke --ledger "$OUT" --host "$HOST" || true

echo
echo "The same command shape revokes a rule set (--rule-set author:hash), an"
echo "axiom (--axiom digest), a basis, or a whole kernel. The surface syntax"
echo "has no way to declare a rule set yet, so this demo revokes a host; the"
echo "rule-set path is exercised in test/ledger_test.gleam."
