#!/bin/sh
# From a clean clone, no arguments: check one term against a declared effect
# set that covers it, and one against a declaration that does not -- naming the
# excess capability.
#
# What this proves: the artifact cannot reach a host procedure it did not
# declare. What it does NOT prove: anything about what the artifact computes.
# It is a reachability bound, and it is only as strong as the runtime's
# guarantee that `trusted` is the sole effect channel -- a guarantee nothing in
# this repository currently enforces. See the open risks in docs/TCB.md.
set -eu

cd "$(dirname "$0")/.."

HOST=a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1a1
RUN="gleam run --no-print-progress -m cronch/cli --"

# The procedure's content address is the hash of its declared signature, which
# `check` prints. Recover it rather than hard-coding it, so this demo cannot
# drift out of agreement with the artifacts it is describing.
OUT="${TMPDIR:-/tmp}/cronch-demo-admission.$$"
trap 'rm -rf "$OUT"' EXIT
mkdir -p "$OUT"
PROC=$($RUN check demo/artifacts.cronch --emit-receipts "$OUT" 2>/dev/null \
       | sed -n 's/^CHECK fetch .* artifact=blake3:\([0-9a-f]*\) .*/\1/p')

echo "== 1. declaring what it actually reaches ====================="
echo "The declaration covers (host, fetch), which is exactly what the"
echo "effectful artifact reaches. Everything is admitted."
echo
$RUN admit demo/artifacts.cronch --declare "$HOST:$PROC"

echo
echo "== 2. declaring nothing ====================================="
echo "An empty declaration is the strongest claim there is: this artifact"
echo "reaches no host procedure at all. The purist artifact and the plain"
echo "definition satisfy it; the two that touch the host do not, and the"
echo "excess capability is named."
echo
$RUN admit demo/artifacts.cronch --declare "" || true

echo
echo "Note that 'downstream' is refused too. It names no host of its own --"
echo "it reaches one through a content-addressed reference, and of_term is"
echo "transitive precisely so that moving a trusted node into a definition"
echo "does not launder it out of the declaration."
