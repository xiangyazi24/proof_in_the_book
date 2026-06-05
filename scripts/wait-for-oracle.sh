#!/bin/bash
# wait-for-oracle.sh <question_filename>
# Blocks until the corresponding ANSWER_*.md appears.
set -e
q="$1"
[ -z "$q" ] && { echo "usage: wait-for-oracle.sh QUESTION_NNN.md" >&2; exit 1; }
dir="$HOME/repos/proof_in_the_book/HANDOFF/oracle"
ans="${q/QUESTION_/ANSWER_}"
echo "[oracle] question filed: $q"
echo "[oracle] waiting for $dir/$ans (poll 5s, max 30min)..."
n=0
while [ ! -f "$dir/$ans" ]; do
  sleep 5
  n=$((n+1))
  [ $n -gt 360 ] && { echo "[oracle] TIMEOUT after 30min" >&2; exit 2; }
done
echo "[oracle] ===== ANSWER ====="
cat "$dir/$ans"
echo
echo "[oracle] ================="
