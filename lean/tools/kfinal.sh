#!/bin/bash
# Final step of the kernel build, after tools/kbuild.py (usage: bash tools/kfinal.sh; it works in the repository root,
# the parent of tools/). Checks every shard module of tools/kjobs.txt (olean present, rc 0 in logs/kbuild.tsv, no error
# message in its log), compiles the final modules SignUnc/{LowShardsK, UpperMainK, LowerMainK, MainK, ProbeK}.lean with
# the flags of tools/kbuild.py, and prints the statements and the axioms (Axioms.lean). Logs: logs/final_*.log.
# ProbeK also imports SignUnc.Lower.ExtremizerProbe, built by the first `lake build` command (see tools/kbuild.py).
set -u
cd "$(dirname "$0")/.." || exit 1
export TMPDIR=$PWD/tmp
mkdir -p logs tmp
ulimit -s unlimited
T=""
[ -x /usr/bin/time ] && T="/usr/bin/time -v"
bad=0
while read -r m est gb; do
  [ -n "$m" ] || continue
  f=logs/kb/${m//\//_}.log
  o=.lake/build/lib/lean/$m.olean
  if [ ! -s "$o" ]; then echo "MISSING $o"; bad=1; continue; fi
  rc=$(awk -v m="$m" '$1 == m { r = $2 } END { print r }' logs/kbuild.tsv)
  if [ "$rc" != 0 ]; then echo "BADEXIT $m rc=$rc"; bad=1; fi
  if sed '/Command being timed/,$d' "$f" | grep -qi "error"; then echo "ERRORTEXT $m"; bad=1; fi
done < tools/kjobs.txt
echo "shard verification bad=$bad ($(wc -l < tools/kjobs.txt) shards)"
[ $bad = 0 ] || exit 1
O=.lake/build/lib/lean/SignUnc
for m in LowShardsK UpperMainK LowerMainK MainK ProbeK; do
  $T lake env lean --tstack=1000000 -DElab.async=false -o $O/$m.olean -i $O/$m.ilean SignUnc/$m.lean > logs/final_$m.log 2>&1
  rc=$?
  echo "$m rc=$rc $(grep -E 'Elapsed' logs/final_$m.log | sed 's/.*: //') maxrss_kb=$(grep 'Maximum resident' logs/final_$m.log | awk '{print $NF}')"
  sed '/Command being timed/,$d' logs/final_$m.log | grep -i error | head -3
  [ $rc = 0 ] || bad=1
done
[ $bad = 0 ] || { echo "final modules: FAILED"; exit 1; }
lake env lean Axioms.lean 2>&1 | grep -v "repository has local"
awk '$2 == "0" { n++; s += $3; if ($4 > m) m = $4 } END { printf "shard records rc0=%d sum_wall_s=%.0f max_rss_kb=%d\n", n, s, m }' logs/kbuild.tsv
echo "ALL FINISHED $(date -u)"
