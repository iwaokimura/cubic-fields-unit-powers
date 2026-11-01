#!/usr/bin/env bash
# Run every verification script in this repository, in parallel, with one log
# per script, then print a summary.  Usage:
#
#     J=12 ./run-all.sh
#
# J is the number of parallel jobs (default 12).  Logs and per-script exit
# codes go to verify-logs/ (override with OUT=...).  check-c4-sieve.gp is run
# after everything else: it reads c4-qc-leftovers.txt, which
# check-c4-endgame.sage rewrites.
#
# check-mwsieve.gp is excluded: it is the superseded, diverging sieve
# schedule kept only as the record of E054(c); it does not terminate.
#
# check-c4-2desc.gp needs Denis Simon's ell.gp as shipped with SageMath; the
# script below locates it via sage unless SIMON_ELL is already set.
set -u
cd "$(dirname "$0")"
J="${J:-12}"
OUT="${OUT:-verify-logs}"
mkdir -p "$OUT"
export OUT
export PYTHONUNBUFFERED=1 PYTHONDONTWRITEBYTECODE=1
if [ -z "${SIMON_ELL:-}" ]; then
  SIMON_ELL="$(sage -c "from sage.env import SAGE_EXTCODE; print(SAGE_EXTCODE)" 2>/dev/null)/pari/simon/ell.gp"
fi
export SIMON_ELL
{ gp --version 2>&1 | head -2; sage --version; echo "SIMON_ELL=$SIMON_ELL"; date; } \
  > "$OUT/versions.txt" 2>&1

run_one() {
  local s="$1" rc start
  start=$(date +%s)
  case "$s" in
    *.gp)   gp -q --default parisize=2G "$s" < /dev/null > "$OUT/$s.log" 2>&1 ;;
    *.sage) sage "$s"                        < /dev/null > "$OUT/$s.log" 2>&1 ;;
  esac
  rc=$?
  echo "$rc $(( $(date +%s) - start ))" > "$OUT/$s.exit"
}
export -f run_one

# Longest jobs first, so the parallel pool drains evenly; then the rest.
SLOW="check-c4-qc.sage check-rho-tailbound.sage check-c4-endgame.sage \
check-e028-sweep.gp check-qpow.gp check-c4-modp.sage check-c4-autgroup.sage \
check-e029-kummer.sage check-c4-iterated.sage check-c4-heightsys.sage \
check-c4-globalheight.sage check-c4-phase5.sage check-two-logs.gp \
check-xs13-frob.sage check-xs13-table.sage check-c4-baddisk.sage \
check-xs13-classes.sage check-c4-b11.sage check-c4-h2.sage"

{ for s in $SLOW; do echo "$s"; done;
  ls check-*.gp check-*.sage | grep -v -F -x -e check-c4-sieve.gp -e check-mwsieve.gp \
    $(for s in $SLOW; do echo "-e $s"; done); } \
  | xargs -P "$J" -n 1 -I{} bash -c 'run_one "$@"' _ {}

run_one check-c4-sieve.gp

# ---- summary --------------------------------------------------------------
fails=0
for f in "$OUT"/*.exit; do
  s=$(basename "$f" .exit)
  read -r rc secs < "$f"
  if [ "$rc" != 0 ]; then
    echo "NONZERO-EXIT $s (rc=$rc, ${secs}s)"; fails=$((fails+1))
  fi
done
bad=$(grep -l -a -E "\bRED\b|\bFAIL\b|Traceback|at top-level: |syntax error|skipping file" "$OUT"/*.log \
      2>/dev/null || true)
echo "----------------------------------------------------------------------"
echo "scripts run: $(ls "$OUT"/*.exit | wc -l), nonzero exits: $fails"
# gp reports a syntax error, skips that statement ("... skipping file") and
# goes on, so the gate line can still say GREEN: these must be caught here.
echo "logs mentioning RED/FAIL/Traceback/gp errors (inspect by hand):"
for f in $bad; do echo "  $f"; done
