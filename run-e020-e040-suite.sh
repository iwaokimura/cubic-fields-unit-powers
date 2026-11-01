#!/bin/sh
# run-e020-e040-suite.sh --- E119 Phase 3: the regression suite for E020-E040.
#
# Runs all 30 scripts named by E020 ... E040 and
# collects their gate lines.  Every script prints exactly one line
#     EXXX GATE: GREEN            (0 failures)
#     EXXX GATE: *** RED ***      (n failures)
# Before E119 (2026-08-19) none of them printed a verdict at all, so
# "the script still runs" was the only thing a re-run could establish.
#
# Usage:  sh run-e020-e040-suite.sh [outdir] [jobs]
#
# PARALLEL since 2026-08-20 (user request).  The scripts are run JOBS at a
# time, default 8.  This is safe because no script in the suite writes a file:
# each one's entire output is stdout, redirected here to its own "$OUT/$f.log",
# so two concurrent scripts share nothing.  Checked before parallelising --
# a grep over all 30 for write/system/extern/open/save/.sobj//tmp found
# nothing.  If a future script writes ANY file, give it a per-run path or the
# suite stops being parallel-safe.  (Sage does write "$f.py" next to each
# .sage file when it preparses; those names are distinct per script, so they
# do not collide.  Do not run two copies of the SUITE at once, though -- that
# would collide on both the .py files and the log.)
#
# Sequential total was about 25 minutes, dominated by check-e028-sweep.gp,
# check-qpow.gp, check-c4-modp.sage, check-c4-autgroup.sage and
# check-e029-kummer.sage.  In parallel the wall time is roughly the longest
# single script, since those five run side by side.
#
# The table at the end is printed in a FIXED order -- the order of the lists
# below, not the order of completion -- so that two runs are diffable.

# --- internal: run one script and record its wall time.  Invoked by xargs. ---
if [ "$1" = "--one" ]; then
    f=$2
    OUT=$3
    t0=$(date +%s)
    case "$f" in
        *.gp)   gp -q "$f" > "$OUT/$f.log" 2>&1 < /dev/null ;;
        *.sage) PYTHONUNBUFFERED=1 sage "$f" > "$OUT/$f.log" 2>&1 < /dev/null ;;
        *)      echo "unknown script kind: $f" > "$OUT/$f.log" ;;
    esac
    t1=$(date +%s)
    echo $((t1 - t0)) > "$OUT/$f.time"
    exit 0
fi

OUT=${1:-e020-e040-runs}
JOBS=${2:-8}
mkdir -p "$OUT"

# --- provenance ------------------------------------------------------------
# The two halves of the suite do NOT run the same PARI.  The .gp scripts use
# the gp binary on PATH; the .sage scripts use the libpari that Sage links,
# which is a separate build and is NOT changed by upgrading gp.  On 2026-08-20
# that was gp 2.17.4 against Sage's PARI 2.17.1.  Recorded here so that a run
# log says for itself what produced it -- the scripts' own output does not.
{
  echo "# gp    : $(command -v gp)"
  echo "# gp    : $(gp --version 2>&1 | sed -n 's/.*Version \([0-9][0-9.]*\).*/\1/p' | head -1)"
  echo "# sage  : $(command -v sage)"
  echo "# sage  : PARI $(timeout 300 sage -c 'from sage.libs.pari import pari; print(pari.pari_version())' 2>/dev/null | sed -n 's/.*Version \([0-9][0-9.]*\).*/\1/p' | head -1)"
} | tee "$OUT/versions.txt"
echo

GP="check-star.gp check-q5.gp check-qpow.gp check-qpow-sieve.gp \
check-audit-post-trim.gp check-expo.gp check-composite-q.gp \
check-umemoto-cubic.gp check-index-closedform.gp \
check-bsquare.gp check-c4-points.gp check-c4-goodred.gp check-c4-aut.gp \
check-c4-prym.gp check-c4-prym-rr.gp check-c4-rational.gp \
check-c4-badprimes.gp \
check-e028-sweep.gp check-e029-lattice.gp"

SAGE="check-q5-genus.sage check-qpow-genus.sage check-composite-genus.sage \
check-c4-modp.sage check-c4-quartic.sage check-c4-autgroup.sage \
check-e029-dtilde.sage check-e029-kummer.sage check-e029-descent.sage \
check-e029-cube.sage"

ALL="$GP $SAGE"

# The long ones first: with a fixed pool, starting the stragglers last is what
# makes the tail of the run serial.  This list is a scheduling hint only -- the
# report below is printed in the ALL order regardless.
SLOW="check-e028-sweep.gp check-qpow.gp check-c4-modp.sage \
check-c4-autgroup.sage check-e029-kummer.sage"
REST=$(printf '%s\n' $ALL | grep -v -x -F "$(printf '%s\n' $SLOW)")
ORDER="$SLOW $REST"

wall0=$(date +%s)
printf '%s\n' $ORDER | xargs -P "$JOBS" -n 1 -I@ sh "$0" --one @ "$OUT"
wall1=$(date +%s)

n=0
red=0
for f in $ALL; do
    n=$((n + 1))
    line=$(awk '/ GATE: /' "$OUT/$f.log" 2>/dev/null)
    secs=$(cat "$OUT/$f.time" 2>/dev/null)
    printf "%-28s %5ss  %s\n" "$f" "${secs:-?}" "${line:-*** NO GATE LINE ***}"
    case "$line" in *RED*) red=$((red + 1)) ;; esac
    test -n "$line" || red=$((red + 1))
done

echo
echo "E020-E040 SUITE: $((n - red))/$n GREEN   ($((wall1 - wall0))s wall, $JOBS jobs)"
test "$red" -eq 0
