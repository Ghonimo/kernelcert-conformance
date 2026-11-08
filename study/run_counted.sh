#!/bin/bash
# The counted run of PREREGISTRATION.md, on the Linux host.
#   bash run_counted.sh ROOT     (ROOT holds repo/ and tools/; results go to ROOT/counted/)
set -u
umask 077
ROOT=$(cd "$1" && pwd)
R=$ROOT/counted
mkdir -p -m 700 "$R"
cd "$R" || exit 1
log() { echo "[$(date '+%F %T')] $*" | tee -a "$R/run.log"; }
log "repo commit $(cat "$ROOT/repo/COMMIT" 2>/dev/null)"
sha256sum "$ROOT/tools/bin/kcheck" "$ROOT/tools/bin/valaigcert" "$ROOT/tools/bin/cadical" \
  "$ROOT"/tools/certifaiger-*/bin/certifaiger >> "$R/run.log"
log "stage1"
python3 -I "$ROOT/repo/study/gen/make_corpus.py" stage1 corpus --seed 20261104 --models 600
log "rIC3"
bash "$ROOT/repo/study/gen/ric3_certificates.sh" corpus "$ROOT/tools" 16 | tee -a "$R/run.log"
log "stage3"
python3 -I "$ROOT/repo/study/gen/make_corpus.py" stage3 corpus --seed 20261104
log "pairs: $(($(wc -l < corpus/manifest.csv) - 1)) generated + fixed"
python3 -I "$ROOT/repo/study/run_pairs.py" corpus "$ROOT/tools" "$ROOT/repo" results.csv --jobs 12 | tee -a "$R/run.log"
python3 -I "$ROOT/repo/study/run_pairs.py" "$ROOT/repo/study/corpus/fixed" "$ROOT/tools" "$ROOT/repo" results_fixed.csv --jobs 8 | tee -a "$R/run.log"
chmod -R go-rwx "$R"
log "done"
