#!/bin/bash
# Builds the two Lean executables of the study, one toolchain at a time, under a local
# scratch directory (home quotas are small; Lean toolchains are about 1.5 GB each), and
# copies only the executables to $ROOT/tools/bin.
#   ROOT=$HOME/research/certcheck V=/var/tmp/ghonim_cc bash build_lean_tools.sh
set -u
umask 077
ROOT=${ROOT:-$HOME/research/certcheck}
V=${V:-/var/tmp/ghonim_cc}
export ELAN_HOME=$V/elan
LAKE=$ELAN_HOME/bin/lake
VALAIG_SHA=6217ed0aa33dd2f657dd5c639847f276f02724b8
mkdir -p -m 700 "$V" "$ROOT/tools/bin"
# Lean reserves much address space per thread; a host cap on virtual memory (64 GiB soft
# on Rocky 9 here) makes thread creation fail. Raise the soft cap to the hard one.
ulimit -v "$(ulimit -H -v)" 2>/dev/null
log() { echo "[$(date '+%F %T')] $*"; }

log "kcheck: copy the formalization and build"
rm -rf "$V/kcheck-src" && mkdir -p "$V/kcheck-src"
cp -r "$ROOT/repo/formalization/." "$V/kcheck-src/"
rm -rf "$V/kcheck-src/.lake"
( cd "$V/kcheck-src" && "$LAKE" build kcheck ) > "$V/kcheck-build.log" 2>&1
echo "kcheck build exit $?"
cp "$V/kcheck-src/.lake/build/bin/kcheck" "$ROOT/tools/bin/kcheck" && log "kcheck installed"

log "valaig $VALAIG_SHA"
if [ ! -d "$V/valaig" ]; then git clone -q https://github.com/opencompl/valaig "$V/valaig"; fi
( cd "$V/valaig" && git checkout -q $VALAIG_SHA && "$LAKE" build valaigcert ) > "$V/valaig-build.log" 2>&1
echo "valaig build exit $?"
cp "$V/valaig/.lake/build/bin/valaigcert" "$ROOT/tools/bin/valaigcert" && log "valaigcert installed"
chmod -R go-rwx "$V" "$ROOT/tools"
df -h "$V" | tail -1
log "done"
