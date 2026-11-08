#!/bin/bash
# Builds, at pinned versions, the tools the conformance study compares.
# Linux (tested on Rocky 9: gcc 11.5, cmake 3.31). Everything goes under $ROOT/tools;
# Rust and Lean are installed per user (rustup, elan) if missing.
#   ROOT=$HOME/research/certcheck bash setup_linux.sh
set -u
umask 077
ROOT=${ROOT:-$HOME/research/certcheck}
T=$ROOT/tools
L=$T/logs
mkdir -p -m 700 "$T" "$L"
cd "$T" || exit 1
log() { echo "[$(date '+%F %T')] $*"; }

AIGER_SHA=039ec1a2cc
CERT_CURRENT=ba86b456c32464929c9457450922cd88b4216afc   # checker source as of 10.3.0 (2026-09-22)
CERT_OLD=35a0c7f924                                      # 10.2.1, before both 2026-09-22 changes
CERT_NEW=b540f0c595f07fc4e66c2f7e12de9ad97ce56888        # 10.4.1 (2026-11-05), released after the counted run; post hoc only
RIC3_VERSION=1.5.2
VALAIG_SHA=6217ed0aa33dd2f657dd5c639847f276f02724b8

# 1. AIGER tools (aigfuzz, aigsim, aigtoaig, aigtocnf)
if [ ! -x aiger/aigsim ]; then
  log "aiger $AIGER_SHA"
  rm -rf aiger
  { git clone -q https://github.com/arminbiere/aiger aiger && cd aiger && git checkout -q $AIGER_SHA \
      && ./configure.sh && make -j8; } > "$L/aiger.log" 2>&1
  cd "$T"
fi

# 2. Certifaiger: current and 10.2.1, release builds; plus current with assertions on
build_cert() { # name sha extra-cmake-args
  local name=$1 sha=$2; shift 2
  if [ ! -x "$name/bin/check" ]; then
    log "certifaiger $name $sha"
    rm -rf "$name"
    { git clone -q https://github.com/Froleyks/certifaiger "$name" && cd "$name" && git checkout -q "$sha" \
        && cmake -DCMAKE_BUILD_TYPE=Release -B build -DSTATIC=OFF -DCHECK=ON "$@" \
        && cmake --build build --parallel 8 && cmake --install build --prefix . ; } > "$L/$name.log" 2>&1
    cd "$T"
  fi
}
build_cert certifaiger-current "$CERT_CURRENT"
build_cert certifaiger-10.2.1 "$CERT_OLD"
build_cert certifaiger-current-assert "$CERT_CURRENT" -DASSERT=ON
build_cert certifaiger-10.4.1 "$CERT_NEW"   # post hoc only: study/posthoc_cf1041.py
# 10.2.1 links its bundled AIGER tools statically even with STATIC=OFF, which fails on
# systems without a static C library. Its checker binary and scripts still build; give
# it the current build's AIGER tools and SAT solver (same vendored sources).
if [ ! -x certifaiger-10.2.1/bin/check ] && [ -x certifaiger-10.2.1/build/certifaiger ]; then
  log "certifaiger-10.2.1: assembling bin/ from its own checker and scripts plus current tools"
  mkdir -p certifaiger-10.2.1/bin
  for f in certifaiger check check_sat check_unsat certified; do
    cp certifaiger-10.2.1/build/$f certifaiger-10.2.1/bin/ 2>/dev/null
  done
  for f in aigtocnf aigsplit aigsim aigtoaig kissat limit runlim; do
    [ -e certifaiger-10.2.1/bin/$f ] || cp certifaiger-current/bin/$f certifaiger-10.2.1/bin/
  done
fi

# 3. rIC3, as its published container image pinned by digest. (Building the crate needs
#    clang, meson and a nightly Rust for its solver bindings.)
RIC3_IMAGE=docker.io/gipsyh/ric3@sha256:60e8fcb333879ef5ac165f77e69948fc0e997376d24eaa959c22101de57dc292  # tag v1.5.2
if ! podman image exists "$RIC3_IMAGE" 2>/dev/null; then
  log "rIC3 image $RIC3_IMAGE"
  podman pull "$RIC3_IMAGE" > "$L/ric3-image.log" 2>&1
fi

# 3b. CaDiCaL, which Valaig calls as an external `cadical` (Certifaiger's own tree only
#     fetches it at build time when configured for it).
CADICAL_TAG=rel-3.0.1
if [ ! -x bin/cadical ]; then
  log "cadical $CADICAL_TAG"
  rm -rf cadical-src
  { git clone -q https://github.com/arminbiere/cadical cadical-src && cd cadical-src && git checkout -q $CADICAL_TAG \
      && ./configure && make -j8 && mkdir -p ../bin && cp build/cadical ../bin/cadical; } > "$L/cadical.log" 2>&1
  cd "$T"; rm -rf cadical-src
fi

# 4. elan (Lean toolchains are fetched per project from lean-toolchain)
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  log "elan (user install, no default toolchain)"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none --no-modify-path > "$L/elan.log" 2>&1
fi

# 5. Valaig
if [ ! -x valaig/.lake/build/bin/valaigcert ]; then
  log "valaig $VALAIG_SHA"
  rm -rf valaig
  { git clone -q https://github.com/opencompl/valaig valaig && cd valaig && git checkout -q $VALAIG_SHA \
      && "$HOME/.elan/bin/lake" build valaigcert; } > "$L/valaig.log" 2>&1
  cd "$T"
fi

chmod -R go-rwx "$T"
log "done"
for x in aiger/aigsim aiger/aigfuzz certifaiger-current/bin/check certifaiger-10.2.1/bin/check \
         certifaiger-current-assert/bin/check certifaiger-10.4.1/bin/check valaig/.lake/build/bin/valaigcert; do
  if [ -x "$x" ]; then echo "ok      $x"; else echo "MISSING $x"; fi
done
