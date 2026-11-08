#!/bin/bash
# rIC3 certificates for the std models of a corpus (run on the Linux host).
#   bash ric3_certificates.sh CORPUS_DIR TOOLS_DIR [JOBS]
# Writes CORPUS_DIR/ric3/<model>.cert.aag for every model rIC3 proves safe, and
# CORPUS_DIR/ric3/verdicts.csv (model, exit code, verdict) for every std model.
set -u
umask 077
C=$(cd "$1" && pwd); T=$(cd "$2" && pwd); J=${3:-8}
IMG=docker.io/gipsyh/ric3@sha256:60e8fcb333879ef5ac165f77e69948fc0e997376d24eaa959c22101de57dc292
mkdir -p -m 700 "$C/ric3"
one() {
  m=$1; C=$2; T=$3; IMG=$4
  w=$(mktemp -d "$C/ric3/work.XXXXXX")
  cp "$C/models/$m.aag" "$w/m.aag"
  timeout 120 podman run --rm --security-opt label=disable -v "$w:/w" "$IMG" -e ic3 /w/m.aag /w/m.cert.aig > "$w/out" 2>&1
  rc=$?
  case $rc in 20) v=safe;; 10) v=unsafe;; 124) v=timeout;; *) v=other;; esac
  if [ $rc -eq 20 ] && [ -s "$w/m.cert.aig" ]; then
    "$T/certifaiger-current/bin/aigtoaig" "$w/m.cert.aig" "$C/ric3/$m.cert.aag"
  fi
  echo "$m,$rc,$v"
  rm -rf "$w"
}
export -f one
grep -l "^c$" "$C"/models/m[0-9][0-9][0-9][0-9].aag | while read -r f; do
  n=$(basename "$f" .aag); grep -q "^std model" "$f" && echo "$n"
done | xargs -P "$J" -I{} bash -c 'one {} "$0" "$1" "$2"' "$C" "$T" "$IMG" | sort > "$C/ric3/verdicts.csv"
chmod -R go-rwx "$C"
echo "rIC3: $(wc -l < "$C/ric3/verdicts.csv") models, $(ls "$C/ric3"/*.cert.aag 2>/dev/null | wc -l) certificates"
