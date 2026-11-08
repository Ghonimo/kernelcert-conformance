#!/bin/bash
# Exit codes of the kcheck executable on fixtures: 0 accept, 1 reject, 2 refused input.
cd "$(dirname "$0")/.." || exit 9
K=.lake/build/bin/kcheck
fail=0
expect() { "$K" "$1" > /dev/null 2>&1; rc=$?; if [ "$rc" -ne "$2" ]; then echo "FAIL $1: exit $rc, expected $2"; fail=1; else echo "ok   $1 -> $rc"; fi; }
expect tests/fixtures/toy5.json 0
expect tests/fixtures/unsafe.json 1
expect tests/fixtures/badmap.json 2
expect tests/fixtures/does_not_exist.json 2
exit $fail
