#!/usr/bin/env bash
# Export each module in fixtures/Fixtures/ into javascript/test/fixtures/, gzipped. Needs Lean 4.35.0's `lake` and
# `leanexport` on PATH (the kernel's scripts/install-lean.sh installs them). The tests don't: they use what's
# committed.
set -euo pipefail
cd "$(dirname "$0")/../fixtures"
OUT=../javascript/test/fixtures
mkdir -p "$OUT"
names=$(node -e 'import("../javascript/index.js").then((m) => console.log(m.EXPORTED.join(" ")))')
lake build Fixtures
for file in Fixtures/*.lean; do
  module=$(basename "$file" .lean)
  # shellcheck disable=SC2086
  lake env leanexport "Fixtures.$module" -- $names | gzip -9n >"$OUT/$module.ndjson.gz"
done
ls -l "$OUT"
