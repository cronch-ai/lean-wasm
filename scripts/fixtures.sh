#!/usr/bin/env bash
# Export each module in fixtures/Fixtures/ into javascript/test/fixtures/, and fixtures/Reasoning/ into its reasoning/,
# gzipped. Needs Lean 4.35.0's `lake` and `leanexport` on PATH (the kernel's scripts/install-lean.sh installs them).
# The tests don't: they use what's committed.
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

# Constrained reasoning: the theory is exported with `Gamma` and `True` in place of `obligation`, as a platform pins
# it, and each solution as any solution is.
OUT_R="$OUT/reasoning"
mkdir -p "$OUT_R"
lake build Reasoning
# shellcheck disable=SC2086
lake env leanexport Reasoning.Theory -- Gamma True ${names#obligation } | gzip -9n >"$OUT_R/Theory.ndjson.gz"
for file in Reasoning/*.lean; do
  module=$(basename "$file" .lean)
  [ "$module" = Theory ] && continue
  # shellcheck disable=SC2086
  lake env leanexport "Reasoning.$module" -- $names | gzip -9n >"$OUT_R/$module.ndjson.gz"
done
ls -l "$OUT_R"
