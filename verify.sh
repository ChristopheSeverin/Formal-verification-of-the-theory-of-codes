#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
shopt -s nullglob globstar

sources=(proofs/*/lean/**/*.lean)
audits=(proofs/*/checks/Check.lean)
if (( ! ${#sources[@]} || ! ${#audits[@]} )); then
  echo "No proof sources or audits found." >&2
  exit 1
fi

# Fetch the cache for the Mathlib modules the collection actually imports.
mapfile -t upstream < <(
  awk '{for (i = 1; i < NF; i++) if ($i == "import" && $(i+1) ~ /^Mathlib\./) print $(i+1)}' \
    "${sources[@]}" "${audits[@]}" | sort -u
)
if (( ${#upstream[@]} )); then
  lake exe cache get "${upstream[@]}" ||
    echo "The binary cache is unavailable. Lake will build dependencies from source." >&2
fi

lake build
for audit in "${audits[@]}"; do
  lake lean "$audit"
done

# An import-only file introduces no proof terms. Check any file with more content.
for source in "${sources[@]}"; do
  if ! grep -qEv '^[[:space:]]*$|^[[:space:]]*module[[:space:]]*$|^[[:space:]]*((public|meta) +)*import [[:alnum:]_.]+[[:space:]]*$' "$source"; then
    continue
  fi
  module=${source#proofs/*/lean/}
  module=${module%.lean}
  lake env leanchecker --verbose "${module//\//.}"
done
