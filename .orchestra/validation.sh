#!/usr/bin/env bash
set -euo pipefail

# $HOME is read-only in this sandbox, so keep lake's cache dir inside the repo.
export XDG_CACHE_HOME="$PWD/.cache-home"

# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
# `TateCurvesTheta.lean` starts with a copyright header that mk_all does not write, so regenerate the
# root module with mk_all and compare it with the committed file minus its leading header.
root_saved="$(mktemp)"
cp TateCurvesTheta.lean "$root_saved"
# mk_all exits 1 when it rewrites the file (always, because of the header); a failed run leaves
# the file with its header, which the comparison below then rejects.
lake exe mk_all --lib TateCurvesTheta --git > /dev/null || true
if ! awk 'NR == 1 && $0 == "/-" { h = 1 } h { if ($0 == "-/") h = 0; next } { print }' "$root_saved" \
    | cmp -s - TateCurvesTheta.lean; then
  cp "$root_saved" TateCurvesTheta.lean
  echo "The file 'TateCurvesTheta.lean' is out of date: run \`lake exe mk_all --lib TateCurvesTheta --git\` and keep its header."
  exit 1
fi
cp "$root_saved" TateCurvesTheta.lean

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
