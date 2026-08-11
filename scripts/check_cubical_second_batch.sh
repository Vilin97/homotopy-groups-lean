#!/usr/bin/env bash
set -euo pipefail

AGDA_VERSION="2.8.0"
AGDA_SHA256="824081b8dcbe431289a50ac6bd83e451f390c51c3884ac7a8c4a5c0df2632faf"
AGDA_URL="https://github.com/agda/agda/releases/download/v2.8.0/Agda-v2.8.0-linux.tar.xz"
CUBICAL_COMMIT="92166033326aa59800a580b428125f3c654b5e45"
CUBICAL_URL="https://github.com/agda/cubical.git"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch_parent="${CODEX_SCRATCH_ROOT:-${RUNNER_TEMP:-/data/codex/scratch}}"
scratch_root="$scratch_parent/homotopy-groups-cubical"
agda_root="$scratch_root/agda-$AGDA_VERSION"
cubical_root="$scratch_root/cubical-$CUBICAL_COMMIT"
archive="$agda_root/Agda-v$AGDA_VERSION-linux.tar.xz"
checked_source="$scratch_root/SecondBatch.agda"

mkdir -p "$agda_root" "$scratch_root"

if [[ ! -x "$agda_root/agda" ]]; then
  curl --fail --location --silent --show-error "$AGDA_URL" -o "$archive.part"
  test "$(sha256sum "$archive.part" | cut -d' ' -f1)" = "$AGDA_SHA256"
  mv "$archive.part" "$archive"
  tar -xJf "$archive" -C "$agda_root"
fi

test "$($agda_root/agda --numeric-version)" = "$AGDA_VERSION"

if [[ ! -d "$cubical_root/.git" ]]; then
  git clone --filter=blob:none --no-checkout "$CUBICAL_URL" "$cubical_root"
  git -C "$cubical_root" checkout --detach "$CUBICAL_COMMIT"
fi

test "$(git -C "$cubical_root" rev-parse HEAD)" = "$CUBICAL_COMMIT"
test -z "$(git -C "$cubical_root" status --short)"

# Agda writes the top-level interface beside the checked source.  Keep that
# generated cache on the scratch disk rather than in the repository.
cp "$repo_root/formalizations/cubical/SecondBatch.agda" "$checked_source"

"$agda_root/agda" \
  --cubical \
  --guardedness \
  --safe \
  -WnoUnsupportedIndexedMatch \
  -i "$scratch_root" \
  -i "$cubical_root" \
  "$checked_source"
