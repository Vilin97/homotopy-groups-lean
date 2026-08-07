#!/usr/bin/env bash
set -euo pipefail

readonly LEAN_TOOLCHAIN='leanprover/lean4:v4.32.2'
readonly LEAN_ARCHIVE_URL='https://github.com/leanprover/lean4/releases/download/v4.32.2/lean-4.32.2-linux.tar.zst'
readonly LEAN_ARCHIVE_SHA256='5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa'

: "${RUNNER_TEMP:?RUNNER_TEMP must be set by the GitHub Actions runner}"
: "${GITHUB_PATH:?GITHUB_PATH must be set by the GitHub Actions runner}"

if [[ "$(/usr/bin/uname -m)" != 'x86_64' ]]; then
  echo 'the pinned Lean archive requires an x86_64 runner' >&2
  exit 1
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"

if ! cmp -s <(printf '%s\n' "$LEAN_TOOLCHAIN") "$repo_root/lean-toolchain"; then
  echo "lean-toolchain does not exactly match $LEAN_TOOLCHAIN" >&2
  exit 1
fi

archive="$(/usr/bin/mktemp "$RUNNER_TEMP/lean-4.32.2.XXXXXX.tar.zst")"
install_root="$(/usr/bin/mktemp -d "$RUNNER_TEMP/lean-4.32.2.XXXXXX")"

/usr/bin/curl --fail --location --silent --show-error --retry 5 \
  --proto '=https' --proto-redir '=https' --tlsv1.2 \
  --output "$archive" "$LEAN_ARCHIVE_URL"
printf '%s  %s\n' "$LEAN_ARCHIVE_SHA256" "$archive" | /usr/bin/sha256sum -c -
/usr/bin/tar --zstd --strip-components=1 -xf "$archive" -C "$install_root"
/usr/bin/rm -f -- "$archive"

lean_bin="$install_root/bin/lean"
lake_bin="$install_root/bin/lake"
test -x "$lean_bin"
test -x "$lake_bin"

printf '%s\n' "$install_root/bin" >> "$GITHUB_PATH"
printf 'Lean binary: %s\n' "$lean_bin"
"$lean_bin" --version
printf 'Lake binary: %s\n' "$lake_bin"
"$lake_bin" --version

"$lean_bin" --version | /usr/bin/grep -Fq 'version 4.32.2'
