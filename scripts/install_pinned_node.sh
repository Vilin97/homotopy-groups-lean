#!/usr/bin/env bash
set -euo pipefail

readonly NODE_VERSION='22.19.0'
readonly NODE_ARCHIVE_URL='https://nodejs.org/dist/v22.19.0/node-v22.19.0-linux-x64.tar.xz'
readonly NODE_ARCHIVE_SHA256='c0649af18e6a24f6fe5535a3e86b341dd49a8e71117c8b68bde973ef834f16f2'

: "${RUNNER_TEMP:?RUNNER_TEMP must be set by the GitHub Actions runner}"
: "${GITHUB_PATH:?GITHUB_PATH must be set by the GitHub Actions runner}"

if [[ "$(/usr/bin/uname -m)" != 'x86_64' ]]; then
  echo 'the pinned Node archive requires an x86_64 runner' >&2
  exit 1
fi

archive="$(/usr/bin/mktemp "$RUNNER_TEMP/node-$NODE_VERSION.XXXXXX.tar.xz")"
install_root="$(/usr/bin/mktemp -d "$RUNNER_TEMP/node-$NODE_VERSION.XXXXXX")"

/usr/bin/curl --fail --location --silent --show-error --retry 5 \
  --proto '=https' --proto-redir '=https' --tlsv1.2 \
  --output "$archive" "$NODE_ARCHIVE_URL"
printf '%s  %s\n' "$NODE_ARCHIVE_SHA256" "$archive" | /usr/bin/sha256sum -c -
/usr/bin/tar -xJf "$archive" --strip-components=1 -C "$install_root"
/usr/bin/rm -f -- "$archive"

node_bin="$install_root/bin/node"
npm_bin="$install_root/bin/npm"
test -x "$node_bin"
test -x "$npm_bin"
[[ "$("$node_bin" --version)" == "v$NODE_VERSION" ]]

printf '%s\n' "$install_root/bin" >> "$GITHUB_PATH"
"$node_bin" --version
PATH="$install_root/bin:/usr/bin:/bin" "$npm_bin" --version
