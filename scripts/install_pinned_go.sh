#!/usr/bin/env bash
set -euo pipefail

readonly GO_VERSION='1.25.12'
readonly GO_ARCHIVE_URL='https://go.dev/dl/go1.25.12.linux-amd64.tar.gz'
readonly GO_ARCHIVE_SHA256='234828b7a89e0e303d2556310ee549fbcf253d28de937bac3da13d6294262ac1'

: "${RUNNER_TEMP:?RUNNER_TEMP must be set by the GitHub Actions runner}"
: "${GITHUB_PATH:?GITHUB_PATH must be set by the GitHub Actions runner}"
: "${GITHUB_ENV:?GITHUB_ENV must be set by the GitHub Actions runner}"

if [[ "$(/usr/bin/uname -m)" != 'x86_64' ]]; then
  echo 'the pinned Go archive requires an x86_64 runner' >&2
  exit 1
fi

archive="$(/usr/bin/mktemp "$RUNNER_TEMP/go-$GO_VERSION.XXXXXX.tar.gz")"
install_parent="$(/usr/bin/mktemp -d "$RUNNER_TEMP/go-$GO_VERSION.XXXXXX")"

/usr/bin/curl --fail --location --silent --show-error --retry 5 \
  --proto '=https' --proto-redir '=https' --tlsv1.2 \
  --output "$archive" "$GO_ARCHIVE_URL"
printf '%s  %s\n' "$GO_ARCHIVE_SHA256" "$archive" | /usr/bin/sha256sum -c -
/usr/bin/tar -xzf "$archive" -C "$install_parent"
/usr/bin/rm -f -- "$archive"

go_bin="$install_parent/go/bin/go"
test -x "$go_bin"
[[ "$("$go_bin" version)" == go\ version\ go"$GO_VERSION"\ * ]]

printf '%s\n' "$install_parent/go/bin" >> "$GITHUB_PATH"
printf '%s\n' 'GOTOOLCHAIN=local' >> "$GITHUB_ENV"
"$go_bin" version
