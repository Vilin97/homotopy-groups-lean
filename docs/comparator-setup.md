# Local comparator setup

Generated workspaces call four external executables. Build the immutable pins
listed below; do not substitute branch names or release tags.

```bash
go install github.com/zouuup/landrun/cmd/landrun@5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
export PATH="$(go env GOPATH)/bin:$PATH"

benchmark_root="$(pwd)"
benchmark_tools="$(mktemp -d)"

git clone https://github.com/leanprover/lean4export.git "$benchmark_tools/lean4export"
git -C "$benchmark_tools/lean4export" checkout 4e7915201d3f9f04470d9eae002fa695f7cdc589
cp "$benchmark_root/lean-toolchain" "$benchmark_tools/lean4export/lean-toolchain"
(cd "$benchmark_tools/lean4export" && lake build lean4export)
export PATH="$benchmark_tools/lean4export/.lake/build/bin:$PATH"

git clone https://github.com/leanprover/comparator.git "$benchmark_tools/comparator"
git -C "$benchmark_tools/comparator" checkout 07bc4ea40f2266dcb861820a2ec1fa3244ed307f
cp "$benchmark_root/lean-toolchain" "$benchmark_tools/comparator/lean-toolchain"
git -C "$benchmark_tools/comparator" apply "$benchmark_root/patches/comparator-landrun-terminator.patch"
git -C "$benchmark_tools/comparator" apply "$benchmark_root/patches/comparator-absolute-tools.patch"
git -C "$benchmark_tools/comparator" apply "$benchmark_root/patches/comparator-stage-status.patch"
(cd "$benchmark_tools/comparator" && lake build comparator)
export PATH="$benchmark_tools/comparator/.lake/build/bin:$PATH"

git clone https://github.com/robsimmons/nanoda_lib.git "$benchmark_tools/nanoda_lib"
git -C "$benchmark_tools/nanoda_lib" checkout 68d5ca9db226849b41a6fff59d796ff19d0a8840
(cd "$benchmark_tools/nanoda_lib" && cargo build --release)
export PATH="$benchmark_tools/nanoda_lib/target/release:$PATH"
```

`lean4export` and comparator must be rebuilt with this repository's exact Lean
toolchain. Otherwise incompatible `.olean` headers cause a read error unrelated
to the candidate proof. The terminator patch is the one-line upstream fix that
protects lean4export's declaration separator from landrun's option parser. The
absolute-tools patch makes comparator use evaluator-resolved Lake, Lean, and Git
paths, closing workspace `PATH` shadowing while preserving the `lake env`
module path required by lean4export. The stage-status patch lets the harness
reserve exit code 2 only for an explicit comparator mismatch verdict or the
solution builder's ordinary error code 1. Other child exits, export/kernel
failures, setup errors, service failures, timeouts, signals, and resource kills
remain evaluator infrastructure errors. The harness resolves the real toolchain
Lake and Lean binaries through `lean --print-prefix` before entering the
network-syscall filter and sets `UV_USE_IO_URING=0` while retaining the `@aio`
denial. Immediately before starting that service, the harness builds only the
trusted `Challenge` target. Lean 4.32 can create replay hashes beside cached
Mathlib artifacts; priming this non-submission target first lets landrun keep
dependencies read-only while elaborating the candidate. Clear stale workspace
`.lake/build` output after changing any toolchain.

Verify the external interface and a full accepted submission:

```bash
lake exe homotopy-groups-lean check-comparator-installation
```

If comparator is not on `PATH`, set `COMPARATOR_BIN` when running `lake test`.
Comparator still needs `systemd-run`, `landrun`, `lean4export`, `nanoda_bin`,
Lake, Lean, and Git on `PATH` at harness startup. Each is resolved to a trusted
absolute path before the isolated service starts. Invoke comparator through
`lake test`; a bare comparator command omits the required process, environment,
and network isolation.
