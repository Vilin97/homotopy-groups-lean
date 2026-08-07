# Security model

Benchmark submissions are untrusted code. A successful proof may consume CPU,
memory, and disk and may attempt process execution, network access, filesystem
reads, environment-variable disclosure, or tampering with trusted artifacts.
Do not run submissions on a host that carries unrelated credentials.

## Trust boundary

Trusted inputs are the reviewed benchmark commit, pinned toolchain and
dependencies, generated `Challenge.lean`, `Solution.lean`, `config.json`, Lake
files, comparator harness, and CI workflow. Participant-owned inputs are
`Submission.lean` and Lean source below `Submission/`; the validator enforces
this boundary for repository submissions.

A passing submission must satisfy both checks:

1. comparator matches the candidate declarations against the trusted solution
   bridge; and
2. `WorkspaceTest.lean` overrides `enable_nanoda` to `true`, so the proof is
   replayed by nanoda's independent kernel.

Comparator must execute inside landrun with the intended read-only/read-write
mounts, executable allowlist, resource limits, and no injected secrets. The
security probes under `scripts/security_probes/` test environment disclosure,
Lake-process escape, and trusted-artifact tampering. `sandbox_engaged_probe.py`
checks that a deliberately hostile workspace is actually constrained.

The complete comparator tree additionally runs as an unprivileged transient
systemd service. Its environment is rebuilt from an empty allowlist; a private
user namespace prevents reads of same-UID host process environments; the
`@network-io` syscall group and AF_UNIX are denied; and systemd's cgroup kills
detached descendants when comparator exits. `systemd_sandbox_probe.py` tests
TCP, UDP, UNIX sockets, host `/proc`, environment isolation, and descendant
cleanup before any hosted submission is fetched. Hosted evaluation is allowed
only on a disposable runner that carries no unrelated credentials. The service
also caps memory, processes, open files, individual file size, and wall time;
RunEval forwards at most 2 MiB from each child output stream. The evaluator
sets `UV_USE_IO_URING=0` before denying `@aio`, so Lean's libuv runtime does not
attempt the intentionally blocked io_uring syscalls.

## Immutable dependency pins

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.2` |
| Mathlib | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| lean4-cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |
| landrun | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| comparator base | `07bc4ea40f2266dcb861820a2ec1fa3244ed307f` |
| comparator terminator patch | upstream `9badaf470d8f724346d33738bd273efacd78df76`; local SHA-256 `a421770633877895de509d185a07bf04169a5c9becd73e595315ec95d40f326c` |
| comparator absolute-tools patch | local SHA-256 `c9796ebf468991d07acc31f2f8e95cef53f61164f03a1ad2302c14f725e2000e` |
| comparator stage-status patch | local SHA-256 `23a7fa6e34ebc79f2b71576db10f012a32bca85400ca7bf246a7337a3dab9ca2` |
| nanoda_lib | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

GitHub Actions and downloaded build inputs must likewise use immutable commit
SHAs. `scripts/action_pin_audit.py` rejects mutable action selectors. A pin bump
requires reviewing the upstream diff, updating every workflow and this table in
one change, rebuilding from a clean cache, and rerunning the comparator smoke
test plus all security probes.

## Operational rules

- Give evaluation jobs only the permissions they need; keep untrusted execution
  separate from jobs that can write repository contents or leaderboard state.
- Never expose deployment keys, app private keys, cloud credentials, or tokens
  to the submission process or its children.
- Treat generated workspaces as reproducible artifacts. Regenerate them from
  reviewed source and manifests rather than accepting participant replacements.
- Upload verdicts and logs only after the sandboxed process has stopped. Verify
  manifest membership, the current trusted-workspace fingerprint, exact evaluator
  pins, workflow identity, benchmark commit, and artifact digest before ingestion.
- Fail closed when landrun, comparator, lean4export, or nanoda is absent or when
  a security probe detects unexpected access.
- Resolve Lake, Lean, Git, landrun, lean4export, nanoda, comparator, and
  `systemd-run` before untrusted elaboration. Resolve the active toolchain with
  the trusted elan launcher outside the syscall-filtered service, then invoke
  the real `<prefix>/bin/lake` and `<prefix>/bin/lean` binaries inside it. The
  pinned comparator patch makes its internal build commands use those absolute
  paths, even though `lake env` necessarily adds workspace build directories to
  the child environment.
- Use the comparator's trusted stage marker plus its service exit status to
  distinguish a candidate rejection from setup, service, signal, or timeout
  failures. The random marker file is outside landrun's writable workspace.

## Hosted intake and result separation

`.github/workflows/submission.yml` triggers once on `issues: opened`; evaluation
does not depend on asynchronous label delivery. A repository-wide concurrency
group admits one expensive evaluation at a time and uses GitHub's bounded
`queue: max` FIFO queue (up to 100 waiting runs), so a newer submission does not
silently replace an older pending one. Result writes use the same queueing mode.

The intake accepts only a public `https://github.com/owner/repository` URL and a
full commit SHA. It authenticates GitHub repository-metadata requests with a
step-scoped `GITHUB_TOKEN`; that token is removed from every Git subprocess
environment and must not be present during untrusted elaboration. GitHub's
repository-size metadata must be at most 102,400 KiB, and each Git subprocess
has a 60-second timeout. Before provisioning evaluator tools, the cheap gate
fetches the exact commit and inspects the requested path and allowlisted proof
files without executing submitted code. Intake rejects path traversal,
symlinks, oversized source sets, and more than 128 proof files, then overlays
only `Submission.lean` and `Submission/**/*.lean` onto a freshly generated
trusted workspace. Dependency priming runs only trusted `lake update`, Mathlib
cache code, and the isolated benchmark-owned `Challenge` target. This creates
Lake's replay metadata before the dependency tree becomes read-only and must
never precompile a target importing `Submission`.

The evaluation job has only `contents: read`; checkout credentials are not
persisted and `.git` metadata is stripped before untrusted elaboration. Only
after comparator stops does it create a bounded, source-free JSON verdict and
SHA-256 digest. Intake binds that verdict to a deterministic SHA-256 fingerprint
of every trusted file in the pristine generated problem workspace. A separate
`contents: write` job recomputes that fingerprint and validates manifest
membership, exact toolchain and comparator-patch pins, actor, issue, eligibility,
run attempt, benchmark and submission SHAs, digest, the exact proof-file path
allowlist, and agreement between the outcome and all three checks. It then writes
a new, never-overwritten `results/issue-…-run-…-attempt-….json` file. Before
deriving tracker or leaderboard data, every stored result is revalidated for its
exact field set, types, outcome/check agreement, score binding, evaluator pins,
proof-file allowlist, and workflow-bound filename. A valid retained result
counts only while its fingerprint still matches the current benchmark. A third
issues-only job posts the human-readable result; it has no access to untrusted
source.

The patched comparator writes a trusted verdict marker outside landrun's
writable tree. The random enforced config is mode `0444` and the random marker
is mode `0666` so the `PrivateUsers=yes` remapped comparator can read/update
them; candidate children neither receive the marker path nor have Landlock
write access outside `.lake`. `WorkspaceTest.lean` reserves exit code 2 only
for the comparator's explicit `candidate_rejected` result after either a
solution build returns its ordinary error code 1 or its pure declaration/axiom
comparison returns a mismatch. Other build exits and every export, kernel, or
sandbox-child failure remain infrastructure errors: tool failures, exceptions,
crashes, signals, resource kills, timeouts, stale markers, and malformed output
cannot be inferred to be a rejection. Only exit code 0 paired with the explicit
`accepted` marker can become `accepted`.

Report vulnerabilities privately to the repository maintainers before opening a
public issue. Include the affected commit, threat scenario, reproduction steps,
and whether credentials or leaderboard integrity may have been exposed.

This design and its probes are adapted from the Apache-2.0 `lean-eval` security
model; see `NOTICE` for attribution.
