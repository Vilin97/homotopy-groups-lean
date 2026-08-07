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
caps memory at 12 GiB, processes at 512, open files at 4,096, individual file
size at 1 GiB, and wall time at 45 minutes; RunEval forwards at most 2 MiB from
each child output stream. The evaluator
sets `UV_USE_IO_URING=0` before denying `@aio`, so Lean's libuv runtime does not
attempt the intentionally blocked io_uring syscalls.

## Immutable dependency pins

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.2` |
| Lean Linux archive | SHA-256 `5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa` |
| Mathlib | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| lean4-cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |
| landrun | `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f` |
| lean4export | `4e7915201d3f9f04470d9eae002fa695f7cdc589` |
| comparator base | `07bc4ea40f2266dcb861820a2ec1fa3244ed307f` |
| comparator terminator patch | upstream `9badaf470d8f724346d33738bd273efacd78df76`; local SHA-256 `a421770633877895de509d185a07bf04169a5c9becd73e595315ec95d40f326c` |
| comparator absolute-tools patch | local SHA-256 `c9796ebf468991d07acc31f2f8e95cef53f61164f03a1ad2302c14f725e2000e` |
| comparator stage-status patch | local SHA-256 `23a7fa6e34ebc79f2b71576db10f012a32bca85400ca7bf246a7337a3dab9ca2` |
| nanoda_lib | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Go Linux archive | `1.25.12`; SHA-256 `234828b7a89e0e303d2556310ee549fbcf253d28de937bac3da13d6294262ac1` |
| Node Linux archive | `22.19.0`; SHA-256 `c0649af18e6a24f6fe5535a3e86b341dd49a8e71117c8b68bde973ef834f16f2` |

Hosted jobs use the fixed `ubuntu-24.04` label. `/usr/bin/python3`, Cargo, Rust,
and the operating-system utilities used to install verified archives are part
of the trusted GitHub runner image; its patch revision is a CI-platform trust
dependency, not a repository-pinned byte image. Lean, Go, and Node are fetched
from fixed official URLs and verified against the SHA-256 values above before
extraction. GitHub Actions must use immutable commit SHAs. The audit rejects
moving runner aliases and setup actions whose pinned implementations still
fetch mutable manifests or unverified installers at runtime. A pin bump requires
reviewing the upstream diff, updating every workflow and this table in one
change, rebuilding from a clean cache, and rerunning the comparator smoke test
plus all security probes.

Mathlib build artifacts are the deliberate exception to fetch-time byte
identity. Evaluation disables Mathlib's automatic post-update cache hook,
clears custom cache URL/source/repository-scope overrides, and explicitly reads
only the `leanprover-community/mathlib4` `master,legacy` chain. `master` admits
uploads from trusted mathlib4 `master`/`staging` CI writers; `legacy` is a
read-only mirror of master-built artifacts retained for older stable commits.
Its keys are derived from pinned source contents, imports, Lean toolchain, and
build configuration. The benchmark therefore trusts those maintainers, GitHub
CI identity and credentials, and the Azure cache tenant and container controls.
Compromise of those actors or services, upstream Lean releases, or the
CI/storage platform remains out of scope. Fork, nightly, PR-toolchain,
custom-URL, scoped, and unsafe cache sources are not read. This matches the
trust boundary documented by the pinned Mathlib cache client; cache keys
identify build inputs rather than the downloaded bytes.

Every hosted verdict records the evaluator-relevant values above in its exact
`toolchain` identity: runner label, Lean and Go versions and archive digests,
the Mathlib cache repository and source container, and the 45-minute isolated
service deadline. Node is omitted because it is used only by CI's website
build, not by submission evaluation.

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
  `systemd-run` before untrusted elaboration. Install the digest-verified Lean
  release outside the syscall-filtered service, then invoke its real
  `<prefix>/bin/lake` and `<prefix>/bin/lean` binaries inside it. The
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

Report vulnerabilities through GitHub's private **Report a vulnerability**
channel at
<https://github.com/Vilin97/homotopy-groups-lean/security/advisories/new>
before opening a public issue. Include the affected commit, threat scenario,
reproduction steps, and whether credentials or leaderboard integrity may have
been exposed.

This design and its probes are adapted from the Apache-2.0 `lean-eval` security
model; see `NOTICE` for attribution.
