/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

import EvalTools.StartProblem
import EvalTools.Subprocess

namespace EvalTools

set_option autoImplicit false

structure Semver where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Inhabited, BEq, Repr

namespace Semver

def lt (a b : Semver) : Bool :=
  a.major < b.major
    || (a.major == b.major && (a.minor < b.minor
        || (a.minor == b.minor && a.patch < b.patch)))

def toString (v : Semver) : String := s!"v{v.major}.{v.minor}.{v.patch}"

end Semver

/-- landrun pinned to the same SHA as `.github/workflows/{ci,submission}.yml`.
Bump procedure: see SECURITY.md. -/
def landrunInstallTarget : String :=
  "5ed4a3db3a4ad930d577215c6b9abaa19df7f99f"

def minLandrunVersion : Semver := ⟨0, 1, 14⟩

def requiredLandrunFlags : Array String :=
  #["--best-effort", "--ro", "--rw", "--rox", "--rwx", "--ldd", "--add-exec"]

structure LandrunInspection where
  path : String
  helpText : String
  versionText : Option String
  version : Option Semver

private def isWordChar (c : Char) : Bool :=
  c.isDigit || c.isAlpha

/-- Parse the first `v?MAJOR.MINOR.PATCH` substring out of `text`, mirroring
the Python `re.search(r"\bv?(\d+)\.(\d+)\.(\d+)\b", text)`. -/
def parseSemver (text : String) : Option Semver := Id.run do
  let chars := text.toList
  let n := chars.length
  let arr := chars.toArray
  let isDigit (i : Nat) : Bool := i < n && arr[i]!.isDigit
  let readNumber (start : Nat) : Nat × Nat := Id.run do
    let mut k := start
    while k < n && arr[k]!.isDigit do
      k := k + 1
    return (start, k)
  let toNum (lo hi : Nat) : Option Nat :=
    let s := String.ofList (arr.extract lo hi).toList
    s.toNat?
  let mut i := 0
  while i < n do
    -- Optional leading `v`, but require word boundary before any literal char.
    if i == 0 || !isWordChar arr[i - 1]! then
      let start := if i < n && arr[i]! == 'v' then i + 1 else i
      if isDigit start then
        let (a0, a1) := readNumber start
        if a1 < n && arr[a1]! == '.' && isDigit (a1 + 1) then
          let (b0, b1) := readNumber (a1 + 1)
          if b1 < n && arr[b1]! == '.' && isDigit (b1 + 1) then
            let (c0, c1) := readNumber (b1 + 1)
            if c1 == n || !isWordChar arr[c1]! then
              match toNum a0 a1, toNum b0 b1, toNum c0 c1 with
              | some a, some b, some c => return some ⟨a, b, c⟩
              | _, _, _ => pure ()
    i := i + 1
  return none

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.find? needle).isSome

def missingLandrunFlags (helpText : String) : Array String :=
  requiredLandrunFlags.filter fun flag => !hasSubstr helpText flag

def landrunInstallAdvice : String :=
  String.intercalate "\n" [
    "Comparator currently needs a `landrun` build with `--ldd` and `--add-exec` support.",
    "Released tags through `v0.1.15` are not enough to reliably satisfy comparator's sandboxing needs.",
    "Install or reinstall the project's pinned commit with:",
    s!"  go install github.com/zouuup/landrun/cmd/landrun@{landrunInstallTarget}",
    "Version strings are not sufficient to distinguish landrun commits — upstream main has long reported `0.1.15` even when the SHA differs. `landrunInstallTarget` holds the project's pin and must stay in lockstep with the workflow and SECURITY.md pin table."
  ]

/-- Look up an executable on PATH, returning the resolved absolute path. -/
def which (name : String) : IO (Option String) := do
  let res ← runCmdCaptured "which" #[name] (← IO.currentDir)
  if res.exitCode != 0 then return none
  let trimmed := res.stdout.trimAscii.toString
  if trimmed.isEmpty then return none else return some trimmed

/-- Run a process with `LC_ALL=C` / `LANG=C`, capture both streams. -/
def runCaptureC (cmd : String) (args : Array String) : IO ProcessOutput := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
    env := #[("LC_ALL", some "C"), ("LANG", some "C")]
  }
  return { exitCode := out.exitCode, stdout := out.stdout, stderr := out.stderr }

private def combined (out : ProcessOutput) : String :=
  let parts := [out.stdout, out.stderr].filter (! ·.isEmpty)
  (String.intercalate "\n" parts).trimAscii.toString

def inspectLandrun : IO LandrunInspection := do
  let path? ← which "landrun"
  let path ←
    match path? with
    | some p => pure p
    | none => throw <| IO.userError s!"`landrun` was not found on PATH.\n{landrunInstallAdvice}"
  let helpRun ← runCaptureC path #["--help"]
  let mut helpText := combined helpRun
  if helpText.isEmpty then
    let helpRun2 ← runCaptureC path #["-h"]
    helpText := combined helpRun2
  let versionRun ← runCaptureC path #["--version"]
  let versionText := combined versionRun
  let versionText? := if versionText.isEmpty then none else some versionText
  return {
    path := path
    helpText := helpText
    versionText := versionText?
    version := versionText?.bind parseSemver
  }

def validateLandrun (inspection : LandrunInspection) : Except String Unit := do
  let missing := missingLandrunFlags inspection.helpText
  if !missing.isEmpty then
    let formatted := ", ".intercalate missing.toList
    throw s!"`landrun` at {inspection.path} is missing comparator-required flags: {formatted}\n{landrunInstallAdvice}"
  match inspection.version with
  | some v =>
      if Semver.lt v minLandrunVersion then
        let displayed := inspection.versionText.getD v.toString
        throw <| String.intercalate "\n" [
          s!"`landrun` at {inspection.path} is too old: {displayed}",
          s!"Comparator needs a `landrun` version at or above {minLandrunVersion.toString}.",
          landrunInstallAdvice]
  | none => pure ()

def ensureLandrunCompatible : IO LandrunInspection := do
  let inspection ← inspectLandrun
  match validateLandrun inspection with
  | .ok _ => pure inspection
  | .error msg => throw <| IO.userError msg

/-- Verify the outer sandbox required while landrun cannot deny AF_UNIX itself. -/
def probeSystemdAfUnixIsolation : IO Unit := do
  let some systemdRun ← which "systemd-run"
    | throw <| IO.userError
        "`systemd-run` is required to deny AF_UNIX sockets around comparator."
  let some truePath ← which "true"
    | throw <| IO.userError "Could not locate `true` for the systemd hardening probe."
  let some path ← IO.getEnv "PATH"
    | throw <| IO.userError "PATH is unset; refusing to probe comparator hardening."
  let some home ← IO.getEnv "HOME"
    | throw <| IO.userError "HOME is unset; refusing to probe comparator hardening."
  let cwd ← IO.currentDir
  let args := #[
    "--user", "--pipe", "--wait", "--collect", "--quiet",
    "--property=RestrictAddressFamilies=~AF_UNIX",
    "--property=SystemCallArchitectures=native",
    "--property=SystemCallFilter=~@network-io @aio",
    "--property=PrivateUsers=yes", "--property=ProtectProc=invisible",
    "--property=ProcSubset=pid", "--property=NoNewPrivileges=yes",
    "--property=KillMode=control-group",
    "--property=MemoryMax=12G", "--property=TasksMax=512",
    "--property=LimitNOFILE=4096", "--property=LimitFSIZE=1G",
    "--property=RuntimeMaxSec=20min",
    s!"--working-directory={cwd}", "--", "/usr/bin/env", "-i",
    s!"PATH={path}", s!"HOME={home}", "LANG=C.UTF-8", "LC_ALL=C.UTF-8",
    "LEAN_ABORT_ON_PANIC=1", "UV_USE_IO_URING=0", truePath]
  let probe ← runCaptureC systemdRun args
  if probe.exitCode != 0 then
    let output :=
      let c := combined probe
      if c.isEmpty then "(no output)" else c
    throw <| IO.userError <| String.intercalate "\n" [
      "`systemd-run` failed to enforce the outer evaluator sandbox.",
      "Comparator must not run without process, environment, and network isolation.",
      s!"Probe output:\n{output}"]

def probeLandrunWithLeanToolchain (landrunPath : String) : IO Unit := do
  let some leanPath ← which "lean"
    | throw <| IO.userError "`lean` was not found on PATH while checking comparator prerequisites."
  let prefixRun ← runCaptureC leanPath #["--print-prefix"]
  let leanPrefix := combined prefixRun
  if prefixRun.exitCode != 0 || leanPrefix.isEmpty then
    throw <| IO.userError
      "Failed to determine the active Lean toolchain prefix with `lean --print-prefix`."
  let toolchainLean : System.FilePath := (leanPrefix : System.FilePath) / "bin" / "lean"
  let toolchainLeanStr := toolchainLean.toString
  unless ← toolchainLean.pathExists do
    throw <| IO.userError s!"Lean toolchain binary not found at {toolchainLeanStr}."
  let probeArgs : Array String :=
    #["--best-effort", "--ro", "/", "--rw", "/dev", "--ldd", "--add-exec",
      "--rox", leanPrefix, toolchainLeanStr, "--version"]
  let probe ← runCaptureC landrunPath probeArgs
  if probe.exitCode == 0 then return
  let output :=
    let c := combined probe
    if c.isEmpty then "(no output)" else c
  let cmdline := s!"{landrunPath} {" ".intercalate probeArgs.toList}"
  throw <| IO.userError <| String.intercalate "\n" [
    "`landrun` failed a Lean toolchain execution probe.",
    "Comparator needs `landrun --ldd --add-exec` to execute Lean's dynamically linked toolchain binaries inside the sandbox.",
    "Tagged `landrun` builds such as `v0.1.15` can fail here because they miss newer ELF dependency handling present on upstream `main`.",
    s!"Probe command: {cmdline}",
    s!"Probe output:\n{output}",
    landrunInstallAdvice]

/-- The homotopy problem used for the maintainer-controlled comparator smoke test. -/
def comparatorSmokeTestProblemId : String :=
  "pi1_circle_mulEquiv_int"

/-- Repository-relative maintained solution for `comparatorSmokeTestProblemId`. -/
def comparatorSmokeTestSolution : System.FilePath :=
  "examples" / "submissions" / "pi1_circle" / "Submission.lean"

/-- Install the audited maintained proof without synthesizing source in the test harness. -/
def solveComparatorSmokeTest (root workspace : System.FilePath) : IO Unit := do
  let source := root / comparatorSmokeTestSolution
  unless ← source.pathExists do
    throw <| IO.userError s!"Missing maintained smoke-test solution: {source}"
  IO.FS.writeFile (workspace / "Submission.lean") (← IO.FS.readFile source)

/-- Reuse the repository's reviewed dependency checkout in ephemeral smoke-test
workspaces. The generated workspace remains isolated and receives its own build
directory, while avoiding a fresh multi-gigabyte Mathlib clone for every check. -/
def linkTrustedRootDependencies (root workspace : System.FilePath) : IO Unit := do
  let packages := root / ".lake" / "packages"
  unless ← packages.isDir do
    throw <| IO.userError "Root dependencies are not primed; run `lake update` first."
  let lakeDir := workspace / ".lake"
  IO.FS.createDirAll lakeDir
  let destination := lakeDir / "packages"
  let destinationExists ←
    try
      discard destination.symlinkMetadata
      pure true
    catch _ => pure false
  if destinationExists then
    let expected ← IO.FS.realPath packages
    let actual ←
      try IO.FS.realPath destination
      catch _ => throw <| IO.userError s!"Existing dependency link is broken: {destination}"
    if actual != expected then
      throw <| IO.userError s!"Workspace dependency path does not point to the trusted root packages: {destination}"
    return
  let link ← IO.Process.output {
    cmd := "/bin/ln"
    args := #["-s", packages.toString, destination.toString]
  }
  if link.exitCode != 0 then
    throw <| IO.userError s!"Could not link trusted root dependencies: {link.stderr}"

/-- Run an end-to-end comparator check against a real homotopy-group workspace. -/
def runCheckComparatorInstallation (root : System.FilePath) : IO UInt32 := do
  try
    probeSystemdAfUnixIsolation
    let landrun ← ensureLandrunCompatible
    probeLandrunWithLeanToolchain landrun.path
    match landrun.version with
    | some v => IO.println s!"Using landrun {v.toString} from {landrun.path}."
    | none => IO.println s!"Using landrun at {landrun.path}."
    let source := root / "generated" / comparatorSmokeTestProblemId
    unless ← source.isDir do
      IO.eprintln s!"Missing generated workspace: {source}"
      return (1 : UInt32)
    let tmp ← IO.FS.createTempDir
    try
      let workspace := tmp / comparatorSmokeTestProblemId
      copyTree source workspace
      linkTrustedRootDependencies root workspace
      solveComparatorSmokeTest root workspace
      runCmdCheckedInherit "lake" #["test"] workspace "lake test failed"
      IO.FS.removeDirAll tmp
    catch err =>
      try IO.FS.removeDirAll tmp catch _ => pure ()
      throw err
    IO.println "Comparator check passed."
    return (0 : UInt32)
  catch err =>
    IO.eprintln err
    return (1 : UInt32)

end EvalTools
