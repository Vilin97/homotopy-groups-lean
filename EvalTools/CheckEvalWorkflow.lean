/-
Adapted from leanprover/lean-eval at commit
53348531969dc984e02e3be0379a7282c664abd9.
Modified for homotopy-groups-lean; see NOTICE and LICENSE.
-/

import EvalTools.CheckComparatorInstallation
import EvalTools.Generate
import EvalTools.Manifest
import EvalTools.Markers
import EvalTools.RunEval
import EvalTools.StartProblem

set_option linter.deprecated false

open Lean

namespace EvalTools

set_option autoImplicit false

/-- Replace the first occurrence of `placeholder` in `text` with `replacement`. -/
private def replaceFirst (text placeholder replacement : String) : Option String := Id.run do
  let parts := text.splitOn placeholder
  if parts.length < 2 then return none
  let head := parts.head!
  let rest := parts.tail
  let tail := placeholder.intercalate rest
  return some (head ++ replacement ++ tail)

/-- Replace `  sorry\n` in `Submission.lean` with `replacement`. Mirrors
`replace_placeholder` in `check_eval_workflow.py`. -/
private def replacePlaceholder (workspace : System.FilePath) (replacement : String) :
    IO Unit := do
  let submissionPath := workspace / "Submission.lean"
  let original ← IO.FS.readFile submissionPath
  match replaceFirst original "  sorry\n" replacement with
  | none =>
      throw <| IO.userError s!"Expected placeholder proof in {submissionPath}"
  | some updated =>
      IO.FS.writeFile submissionPath updated

private def prepareSmokeTestWorkspace (root : System.FilePath)
    (workspacesRoot : System.FilePath) : IO System.FilePath := do
  let source := root / "generated" / comparatorSmokeTestProblemId
  if !(← source.isDir) then
    throw <| IO.userError s!"Missing generated workspace: {source}"
  let destination := workspacesRoot / comparatorSmokeTestProblemId
  if let some parent := destination.parent then
    IO.FS.createDirAll parent
  copyTree source destination
  linkTrustedRootDependencies root destination
  return destination

private def assertCounts (summary : ScoreSummary) (attempted succeeded : Nat) (label : String) :
    IO Unit := do
  if summary.attemptedProblems != attempted || summary.succeededProblems != succeeded then
    throw <| IO.userError <|
      s!"{label} produced unexpected results.\n" ++
      s!"Expected attempted={attempted}, succeeded={succeeded}.\n" ++
      s!"Actual summary: attempted={summary.attemptedProblems}, succeeded={summary.succeededProblems} (test attempted/succeeded={summary.attemptedTestProblems}/{summary.succeededTestProblems}, main attempted/succeeded={summary.attemptedMainProblems}/{summary.succeededMainProblems})"

private def summarizeAtRoot (root : System.FilePath) (problems : Array EvalProblemMetadata)
    (workspacesRoot : System.FilePath) : IO ScoreSummary := do
  let scores ← scoreProblems root problems workspacesRoot
  return summarizeScores scores

/-- Implementation of `lake exe homotopy-groups-lean check-eval-workflow`. -/
def runCheckEvalWorkflow (root : System.FilePath) : IO UInt32 := do
  let runBody : IO UInt32 := show IO UInt32 from do
    -- This command exercises one maintained end-to-end fixture. Full-corpus
    -- freshness is checked separately by `generate --check`; re-extracting all
    -- 118 declarations before each of the three smoke-test scores would obscure
    -- the evaluator signal and make the CI check unnecessarily expensive.
    try
      generate root (selectedProblemId := some comparatorSmokeTestProblemId) (check := true)
    catch e =>
      throw <| IO.userError <|
        "Repository is not in a clean generated state.\n" ++
        "Run `lake exe homotopy-groups-lean generate` to refresh generated workspaces, " ++
        "then rerun this check.\n\nDetails:\n" ++ toString e
    let allProblems ← loadManifest root
    validateManifestAgainstInventory root allProblems
    let problems := allProblems.filter fun problem => problem.id == comparatorSmokeTestProblemId
    if problems.size != 1 then
      throw <| IO.userError s!"Expected exactly one maintained smoke problem: {comparatorSmokeTestProblemId}"
    buildExtractor root problems
    -- Use a tempdir under REPO_ROOT so `workspace_path` resolves relative to root.
    let tempName : String := s!"homotopy-groups-lean-workflow-{← IO.rand 0 1000000000}"
    let tempDir := root / tempName
    IO.FS.createDirAll tempDir
    try
      let workspacesRoot := tempDir / "workspaces"
      let initialSummary ← summarizeAtRoot root problems workspacesRoot
      assertCounts initialSummary 0 0 "Pristine eval"
      let workspace ← prepareSmokeTestWorkspace root workspacesRoot
      replacePlaceholder workspace "  exact (by rfl : False)\n"
      let incorrectSummary ← summarizeAtRoot root problems workspacesRoot
      assertCounts incorrectSummary 1 0 "Incorrect homotopy smoke-test attempt"
      IO.FS.removeDirAll workspace
      let workspace2 ← prepareSmokeTestWorkspace root workspacesRoot
      solveComparatorSmokeTest root workspace2
      let correctSummary ← summarizeAtRoot root problems workspacesRoot
      assertCounts correctSummary 1 1 "Correct homotopy smoke-test attempt"
      IO.println "Eval workflow check passed."
      IO.FS.removeDirAll tempDir
      return (0 : UInt32)
    catch e =>
      try IO.FS.removeDirAll tempDir catch _ => pure ()
      throw e
  try
    runBody
  catch e =>
    IO.eprintln (toString e)
    return (1 : UInt32)

end EvalTools
