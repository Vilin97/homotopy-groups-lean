/-
Regression probe for leanprover/lean4#14576, adapted from Lean's
`tests/elab/issue_14576_min.lean` (Apache-2.0).

The vulnerable kernel accepted the malformed nested-inductive declaration
below. A fixed kernel rejects it with `invalid projection`. Keep this probe on
the exact `lean --trust=0` binary used to elaborate hosted submissions.
-/

import Lean

open Lean Elab Command

structure KernelProbeC where
  b : Bool

inductive KernelProbeW : Type where
  | mk (p : Bool)

inductive KernelProbeL (α : Type) (b : Bool) : Type where
  | mk

meta def buildMalformedNestedInductive : CommandElabM Unit := do
  let w := mkBVar 0
  let ew := mkApp (mkConst `KernelProbeE) w
  let malformedProjection :=
    mkProj ``KernelProbeC 0 (mkProj ``KernelProbeC 0 w)
  let nested := mkApp2 (mkConst ``KernelProbeL) ew malformedProjection
  let inductiveType := mkForall `w .default (mkConst ``KernelProbeW) (mkSort 1)
  let constructorType := mkForall `w .default (mkConst ``KernelProbeW) <|
    mkForall `l .default nested (mkApp (mkConst `KernelProbeE) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `KernelProbeE
    type := inductiveType
    ctors := [{ name := `KernelProbeE.mk, type := constructorType }]
  }] false

elab "run_issue_14576_probe" : command => buildMalformedNestedInductive

/--
error: (kernel) invalid projection
  w.1
-/
#guard_msgs in
run_issue_14576_probe
