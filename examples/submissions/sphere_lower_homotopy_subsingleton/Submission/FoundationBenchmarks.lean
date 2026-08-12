/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.Homotopy.HSpaces
import Submission.Homotopy.FibrationLESGroup

/-!
# Remaining foundational benchmark bridges

This file supplies two general constructions needed by the foundational benchmark statements:
the Eckmann--Hilton proof that the fundamental group of an H-space is commutative, and the
homeomorphism from one-dimensional generalized loops to ordinary based paths that turns the
path-fibration loop shift into the benchmark's exact `GenLoop` formulation.
-/

open scoped ContinuousMap Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

universe u

namespace HSpacePiOne

variable {X : Type u} [TopologicalSpace X] [HSpace X]

private def hmulPath (p q : Path (HSpace.e : X) (HSpace.e : X)) :
    Path (HSpace.e : X) (HSpace.e : X) where
  toFun t := HSpace.hmul (p t, q t)
  continuous_toFun := by fun_prop
  source' := by rw [p.source, q.source, HSpace.hmul_e_e]
  target' := by rw [p.target, q.target, HSpace.hmul_e_e]

private def hmulPathHomotopy {p p' q q' : Path (HSpace.e : X) (HSpace.e : X)}
    (F : Path.Homotopy p p') (G : Path.Homotopy q q') :
    Path.Homotopy (hmulPath p q) (hmulPath p' q') where
  toFun tx := HSpace.hmul (F tx, G tx)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp [hmulPath]
  map_one_left t := by simp [hmulPath]
  prop' t s hs := by
    rcases hs with rfl | hs
    · simp [hmulPath]
    · rw [Set.mem_singleton_iff] at hs
      subst s
      simp [hmulPath]

private def hmulClass
    (a b : FundamentalGroup X (HSpace.e : X)) :
    FundamentalGroup X (HSpace.e : X) :=
  Quotient.map₂ hmulPath
    (fun _ _ hp _ _ hq ↦ Nonempty.map2 hmulPathHomotopy hp hq) a b

private def hmulReflLeftHomotopy (p : Path (HSpace.e : X) (HSpace.e : X)) :
    Path.Homotopy (hmulPath (Path.refl (HSpace.e : X)) p) p where
  toFun tx := HSpace.eHmul (tx.1, p tx.2)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp [hmulPath]
  map_one_left t := by simp
  prop' t s hs := by
    rcases hs with rfl | hs
    · simpa [hmulPath] using HSpace.eHmul.eq_fst t (Set.mem_singleton HSpace.e)
    · rw [Set.mem_singleton_iff] at hs
      subst s
      simpa [hmulPath] using HSpace.eHmul.eq_fst t (Set.mem_singleton HSpace.e)

private def hmulReflRightHomotopy (p : Path (HSpace.e : X) (HSpace.e : X)) :
    Path.Homotopy (hmulPath p (Path.refl (HSpace.e : X))) p where
  toFun tx := HSpace.hmulE (tx.1, p tx.2)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp [hmulPath]
  map_one_left t := by simp
  prop' t s hs := by
    rcases hs with rfl | hs
    · simpa [hmulPath] using HSpace.hmulE.eq_fst t (Set.mem_singleton HSpace.e)
    · rw [Set.mem_singleton_iff] at hs
      subst s
      simpa [hmulPath] using HSpace.hmulE.eq_fst t (Set.mem_singleton HSpace.e)

private theorem hmulClass_one_left (a : FundamentalGroup X (HSpace.e : X)) :
    hmulClass 1 a = a := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact Quotient.sound ⟨hmulReflLeftHomotopy p⟩

private theorem hmulClass_one_right (a : FundamentalGroup X (HSpace.e : X)) :
    hmulClass a 1 = a := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact Quotient.sound ⟨hmulReflRightHomotopy p⟩

private theorem hmulPath_trans (p q r s : Path (HSpace.e : X) (HSpace.e : X)) :
    hmulPath (p.trans q) (r.trans s) =
      (hmulPath p r).trans (hmulPath q s) := by
  ext t
  simp only [hmulPath, Path.trans_apply, Path.coe_mk_mk]
  split_ifs <;> rfl

private theorem hmulClass_interchange
    (a b c d : FundamentalGroup X (HSpace.e : X)) :
    hmulClass (a * b) (c * d) = hmulClass a c * hmulClass b d := by
  refine Quotient.inductionOn a fun p ↦ ?_
  refine Quotient.inductionOn b fun q ↦ ?_
  refine Quotient.inductionOn c fun r ↦ ?_
  refine Quotient.inductionOn d fun s ↦ ?_
  exact congr_arg
    (fun z : Path (HSpace.e : X) (HSpace.e : X) ↦
      (⟦z⟧ : FundamentalGroup X (HSpace.e : X)))
    (hmulPath_trans q p s r)

private theorem fundamentalGroup_mul_comm
    (a b : FundamentalGroup X (HSpace.e : X)) : a * b = b * a := by
  let hunit : EckmannHilton.IsUnital hmulClass
      (1 : FundamentalGroup X (HSpace.e : X)) :=
    { left_id := hmulClass_one_left
      right_id := hmulClass_one_right }
  exact (EckmannHilton.commGroup hunit hmulClass_interchange).mul_comm a b

end HSpacePiOne

/-- The fundamental group of an H-space is commutative. -/
theorem pi1_hSpace_mul_comm
    (X : Type u) [TopologicalSpace X] [HSpace X]
    (a b : HomotopyGroup.Pi 1 X HSpace.e) :
    a * b = b * a := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simpa using HSpacePiOne.fundamentalGroup_mul_comm
    (X := X)
    (HomotopyGroup.pi1MulEquivFundamentalGroup a)
    (HomotopyGroup.pi1MulEquivFundamentalGroup b)

/-- One-dimensional generalized loops are homeomorphic to ordinary based paths. -/
def genLoopOneHomeomorphPath {X : Type u} [TopologicalSpace X] (x : X) :
    GenLoop (Fin 1) X x ≃ₜ Path x x where
  toEquiv := genLoopEquivOfUnique (Fin 1)
  continuous_toFun := by
    rw [← Path.continuous_uncurry_iff]
    change Continuous fun z : GenLoop (Fin 1) X x × I ↦ z.1.1 (fun _ ↦ z.2)
    exact continuous_eval.comp <|
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_pi fun _ ↦ continuous_snd)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous fun z : Path x x × (Fin 1 → I) ↦ z.1 (z.2 default)
    exact continuous_eval.comp <|
      continuous_fst.prodMk ((continuous_apply default).comp continuous_snd)

@[simp]
theorem genLoopOneHomeomorphPath_const {X : Type u} [TopologicalSpace X] (x : X) :
    genLoopOneHomeomorphPath x (GenLoop.const : GenLoop (Fin 1) X x) = Path.refl x := by
  rfl

/-- Loop spaces shift every positive homotopy group, in the exact generalized-loop model. -/
theorem homotopyGroup_loop_shift
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty
      (HomotopyGroup.Pi (n + 1)
          (GenLoop (Fin 1) X x) GenLoop.const ≃*
        HomotopyGroup.Pi (n + 2) X x) := by
  let e : HomotopyGroup.Pi (n + 2) X x ≃*
      HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) :=
    (fibDeltaMulEquiv (loopBase x) (isSerreFibration_ev₁ X x) n
      (subsingleton_pi_pathSpace x (n + 2) _)
      (subsingleton_pi_pathSpace x (n + 1) _)).trans
      (HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (n + 1))
        (fibreEv₁Homeomorph X x) rfl)
  exact ⟨(HomotopyGroup.homeomorphMulEquivOfEq
    (N := Fin (n + 1)) (genLoopOneHomeomorphPath x)
    (genLoopOneHomeomorphPath_const x)).trans e.symm⟩

end Submission
