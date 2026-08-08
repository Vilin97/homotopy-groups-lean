import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy unitInterval

universe u

noncomputable section

namespace Submission

namespace HSpacePiOne

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Pointwise H-space multiplication of two loops based at the H-space unit. -/
private def hmulPath (p q : Path (HSpace.e : X) (HSpace.e : X)) :
    Path (HSpace.e : X) (HSpace.e : X) where
  toFun t := HSpace.hmul (p t, q t)
  continuous_toFun := by fun_prop
  source' := by rw [p.source, q.source, HSpace.hmul_e_e]
  target' := by rw [p.target, q.target, HSpace.hmul_e_e]

/-- Pointwise multiplication respects homotopy relative to the loop endpoints. -/
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

/-- The second, pointwise multiplication on the fundamental group. -/
private def hmulClass
    (a b : FundamentalGroup X (HSpace.e : X)) :
    FundamentalGroup X (HSpace.e : X) :=
  Quotient.map₂ hmulPath
    (fun _ _ hp _ _ hq => Nonempty.map2 hmulPathHomotopy hp hq) a b

/-- The H-space left-unit homotopy, restricted along a loop. -/
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

/-- The H-space right-unit homotopy, restricted along a loop. -/
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
  refine Quotient.inductionOn a fun p => ?_
  exact Quotient.sound ⟨hmulReflLeftHomotopy p⟩

private theorem hmulClass_one_right (a : FundamentalGroup X (HSpace.e : X)) :
    hmulClass a 1 = a := by
  refine Quotient.inductionOn a fun p => ?_
  exact Quotient.sound ⟨hmulReflRightHomotopy p⟩

/-- Pointwise multiplication interchanges strictly with path concatenation. -/
private theorem hmulPath_trans (p q r s : Path (HSpace.e : X) (HSpace.e : X)) :
    hmulPath (p.trans q) (r.trans s) =
      (hmulPath p r).trans (hmulPath q s) := by
  ext t
  simp only [hmulPath, Path.trans_apply, Path.coe_mk_mk]
  split_ifs <;> rfl

private theorem hmulClass_interchange
    (a b c d : FundamentalGroup X (HSpace.e : X)) :
    hmulClass (a * b) (c * d) = hmulClass a c * hmulClass b d := by
  refine Quotient.inductionOn a fun p => ?_
  refine Quotient.inductionOn b fun q => ?_
  refine Quotient.inductionOn c fun r => ?_
  refine Quotient.inductionOn d fun s => ?_
  exact congr_arg
    (fun z : Path (HSpace.e : X) (HSpace.e : X) =>
      (⟦z⟧ : FundamentalGroup X (HSpace.e : X)))
    (hmulPath_trans q p s r)

/-- Eckmann--Hilton for ordinary loop concatenation and pointwise H-space
multiplication. -/
private theorem fundamentalGroup_mul_comm
    (a b : FundamentalGroup X (HSpace.e : X)) : a * b = b * a := by
  let hunit : EckmannHilton.IsUnital hmulClass
      (1 : FundamentalGroup X (HSpace.e : X)) :=
    { left_id := hmulClass_one_left
      right_id := hmulClass_one_right }
  exact (EckmannHilton.commGroup hunit hmulClass_interchange).mul_comm a b

end HSpacePiOne

open HSpacePiOne

theorem pi1_hSpace_mul_comm
    (X : Type u) [TopologicalSpace X] [HSpace X]
    (a b : HomotopyGroup.Pi 1 X HSpace.e) :
    a * b = b * a := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simpa using fundamentalGroup_mul_comm
    (X := X)
    (HomotopyGroup.pi1MulEquivFundamentalGroup a)
    (HomotopyGroup.pi1MulEquivFundamentalGroup b)

end Submission
