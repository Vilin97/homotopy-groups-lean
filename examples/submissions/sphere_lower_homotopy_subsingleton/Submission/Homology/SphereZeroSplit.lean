/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.RightExact
import Submission.Homology.SphereZero

/-!
# `H₀(S⁰) ≅ ℤ ⊞ ℤ`

`S⁰` is the disjoint union of its two points, both of which are open (it is discrete).  Additivity
of `H₀` over a clopen partition (`isIso_mvKappa_zero_of_isEmpty_inter`) therefore identifies
`H₀(S⁰)` with `H₀(pt) ⊞ H₀(pt) ≅ ℤ ⊞ ℤ`.

This is the last input needed for `H₁(S¹) ≅ ℤ`: the Mayer–Vietoris connecting map identifies
`H₁(S¹)` with the kernel of the "sum" map `H₀(S⁰) ⟶ H₀(pt)`, which under the identification below
is `biprod.desc 𝟙 (-𝟙) : ℤ ⊞ ℤ ⟶ ℤ`, whose kernel is the antidiagonal copy of `ℤ`.

## Main results

* `sphZeroPtSet` — the two singletons of `S⁰`;
* `hgrpZeroSphZeroIso` — `H₀({p₀}) ⊞ H₀({p₁}) ≅ H₀(S⁰)`;
* `hgrpZeroSphZeroIsoZZ` — `ℤ ⊞ ℤ ≅ H₀(S⁰)`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- The singleton subset of `S⁰` at one of its two points. -/
def sphZeroPtSet (b : Bool) : Set (Sph 0) := {sphZeroOfBool b}

instance instUniqueSphZeroPtSet (b : Bool) : Unique (sphZeroPtSet b) where
  default := ⟨sphZeroOfBool b, rfl⟩
  uniq := fun y => Subtype.ext y.2

instance instPathConnectedSpaceSphZeroPtSet (b : Bool) :
    PathConnectedSpace (sphZeroPtSet b) := by
  constructor
  · exact ⟨default⟩
  · intro x y
    obtain rfl : x = y := Subsingleton.elim x y
    exact ⟨Path.refl x⟩

instance instIsEmptySphZeroPtSetInter :
    IsEmpty ((sphZeroPtSet false ∩ sphZeroPtSet true : Set (Sph 0))) := by
  refine ⟨fun z => ?_⟩
  have h : sphZeroOfBool false = sphZeroOfBool true := z.2.1.symm.trans z.2.2
  exact Bool.noConfusion (sphZeroOfBool_injective h)

/-- The two points of `S⁰` cover it, and each is open. -/
theorem sphZeroPtSet_interior_union :
    interior (sphZeroPtSet false) ∪ interior (sphZeroPtSet true) = Set.univ := by
  rw [(isOpen_discrete _).interior_eq, (isOpen_discrete _).interior_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨b, rfl⟩ := sphZeroOfBool_surjective x
  match b with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

/-- **`H₀(S⁰)` splits as the sum of the `H₀`'s of its two points.** -/
def hgrpZeroSphZeroIso :
    mvSum (X := TopCat.of (Sph 0)) (sphZeroPtSet false) (sphZeroPtSet true) 0 ≅
      Hgrp 0 (TopCat.of (Sph 0)) :=
  mvKappaZeroIso (X := TopCat.of (Sph 0)) (sphZeroPtSet false) (sphZeroPtSet true)
    sphZeroPtSet_interior_union

/-- `H₀` of a one-point subspace of `S⁰` is `ℤ`. -/
def hgrpZeroSphZeroPtIso (b : Bool) :
    Hgrp 0 (TopCat.of (sphZeroPtSet b)) ≅ AddCommGrpCat.of ℤ :=
  hgrpZeroIso (TopCat.of (sphZeroPtSet b))

/-- **`ℤ ⊞ ℤ ≅ H₀(S⁰)`.** -/
def hgrpZeroSphZeroIsoZZ :
    (AddCommGrpCat.of ℤ ⊞ AddCommGrpCat.of ℤ) ≅ Hgrp 0 (TopCat.of (Sph 0)) :=
  (biprod.mapIso (hgrpZeroSphZeroPtIso false) (hgrpZeroSphZeroPtIso true)).symm ≪≫
    hgrpZeroSphZeroIso

end Submission
