/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Sphere
import Submission.Cohomology.MayerVietorisIso
import Submission.Homology.SphereOne

/-!
# Nonzero top-degree cohomology classes of spheres

Degree-zero evaluation identifies cohomology of the equatorial belt in `S¹` with homomorphisms
out of its zeroth homology.  The functional which distinguishes the belt's two components is not
in the image of the two contractible hemispheres, so Mayer--Vietoris sends it to a nonzero class
in `H¹(S¹; 𝔽₂)`.  Cohomological suspension then supplies a distinguished nonzero top-degree
class on every positive-dimensional sphere.

## Main results

* `Submission.sphereOneModTwoClass_ne_zero` -- `H¹(S¹; 𝔽₂)` has a nonzero class;
* `Submission.sphereOneModTwoDualClass_evaluation` -- the distinguished circle class evaluates
  to one on an explicit homology class;
* `Submission.sphereTopModTwoClass_ne_zero` -- the top mod-two cohomology of every positive
  sphere is nonzero;
* `Submission.sphereTopModTwoDualClass_evaluation` -- every distinguished top class evaluates
  to one on a matching top-dimensional homology class;
* `Submission.sphereTopCohomologyEquivModTwo` -- top-degree mod-two cohomology of every
  positive-dimensional sphere is `𝔽₂`;
* `Submission.sphereThreeModTwoClass_ne_zero` -- the degree-three specialization needed for the
  suspended Hopf map.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- Mod-two coefficients, regarded as an object of the category of abelian groups. -/
abbrev modTwoCoefficients : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)

/-- The canonical generator of the homology of a point. -/
def hptGenerator : Hpt :=
  (hgrpZeroIso (TopCat.of PUnit.{1})).inv (1 : ℤ)

@[simp]
theorem hgrpZeroIso_hptGenerator :
    (hgrpZeroIso (TopCat.of PUnit.{1})).hom hptGenerator = (1 : ℤ) := by
  rw [hptGenerator, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]

/-- The mod-two functional selecting the first component of the equatorial belt. -/
def beltParity : Hgrp 0 (TopCat.of belt1) ⟶ modTwoCoefficients :=
  beltOneSplitIso.inv ≫ biprod.fst ≫
    (hgrpZeroIso (TopCat.of PUnit.{1})).hom ≫
      AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

/-- The belt functional takes value one on the antidiagonal generator. -/
@[simp]
theorem beltParity_beltAntidiag_generator :
    beltParity (beltAntidiag hptGenerator) = (1 : ZMod 2) := by
  rw [beltParity, beltAntidiag]
  simp only [ConcreteCategory.comp_apply]
  have hcancel : beltOneSplitIso.inv
      (beltOneSplitIso.hom
        (biprod.lift (𝟙 Hpt) (𝟙 Hpt) hptGenerator)) =
      biprod.lift (𝟙 Hpt) (𝟙 Hpt) hptGenerator := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  rw [hcancel]
  have hlift : (biprod.fst : Hpt ⊞ Hpt ⟶ Hpt)
      (biprod.lift (𝟙 Hpt) (𝟙 Hpt) hptGenerator) = hptGenerator := by
    rw [← ConcreteCategory.comp_apply, biprod.lift_fst, ConcreteCategory.id_apply]
  rw [hlift, hgrpZeroIso_hptGenerator]
  rfl

/-- The degree-zero cohomology class represented by `beltParity`. -/
def beltParityDual :
    (homDual (Csing (TopCat.of belt1)) modTwoCoefficients).homology 0 :=
  Classical.choose
    ((ev_zero_bijective (Csing (TopCat.of belt1)) modTwoCoefficients).2 beltParity)

/-- Evaluation of the chosen belt cohomology class recovers `beltParity`. -/
@[simp]
theorem ev_beltParityDual :
    ev (Csing (TopCat.of belt1)) modTwoCoefficients 0 beltParityDual = beltParity :=
  Classical.choose_spec
    ((ev_zero_bijective (Csing (TopCat.of belt1)) modTwoCoefficients).2 beltParity)

/-- The antidiagonal belt class is killed by the degree-zero Mayer--Vietoris map. -/
theorem beltAntidiag_comp_mvIota :
    beltAntidiag ≫
      mvIota (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0 = 0 := by
  rw [mvIota_zero_factor (X := TopCat.of (Sph 1)), ← Category.assoc,
    beltAntidiag_comp_aug, zero_comp]

/-- The belt antidiagonal generator belongs to the kernel of the degree-zero
Mayer--Vietoris map. -/
theorem mvIota_beltAntidiag_generator :
    mvIota (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0
      (beltAntidiag hptGenerator) = 0 := by
  rw [← ConcreteCategory.comp_apply, beltAntidiag_comp_mvIota]
  rfl

/-- A circle homology class whose Mayer--Vietoris boundary is the oriented belt generator. -/
noncomputable def sphereOneHomologyClass : Hgrp 1 (TopCat.of (Sph 1)) :=
  Classical.choose ((ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_δ_iota
      (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)
      (sphCap_interior_union 0) 0)
    (beltAntidiag hptGenerator) mvIota_beltAntidiag_generator)

@[simp]
theorem mvδ_sphereOneHomologyClass :
    mvδ (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)
      (sphCap_interior_union 0) 0 sphereOneHomologyClass =
        beltAntidiag hptGenerator :=
  Classical.choose_spec ((ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_δ_iota
      (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)
      (sphCap_interior_union 0) 0)
    (beltAntidiag hptGenerator) mvIota_beltAntidiag_generator)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `H₁(S¹) ≅ H₀(pt)` used to compute sphere homology intertwines the
Mayer--Vietoris boundary with the belt antidiagonal. -/
theorem hgrpOneSphereOneIsoPt_hom_comp_beltAntidiag :
    hgrpOneSphereOneIsoPt.hom ≫ beltAntidiag =
      mvδ (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)
        (sphCap_interior_union 0) 0 := by
  simp only [hgrpOneSphereOneIsoPt]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

set_option backward.isDefEq.respectTransparency false in
/-- The selected circle homology class is the positive generator under `H₁(S¹) ≅ ℤ`. -/
@[simp]
theorem hgrpOneSphereOneIso_sphereOneHomologyClass :
    hgrpOneSphereOneIso.hom sphereOneHomologyClass = (1 : ℤ) := by
  have hpt : hgrpOneSphereOneIsoPt.hom sphereOneHomologyClass = hptGenerator := by
    apply (AddCommGrpCat.mono_iff_injective beltAntidiag).1 inferInstance
    rw [← ConcreteCategory.comp_apply, hgrpOneSphereOneIsoPt_hom_comp_beltAntidiag,
      mvδ_sphereOneHomologyClass]
  change (hgrpZeroIso (TopCat.of PUnit.{1})).hom
    (hgrpOneSphereOneIsoPt.hom sphereOneHomologyClass) = (1 : ℤ)
  rw [hpt, hgrpZeroIso_hptGenerator]

/-- The chain-level Mayer--Vietoris map kills the antidiagonal belt generator in homology. -/
theorem homologyMap_mvSC_f_beltAntidiag_generator :
    HomologicalComplex.homologyMap
      (mvSC (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)).f 0
        (beltAntidiag hptGenerator) = 0 := by
  apply (AddCommGrpCat.mono_iff_injective
    (mvSumIso (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0).hom).1
      (by infer_instance)
  rw [map_zero, ← ConcreteCategory.comp_apply,
    homologyMap_mvSC_f (X := TopCat.of (Sph 1))]
  change mvIota (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) 0
    (beltAntidiag hptGenerator) = 0
  rw [← ConcreteCategory.comp_apply, beltAntidiag_comp_mvIota]
  rfl

/-- The raw Mayer--Vietoris connecting morphism from the belt to the small cochains. -/
def sphereOneRawCohDelta :
    (homDual (Csing (TopCat.of belt1)) modTwoCoefficients).homology 0 ⟶
      (mvCohSC (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).X₁.homology 1 :=
  (mvCohSC_shortExact (X := TopCat.of (Sph 1))
    (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).δ 0 1 (mvCohRel 0)

/-- Small cochains compute degree-one cohomology of the circle. -/
def sphereOneSmallCohomologyIso :
    (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1 ≅
      (mvCohSC (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).X₁.homology 1 :=
  mvSmallCohomologyIso (X := TopCat.of (Sph 1))
    (sphLowerCap 0) (sphUpperCap 0) (ZMod 2) (sphCap_interior_union 0) 1

/-- The belt parity functional cannot factor through the two hemispheres. -/
theorem beltParity_not_factors_through_mvSC_f :
    ¬ ∃ y :
        (homDual
          (mvSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0)).X₂
          modTwoCoefficients).homology 0,
      beltParity =
        HomologicalComplex.homologyMap
            (mvSC (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)).f 0 ≫
          ev (mvSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0)).X₂ modTwoCoefficients 0 y := by
  rintro ⟨y, hfactor⟩
  have hvalue := ConcreteCategory.congr_hom hfactor (beltAntidiag hptGenerator)
  rw [beltParity_beltAntidiag_generator] at hvalue
  change (1 : ZMod 2) =
    (ev (mvSC (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0)).X₂ modTwoCoefficients 0 y)
        (HomologicalComplex.homologyMap
          (mvSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0)).f 0
              (beltAntidiag hptGenerator)) at hvalue
  rw [homologyMap_mvSC_f_beltAntidiag_generator, map_zero] at hvalue
  exact one_ne_zero hvalue

/-- The raw connecting image of the parity class is nonzero. -/
theorem sphereOneRawCohDelta_beltParityDual_ne_zero :
    sphereOneRawCohDelta beltParityDual ≠ 0 := by
  intro hzero
  apply beltParity_not_factors_through_mvSC_f
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    ((mvCohSC_shortExact (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).homology_exact₃ 0 1 (mvCohRel 0))
      beltParityDual hzero
  refine ⟨y, ?_⟩
  rw [← ev_beltParityDual, ← hy]
  exact ev_naturality_apply
    (K := (mvSC (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0)).X₁)
    (L := (mvSC (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0)).X₂)
    (G := modTwoCoefficients) (i := 0)
    (mvSC (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0)).f y

/-- The Mayer--Vietoris connecting image of the parity class. -/
def sphereOneModTwoDualClass :
    (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1 :=
  sphereOneSmallCohomologyIso.inv (sphereOneRawCohDelta beltParityDual)

/-- The connecting image of the equatorial parity class is nonzero. -/
theorem sphereOneModTwoDualClass_ne_zero :
    sphereOneModTwoDualClass ≠
      (0 : (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1) := by
  intro hzero
  apply sphereOneRawCohDelta_beltParityDual_ne_zero
  apply (AddCommGrpCat.mono_iff_injective sphereOneSmallCohomologyIso.inv).1
    (by infer_instance)
  rw [map_zero]
  exact hzero

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished circle cohomology class evaluates to one on the homology class with the
matching Mayer--Vietoris boundary. -/
@[simp]
theorem sphereOneModTwoDualClass_evaluation :
    ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1
      sphereOneModTwoDualClass sphereOneHomologyClass = (1 : ZMod 2) := by
  have h := mv_delta_adjoint
    (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)
    (sphCap_interior_union 0) 0 beltParityDual sphereOneHomologyClass
  rw [mvδ_sphereOneHomologyClass, ev_beltParityDual] at h
  change ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1
      sphereOneModTwoDualClass sphereOneHomologyClass =
    beltParity (beltAntidiag hptGenerator) at h
  exact h.trans beltParity_beltAntidiag_generator

set_option backward.isDefEq.respectTransparency false in
/-- The matching circle homology class is nonzero. -/
theorem sphereOneHomologyClass_ne_zero : sphereOneHomologyClass ≠ 0 := by
  intro hzero
  have h := sphereOneModTwoDualClass_evaluation
  rw [hzero, map_zero] at h
  exact one_ne_zero h.symm

/-- A canonical nonzero class in `H¹(S¹; 𝔽₂)`. -/
def sphereOneModTwoClass : Hsing 1 (TopCat.of (Sph 1)) (ZMod 2) :=
  (HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph 1)) 1).symm
    sphereOneModTwoDualClass

/-- The canonical degree-one mod-two class on the circle is nonzero. -/
theorem sphereOneModTwoClass_ne_zero : sphereOneModTwoClass ≠ 0 := by
  intro hzero
  apply sphereOneModTwoDualClass_ne_zero
  calc
    sphereOneModTwoDualClass =
        HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph 1)) 1
          sphereOneModTwoClass := by
      rw [sphereOneModTwoClass, AddEquiv.apply_symm_apply]
    _ = HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph 1)) 1 0 :=
      congrArg _ hzero
    _ = 0 := map_zero _

/-- Canonical nonzero top-degree mod-two cohomology classes on all positive-dimensional
spheres. -/
def sphereTopModTwoClass :
    (n : ℕ) → Hsing (n + 1) (TopCat.of (Sph (n + 1))) (ZMod 2)
  | 0 => sphereOneModTwoClass
  | n + 1 => hsingSphStepEquiv (ZMod 2) (n + 1) n (sphereTopModTwoClass n)

/-- Every distinguished top-degree mod-two sphere class is nonzero. -/
theorem sphereTopModTwoClass_ne_zero :
    ∀ n : ℕ, sphereTopModTwoClass n ≠ 0 := by
  intro n
  induction n with
  | zero => exact sphereOneModTwoClass_ne_zero
  | succ n ih =>
      intro hzero
      apply ih
      apply (hsingSphStepEquiv (ZMod 2) (n + 1) n).injective
      rw [map_zero]
      exact hzero

/-! ### Normalized top-dimensional evaluation pairings -/

/-- The distinguished top sphere class in the dual-complex model. -/
noncomputable def sphereTopModTwoDualClass (n : ℕ) :
    (homDual (Csing (TopCat.of (Sph (n + 1)))) modTwoCoefficients).homology (n + 1) :=
  HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph (n + 1))) (n + 1)
    (sphereTopModTwoClass n)

@[simp]
theorem sphereTopModTwoDualClass_zero :
    sphereTopModTwoDualClass 0 = sphereOneModTwoDualClass := by
  rw [sphereTopModTwoDualClass, sphereTopModTwoClass, sphereOneModTwoClass,
    AddEquiv.apply_symm_apply]

/-- Top-dimensional sphere homology classes normalized against the distinguished mod-two
cohomology classes. -/
noncomputable def sphereTopHomologyClass :
    (n : ℕ) → Hgrp (n + 1) (TopCat.of (Sph (n + 1)))
  | 0 => sphereOneHomologyClass
  | n + 1 => (sphStepIso (n + 1) n).inv (sphereTopHomologyClass n)

@[simp]
theorem sphereTopHomologyClass_zero :
    sphereTopHomologyClass 0 = sphereOneHomologyClass := rfl

@[simp]
theorem sphStepIso_sphereTopHomologyClass_succ (n : ℕ) :
    (sphStepIso (n + 1) n).hom (sphereTopHomologyClass (n + 1)) =
      sphereTopHomologyClass n := by
  rw [sphereTopHomologyClass, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The dual-complex representative of the distinguished class on the next sphere is the
Mayer--Vietoris suspension of its pullback to the equatorial belt. -/
theorem sphereTopModTwoDualClass_succ (n : ℕ) :
    sphereTopModTwoDualClass (n + 1) =
      (mvCohδIso_of_contractible
        (X := TopCat.of (Sph (n + 2)))
        (sphLowerCap (n + 1)) (sphUpperCap (n + 1)) (ZMod 2)
        (sphCap_interior_union (n + 1)) n).hom
      (HsingEquivDualHomology (ZMod 2) (TopCat.of (sphBelt (n + 1))) (n + 1)
        (hsingBeltEquiv (ZMod 2) (n + 1) (n + 1) (sphereTopModTwoClass n))) := by
  simp only [sphereTopModTwoDualClass, sphereTopModTwoClass,
    hsingSphStepEquiv, mvHsingδEquiv_of_contractible,
    AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    Iso.addCommGroupIsoToAddEquiv_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished top mod-two class on every positive-dimensional sphere evaluates to one
on the matching top homology class. -/
@[simp]
theorem sphereTopModTwoDualClass_evaluation :
    ∀ n : ℕ,
      ev (Csing (TopCat.of (Sph (n + 1)))) modTwoCoefficients (n + 1)
        (sphereTopModTwoDualClass n) (sphereTopHomologyClass n) = (1 : ZMod 2) := by
  intro n
  induction n with
  | zero =>
      rw [sphereTopModTwoDualClass_zero, sphereTopHomologyClass_zero,
        sphereOneModTwoDualClass_evaluation]
  | succ n ih =>
      let f : TopCat.of (sphBelt (n + 1)) ⟶ TopCat.of (Sph (n + 1)) :=
        TopCat.ofHom (sphBeltHomotopyEquiv (n + 1)).toFun
      let Φbelt := HsingEquivDualHomology (ZMod 2)
        (TopCat.of (sphBelt (n + 1))) (n + 1)
        (hsingBeltEquiv (ZMod 2) (n + 1) (n + 1) (sphereTopModTwoClass n))
      let zBelt := (mvδIso_of_contractible
        (X := TopCat.of (Sph (n + 2)))
        (sphLowerCap (n + 1)) (sphUpperCap (n + 1))
        (sphCap_interior_union (n + 1)) n).hom
        (sphereTopHomologyClass (n + 1))
      have hmv := mv_deltaIso_adjoint_of_contractible
        (X := TopCat.of (Sph (n + 2)))
        (sphLowerCap (n + 1)) (sphUpperCap (n + 1)) (ZMod 2)
        (sphCap_interior_union (n + 1)) n Φbelt
        (sphereTopHomologyClass (n + 1))
      have hbridge := HsingEquivDualHomology_naturality (R := ZMod 2)
        f (n + 1) (sphereTopModTwoClass n)
      have hnat := ev_naturality_apply
        (K := Csing (TopCat.of (sphBelt (n + 1))))
        (L := Csing (TopCat.of (Sph (n + 1))))
        (G := modTwoCoefficients) (i := n + 1)
        (CsingMap f) (sphereTopModTwoDualClass n)
      have hnat' := ConcreteCategory.congr_hom hnat zBelt
      have hz : HgrpMap (n + 1) f zBelt = sphereTopHomologyClass n := by
        change (sphStepIso (n + 1) n).hom (sphereTopHomologyClass (n + 1)) =
          sphereTopHomologyClass n
        exact sphStepIso_sphereTopHomologyClass_succ n
      dsimp only [Φbelt, f, hsingBeltEquiv,
        hsingLinearEquivOfHomotopyEquiv] at hbridge
      dsimp only [f, sphereTopModTwoDualClass] at hnat'
      rw [← hbridge] at hnat'
      change ev (Csing (TopCat.of (sphBelt (n + 1)))) modTwoCoefficients (n + 1)
          Φbelt zBelt =
        ev (Csing (TopCat.of (Sph (n + 1)))) modTwoCoefficients (n + 1)
          (sphereTopModTwoDualClass n) (HgrpMap (n + 1) f zBelt) at hnat'
      rw [hz, ih] at hnat'
      rw [sphereTopModTwoDualClass_succ]
      exact hmv.trans hnat'

set_option backward.isDefEq.respectTransparency false in
/-- The normalized top homology class is the positive integral generator under the canonical
isomorphism `Hₙ(Sⁿ) ≅ ℤ`. -/
@[simp]
theorem hgrpSphereSelfIsoZ_sphereTopHomologyClass :
    ∀ n : ℕ,
      (hgrpSphereSelfIsoZ n).hom (sphereTopHomologyClass n) = (1 : ℤ) := by
  intro n
  induction n with
  | zero => exact hgrpOneSphereOneIso_sphereOneHomologyClass
  | succ n ih =>
      change (hgrpSphereSelfIsoZ n).hom
        ((sphStepIso (n + 1) n).hom (sphereTopHomologyClass (n + 1))) = (1 : ℤ)
      rw [sphStepIso_sphereTopHomologyClass_succ, ih]

/-- The normalized top homology class is the inverse image of `1 : ℤ`. -/
theorem sphereTopHomologyClass_eq_generator (n : ℕ) :
    sphereTopHomologyClass n = (hgrpSphereSelfIsoZ n).inv (1 : ℤ) := by
  apply (AddCommGrpCat.mono_iff_injective (hgrpSphereSelfIsoZ n).hom).1 inferInstance
  rw [hgrpSphereSelfIsoZ_sphereTopHomologyClass,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Every matching top-dimensional sphere homology class is nonzero. -/
theorem sphereTopHomologyClass_ne_zero (n : ℕ) : sphereTopHomologyClass n ≠ 0 := by
  intro hzero
  have h := sphereTopModTwoDualClass_evaluation n
  rw [hzero, map_zero] at h
  exact one_ne_zero h.symm

/-- The distinguished nonzero class in `H³(S³; 𝔽₂)`. -/
abbrev sphereThreeModTwoClass : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2) :=
  sphereTopModTwoClass 2

/-- The distinguished degree-three sphere class in the dual-complex model. -/
noncomputable abbrev sphereThreeModTwoDualClass :
    (homDual (Csing (TopCat.of (Sph 3))) modTwoCoefficients).homology 3 :=
  sphereTopModTwoDualClass 2

/-- The top-dimensional homology class normalized against `sphereThreeModTwoDualClass`. -/
noncomputable abbrev sphereThreeHomologyClass : Hgrp 3 (TopCat.of (Sph 3)) :=
  sphereTopHomologyClass 2

@[simp]
theorem sphereThreeModTwoDualClass_evaluation :
    ev (Csing (TopCat.of (Sph 3))) modTwoCoefficients 3
      sphereThreeModTwoDualClass sphereThreeHomologyClass = (1 : ZMod 2) :=
  sphereTopModTwoDualClass_evaluation 2

/-- The distinguished degree-three class on the `3`-sphere is nonzero. -/
theorem sphereThreeModTwoClass_ne_zero : sphereThreeModTwoClass ≠ 0 :=
  sphereTopModTwoClass_ne_zero 2

/-! ### Classification of top-degree mod-two classes -/

/-- A mod-two functional on the circle belt that kills the antidiagonal generator factors
through the augmentation. -/
theorem beltFunctional_factors_augmentation
    (l : Hgrp 0 (TopCat.of belt1) ⟶ modTwoCoefficients)
    (hl : l (beltAntidiag hptGenerator) = 0) :
    ∃ k : Hpt ⟶ modTwoCoefficients,
      l = HgrpMap 0 (toPt (TopCat.of belt1)) ≫ k := by
  let k : Hpt ⟶ modTwoCoefficients :=
    biprod.inl ≫ beltOneSplitIso.hom ≫ l
  refine ⟨k, ?_⟩
  apply (cancel_epi beltOneSplitIso.hom).1
  rw [← Category.assoc, beltOneSplitIso_hom_comp]
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp [k]
  · have hgen :
        (biprod.inr ≫ beltOneSplitIso.hom ≫ l) hptGenerator =
          -(biprod.inl ≫ beltOneSplitIso.hom ≫ l) hptGenerator := by
      have hvalue := hl
      change ((biprod.lift (𝟙 Hpt) (𝟙 Hpt) ≫ beltOneSplitIso.hom ≫ l)
        hptGenerator) = 0 at hvalue
      rw [biprod.lift_eq, Preadditive.add_comp,
        _root_.AddCommGrpCat.hom_add_apply] at hvalue
      simp only [Category.id_comp] at hvalue
      exact eq_neg_of_add_eq_zero_right hvalue
    have hmorph :
        biprod.inr ≫ beltOneSplitIso.hom ≫ l =
          -(biprod.inl ≫ beltOneSplitIso.hom ≫ l) := by
      apply (cancel_epi (hgrpZeroIso (TopCat.of PUnit.{1})).inv).1
      apply intHom_ext
      change (biprod.inr ≫ beltOneSplitIso.hom ≫ l) hptGenerator =
        -((biprod.inl ≫ beltOneSplitIso.hom ≫ l) hptGenerator)
      exact hgen
    simpa [k] using hmorph

set_option backward.isDefEq.respectTransparency false in
/-- A degree-zero belt class whose functional kills the antidiagonal generator has zero
Mayer--Vietoris connecting image. -/
theorem sphereOneRawCohDelta_eq_zero_of_evaluation
    (Φ : (homDual (Csing (TopCat.of belt1)) modTwoCoefficients).homology 0)
    (hΦ : ev (Csing (TopCat.of belt1)) modTwoCoefficients 0 Φ
      (beltAntidiag hptGenerator) = 0) :
    sphereOneRawCohDelta Φ = 0 := by
  let l : Hgrp 0 (TopCat.of belt1) ⟶ modTwoCoefficients :=
    ev (Csing (TopCat.of belt1)) modTwoCoefficients 0 Φ
  obtain ⟨k, hk⟩ := beltFunctional_factors_augmentation l hΦ
  let q : (mvSC (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0)).X₂.homology 0 ⟶ modTwoCoefficients :=
    (mvSumIso (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) 0).hom ≫
      biprod.fst ≫
        (hgrpZeroToPtIso (TopCat.of (sphLowerCap 0))).hom ≫ k
  have hq :
      HomologicalComplex.homologyMap
          (mvSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0)).f 0 ≫ q = l := by
    dsimp only [q]
    rw [← Category.assoc, homologyMap_mvSC_f]
    rw [mvIota_zero_factor (X := TopCat.of (Sph 1))]
    rw [hk]
    simp only [Category.assoc, biprod.lift_fst_assoc, Iso.inv_hom_id_assoc]
  obtain ⟨y, hy⟩ :=
    (ev_zero_bijective
      (mvSC (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0)).X₂ modTwoCoefficients).2 q
  let Φraw :
      (homDual
        (mvSC (X := TopCat.of (Sph 1))
          (sphLowerCap 0) (sphUpperCap 0)).X₁ modTwoCoefficients).homology 0 := Φ
  have hgyRaw :
      HomologicalComplex.homologyMap
        (homDualMap
          (mvSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0)).f modTwoCoefficients) 0 y = Φraw := by
    apply (ev_zero_bijective
      (mvSC (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0)).X₁ modTwoCoefficients).1
    rw [ev_naturality_apply, hy, hq]
    rfl
  have hgy :
      HomologicalComplex.homologyMap
          (mvCohSC (X := TopCat.of (Sph 1))
            (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).g 0 y = Φ := by
    exact hgyRaw
  rw [← hgy]
  change ((mvCohSC_shortExact (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).δ 0 1 (mvCohRel 0))
      (HomologicalComplex.homologyMap
        (mvCohSC (X := TopCat.of (Sph 1))
          (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).g 0 y) = 0
  rw [← ConcreteCategory.comp_apply,
    (mvCohSC_shortExact (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).comp_δ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on the normalized homology generator detects the zero degree-one dual
cohomology class of the circle. -/
theorem sphereOneDualClass_eq_zero_of_evaluation
    (Ψ : (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1)
    (hΨ : ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1 Ψ
      sphereOneHomologyClass = 0) :
    Ψ = 0 := by
  have hzero : IsZero
      ((mvCohSC (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).X₂.homology 1) :=
    isZero_mvCohSC_X₂_homology_of_contractible
      (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) (ZMod 2) 1
      (by omega)
  haveI : Epi sphereOneRawCohDelta :=
    ((mvCohSC_shortExact (X := TopCat.of (Sph 1))
      (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)).homology_exact₁
        0 1 (mvCohRel 0)).epi_f (hzero.eq_of_tgt _ _)
  obtain ⟨Φ, hΦ⟩ :=
    (AddCommGrpCat.epi_iff_surjective sphereOneRawCohDelta).1 inferInstance
      (sphereOneSmallCohomologyIso.hom Ψ)
  have hambient :
      mvCohδ (X := TopCat.of (Sph 1))
        (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)
        (sphCap_interior_union 0) 0 Φ = Ψ := by
    change sphereOneSmallCohomologyIso.inv (sphereOneRawCohDelta Φ) = Ψ
    rw [hΦ, ← ConcreteCategory.comp_apply,
      Iso.hom_inv_id, ConcreteCategory.id_apply]
  have hbelt :
      ev (Csing (TopCat.of belt1)) modTwoCoefficients 0 Φ
        (beltAntidiag hptGenerator) = 0 := by
    have h := mv_delta_adjoint
      (X := TopCat.of (Sph 1)) (sphLowerCap 0) (sphUpperCap 0) (ZMod 2)
      (sphCap_interior_union 0) 0 Φ sphereOneHomologyClass
    rw [hambient, hΨ, mvδ_sphereOneHomologyClass] at h
    exact h.symm
  have hraw := sphereOneRawCohDelta_eq_zero_of_evaluation Φ hbelt
  have hsmall : sphereOneSmallCohomologyIso.hom Ψ = 0 :=
    hΦ.symm.trans hraw
  have h := congrArg (fun z ↦ sphereOneSmallCohomologyIso.inv z) hsmall
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply, map_zero] at h
  exact h

/-- Evaluation on the normalized circle homology class is injective in degree one. -/
theorem sphereOneDualEvaluation_injective :
    Function.Injective (fun Ψ :
      (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1 ↦
        ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1 Ψ
          sphereOneHomologyClass) := by
  intro Φ Ψ hΦΨ
  apply sub_eq_zero.mp
  apply sphereOneDualClass_eq_zero_of_evaluation
  rw [map_sub]
  change ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1 Φ
      sphereOneHomologyClass -
    ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1 Ψ
      sphereOneHomologyClass = 0
  exact sub_eq_zero.mpr hΦΨ

/-- Evaluation on the normalized circle generator as an additive homomorphism. -/
def sphereOneDualEvaluationHom :
    (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1 →+
      ZMod 2 where
  toFun Ψ := ev (Csing (TopCat.of (Sph 1))) modTwoCoefficients 1 Ψ
    sphereOneHomologyClass
  map_zero' := by rw [map_zero]; rfl
  map_add' Φ Ψ := by rw [map_add]; rfl

/-- Circle evaluation is onto mod-two coefficients. -/
theorem sphereOneDualEvaluationHom_surjective :
    Function.Surjective sphereOneDualEvaluationHom := by
  intro a
  fin_cases a
  · exact ⟨0, map_zero sphereOneDualEvaluationHom⟩
  · exact ⟨sphereOneModTwoDualClass,
      sphereOneModTwoDualClass_evaluation⟩

/-- Degree-one mod-two cohomology of the circle is canonically `𝔽₂`, normalized by
evaluation on `sphereOneHomologyClass`. -/
noncomputable def sphereOneDualCohomologyEquivModTwo :
    (homDual (Csing (TopCat.of (Sph 1))) modTwoCoefficients).homology 1 ≃+
      ZMod 2 :=
  AddEquiv.ofBijective sphereOneDualEvaluationHom
    ⟨sphereOneDualEvaluation_injective, sphereOneDualEvaluationHom_surjective⟩

/-- The same normalized computation in the concrete singular-cohomology model. -/
noncomputable def sphereOneCohomologyEquivModTwo :
    Hsing 1 (TopCat.of (Sph 1)) (ZMod 2) ≃+ ZMod 2 :=
  (HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph 1)) 1).trans
    sphereOneDualCohomologyEquivModTwo

/-- Top-degree mod-two cohomology of every positive-dimensional sphere is `𝔽₂`. -/
noncomputable def sphereTopCohomologyEquivModTwo :
    (n : ℕ) → Hsing (n + 1) (TopCat.of (Sph (n + 1))) (ZMod 2) ≃+ ZMod 2
  | 0 => sphereOneCohomologyEquivModTwo
  | n + 1 =>
      (hsingSphStepEquiv (ZMod 2) (n + 1) n).symm.trans
        (sphereTopCohomologyEquivModTwo n)

/-- The distinguished top sphere class is the unit under the normalized computation. -/
@[simp]
theorem sphereTopCohomologyEquivModTwo_top :
    ∀ n : ℕ,
      sphereTopCohomologyEquivModTwo n (sphereTopModTwoClass n) = 1 := by
  intro n
  induction n with
  | zero =>
      change sphereOneDualEvaluationHom
        (HsingEquivDualHomology (ZMod 2) (TopCat.of (Sph 1)) 1
          sphereOneModTwoClass) = 1
      rw [sphereOneModTwoClass, AddEquiv.apply_symm_apply]
      exact sphereOneModTwoDualClass_evaluation
  | succ n ih =>
      change sphereTopCohomologyEquivModTwo n
        ((hsingSphStepEquiv (ZMod 2) (n + 1) n).symm
          (hsingSphStepEquiv (ZMod 2) (n + 1) n
            (sphereTopModTwoClass n))) = 1
      rw [AddEquiv.symm_apply_apply, ih]

/-- Every top-degree mod-two sphere class is either zero or the distinguished unit class. -/
theorem sphereTopClass_eq_zero_or_eq_top (n : ℕ)
    (x : Hsing (n + 1) (TopCat.of (Sph (n + 1))) (ZMod 2)) :
    x = 0 ∨ x = sphereTopModTwoClass n := by
  have hx : sphereTopCohomologyEquivModTwo n x = 0 ∨
      sphereTopCohomologyEquivModTwo n x = 1 := by
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact hcases _
  rcases hx with hx | hx
  · left
    apply (sphereTopCohomologyEquivModTwo n).injective
    rw [map_zero]
    exact hx
  · right
    apply (sphereTopCohomologyEquivModTwo n).injective
    rw [sphereTopCohomologyEquivModTwo_top]
    exact hx

/-- Every class in the dual-complex model of top sphere cohomology is zero or the normalized
top class. -/
theorem sphereTopDualClass_eq_zero_or_eq_top (n : ℕ)
    (Φ : (homDual (Csing (TopCat.of (Sph (n + 1)))) modTwoCoefficients).homology
      (n + 1)) :
    Φ = 0 ∨ Φ = sphereTopModTwoDualClass n := by
  rcases sphereTopClass_eq_zero_or_eq_top n
      ((HsingEquivDualHomology (ZMod 2)
        (TopCat.of (Sph (n + 1))) (n + 1)).symm Φ) with hzero | htop
  · left
    have h := congrArg
      (HsingEquivDualHomology (ZMod 2)
        (TopCat.of (Sph (n + 1))) (n + 1)) hzero
    rw [AddEquiv.apply_symm_apply, map_zero] at h
    exact h
  · right
    have h := congrArg
      (HsingEquivDualHomology (ZMod 2)
        (TopCat.of (Sph (n + 1))) (n + 1)) htop
    rw [AddEquiv.apply_symm_apply] at h
    exact h

end Submission
