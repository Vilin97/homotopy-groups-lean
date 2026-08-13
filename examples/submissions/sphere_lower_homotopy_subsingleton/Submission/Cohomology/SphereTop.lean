/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Sphere
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
* `Submission.sphereTopModTwoClass_ne_zero` -- the top mod-two cohomology of every positive
  sphere is nonzero;
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

/-- The distinguished nonzero class in `H³(S³; 𝔽₂)`. -/
abbrev sphereThreeModTwoClass : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2) :=
  sphereTopModTwoClass 2

/-- The distinguished degree-three class on the `3`-sphere is nonzero. -/
theorem sphereThreeModTwoClass_ne_zero : sphereThreeModTwoClass ≠ 0 :=
  sphereTopModTwoClass_ne_zero 2

end Submission
