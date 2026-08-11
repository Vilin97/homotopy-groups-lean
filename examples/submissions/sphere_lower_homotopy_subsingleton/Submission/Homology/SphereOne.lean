/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.SphereZeroSplit
import Submission.Homology.Sphere
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# `H₁(S¹) ≅ ℤ`

Mayer–Vietoris for the two enlarged hemispheres of `S¹` makes the connecting map
`∂ : H₁(S¹) ⟶ H₀(belt)` a monomorphism (the hemispheres are contractible), and exact at
`H₀(belt)`.  So `H₁(S¹)` is a kernel of `H₀(belt) ⟶ H₀(A) ⊞ H₀(B)`.

Because `A` and `B` are path-connected, that map has the same kernel as the augmentation
`H₀(belt) ⟶ H₀(pt)` (this uses `isIso_HgrpMap_zero` and the fact that every map factors through
the unique map to a point — no naturality of Mathlib's augmentation is needed).  The belt of `S¹`
is homotopy equivalent to `S⁰`, whose `H₀` splits as `H₀(pt) ⊞ H₀(pt)` by
`hgrpZeroSphZeroIso`, and under that splitting the augmentation becomes
`biprod.desc 𝟙 (-𝟙)`, whose kernel is the antidiagonal copy of `H₀(pt) ≅ ℤ`.

## Main results

* `hgrpOneSphereOneIso : Hgrp 1 (TopCat.of (Sph 1)) ≅ AddCommGrpCat.of ℤ`;
* `hgrpSphereSelfIsoZ`, `hredSphereSelfIsoZ` — the top (reduced) homology of every sphere is `ℤ`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-! ### Generalities -/

/-- Any two maps into the one-point space agree. -/
theorem toPt_eq {Y : TopCat.{0}} (f g : Y ⟶ TopCat.of PUnit.{1}) : f = g := by
  ext

@[reassoc]
theorem comp_toPt {Y Z : TopCat.{0}} (f : Y ⟶ Z) : f ≫ toPt Z = toPt Y := toPt_eq _ _

/-- Postcomposing the second map of an exact short complex of abelian groups with a monomorphism
preserves exactness. -/
theorem exact_comp_mono {S : ShortComplex AddCommGrpCat.{0}} (hS : S.Exact)
    {T : AddCommGrpCat.{0}} (m : S.X₃ ⟶ T) [Mono m] :
    (ShortComplex.mk S.f (S.g ≫ m) (by rw [← Category.assoc, S.zero, zero_comp])).Exact := by
  have hinj : Function.Injective m := (AddCommGrpCat.mono_iff_injective m).1 inferInstance
  rw [ShortComplex.ab_exact_iff] at hS ⊢
  intro x hx
  refine hS x (hinj ?_)
  rw [map_zero]
  simpa only [ConcreteCategory.comp_apply] using hx

/-- The antidiagonal `P ⟶ P ⊞ P` splits off the difference map `P ⊞ P ⟶ P`. -/
def antidiagSplitting (P : AddCommGrpCat.{0}) :
    ShortComplex.Splitting (ShortComplex.mk (biprod.lift (𝟙 P) (𝟙 P))
      (biprod.desc (𝟙 P) (-𝟙 P)) (by simp)) where
  r := biprod.fst
  s := -biprod.inr
  f_r := by simp
  s_g := by simp
  id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-! ### The Mayer–Vietoris map in degree zero as an augmentation -/

/-- For a path-connected space, `H₀(Y) ⟶ H₀(pt)` is an isomorphism. -/
def hgrpZeroToPtIso (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Hgrp 0 Y ≅ Hgrp 0 (TopCat.of PUnit.{1}) :=
  haveI := isIso_HgrpMap_zero (toPt Y)
  asIso (HgrpMap 0 (toPt Y))

lemma hgrpZeroToPtIso_hom (Y : TopCat.{0}) [PathConnectedSpace Y] :
    (hgrpZeroToPtIso Y).hom = HgrpMap 0 (toPt Y) := rfl

variable {X : TopCat.{0}} (A B : Set X)

/-- For path-connected `A` and `B`, the Mayer–Vietoris map `H₀(A ∩ B) ⟶ H₀(A) ⊞ H₀(B)` is the
augmentation `H₀(A ∩ B) ⟶ H₀(pt)` followed by a monomorphism. -/
theorem mvIota_zero_factor [PathConnectedSpace A] [PathConnectedSpace B] :
    mvIota A B 0 = HgrpMap 0 (toPt (TopCat.of (A ∩ B : Set X))) ≫
      biprod.lift (hgrpZeroToPtIso (TopCat.of A)).inv
        (hgrpZeroToPtIso (TopCat.of B)).inv := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.lift_fst]
    simp only [mvIota, biprod.lift_fst]
    rw [Iso.eq_comp_inv, hgrpZeroToPtIso_hom, ← HgrpMap_comp, comp_toPt]
  · rw [Category.assoc, biprod.lift_snd]
    simp only [mvIota, biprod.lift_snd]
    rw [Iso.eq_comp_inv, hgrpZeroToPtIso_hom, ← HgrpMap_comp, comp_toPt]

theorem mono_mvIota_zero_factor [PathConnectedSpace A] [PathConnectedSpace B] :
    Mono (biprod.lift (hgrpZeroToPtIso (TopCat.of A)).inv
      (hgrpZeroToPtIso (TopCat.of B)).inv) :=
  mono_of_mono_fac (biprod.lift_fst (hgrpZeroToPtIso (TopCat.of A)).inv
    (hgrpZeroToPtIso (TopCat.of B)).inv)

/-! ### `H₁(S¹) ≅ ℤ` -/

/-- `H₀` of the one-point space. -/
abbrev Hpt : AddCommGrpCat.{0} := Hgrp 0 (TopCat.of PUnit.{1})

/-- The belt of `S¹`, as the intersection of the two enlarged hemispheres. -/
abbrev belt1 : Set (Sph 1) := sphLowerCap 0 ∩ sphUpperCap 0

/-- The homotopy equivalence from the belt of `S¹` to `S⁰`. -/
def beltToSphZero : TopCat.of belt1 ⟶ TopCat.of (Sph 0) :=
  TopCat.ofHom (sphBeltHomotopyEquiv 0).toFun

lemma hgrpBeltIso_zero_hom :
    (hgrpBeltIso 0 0).hom = HgrpMap 0 beltToSphZero := rfl

lemma hgrpZeroSphZeroIso_hom :
    hgrpZeroSphZeroIso.hom =
      mvKappa (X := TopCat.of (Sph 0)) (sphZeroPtSet false) (sphZeroPtSet true) 0 := rfl

/-- `H₀` of the belt of `S¹` splits as two copies of `H₀(pt)`. -/
def beltOneSplitIso : (Hpt ⊞ Hpt) ≅ Hgrp 0 (TopCat.of belt1) :=
  biprod.mapIso (hgrpZeroToPtIso (TopCat.of (sphZeroPtSet false))).symm
      (hgrpZeroToPtIso (TopCat.of (sphZeroPtSet true))).symm ≪≫
    hgrpZeroSphZeroIso ≪≫ (hgrpBeltIso 0 0).symm

/-- Under the splitting, the augmentation of the belt is the difference map. -/
theorem beltOneSplitIso_hom_comp :
    beltOneSplitIso.hom ≫ HgrpMap 0 (toPt (TopCat.of belt1)) =
      biprod.desc (𝟙 Hpt) (-𝟙 Hpt) := by
  have hw : HgrpMap 0 (toPt (TopCat.of belt1)) =
      HgrpMap 0 beltToSphZero ≫ HgrpMap 0 (toPt (TopCat.of (Sph 0))) := by
    rw [← HgrpMap_comp, comp_toPt]
  have hkey : hgrpZeroSphZeroIso.hom ≫ HgrpMap 0 (toPt (TopCat.of (Sph 0))) =
      biprod.desc (hgrpZeroToPtIso (TopCat.of (sphZeroPtSet false))).hom
        (-(hgrpZeroToPtIso (TopCat.of (sphZeroPtSet true))).hom) := by
    rw [hgrpZeroSphZeroIso_hom]
    simp only [mvKappa]
    rw [biprod_desc_comp]
    congr 1
    · rw [hgrpZeroToPtIso_hom, ← HgrpMap_comp, comp_toPt]
    · rw [Preadditive.neg_comp, hgrpZeroToPtIso_hom, ← HgrpMap_comp, comp_toPt]
  rw [hw]
  simp only [beltOneSplitIso, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Category.assoc,
    ← hgrpBeltIso_zero_hom, Iso.inv_hom_id_assoc]
  rw [hkey]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc, Iso.inv_hom_id]
  · rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc, Preadditive.comp_neg,
      Iso.inv_hom_id]

/-- Exactness is preserved when the second map is replaced by an equal composite with a mono. -/
theorem exact_of_eq_comp_mono {S : ShortComplex AddCommGrpCat.{0}} (hS : S.Exact)
    {T : AddCommGrpCat.{0}} (g' : S.X₂ ⟶ T) (m : S.X₃ ⟶ T) [Mono m] (hg : g' = S.g ≫ m)
    (w : S.f ≫ g' = 0) : (ShortComplex.mk S.f g' w).Exact := by
  subst hg
  exact exact_comp_mono hS m

/-- The antidiagonal `H₀(pt) ⟶ H₀(belt)`. -/
def beltAntidiag : Hpt ⟶ Hgrp 0 (TopCat.of belt1) :=
  biprod.lift (𝟙 Hpt) (𝟙 Hpt) ≫ beltOneSplitIso.hom

instance mono_beltAntidiag : Mono beltAntidiag := by
  haveI : Mono (biprod.lift (𝟙 Hpt) (𝟙 Hpt)) :=
    mono_of_mono_fac (biprod.lift_fst (𝟙 Hpt) (𝟙 Hpt))
  exact mono_comp _ _

theorem beltAntidiag_comp_aug :
    beltAntidiag ≫ HgrpMap 0 (toPt (TopCat.of belt1)) = 0 := by
  rw [beltAntidiag, Category.assoc, beltOneSplitIso_hom_comp, biprod.lift_desc]
  simp

/-- **`H₁(S¹) ≅ H₀(pt)`.** -/
def hgrpOneSphereOneIsoPt : Hgrp 1 (TopCat.of (Sph 1)) ≅ Hpt := by
  have hcov : interior (sphLowerCap 0) ∪ interior (sphUpperCap 0) = Set.univ :=
    sphCap_interior_union 0
  let S1 : TopCat.{0} := TopCat.of (Sph 1)
  have hzA : IsZero (Hgrp 1 (TopCat.of (sphLowerCap 0))) :=
    isZero_Hgrp_of_contractible (X := TopCat.of (sphLowerCap 0)) 0
  have hzB : IsZero (Hgrp 1 (TopCat.of (sphUpperCap 0))) :=
    isZero_Hgrp_of_contractible (X := TopCat.of (sphUpperCap 0)) 0
  have hK : mvKappa (X := S1) (sphLowerCap 0) (sphUpperCap 0) 1 = 0 :=
    (isZero_mvSum (X := S1) (sphLowerCap 0) (sphUpperCap 0) 1 hzA hzB).eq_zero_of_src _
  haveI hmonoδ : Mono (mvδ (X := S1) (sphLowerCap 0) (sphUpperCap 0) hcov 0) :=
    (mayerVietoris_exact_kappa_δ (X := S1) (sphLowerCap 0) (sphUpperCap 0) hcov 0).mono_g hK
  haveI hmonom : Mono (biprod.lift (hgrpZeroToPtIso (TopCat.of (sphLowerCap 0))).inv
      (hgrpZeroToPtIso (TopCat.of (sphUpperCap 0))).inv) :=
    mono_mvIota_zero_factor (X := S1) (sphLowerCap 0) (sphUpperCap 0)
  have hex0 := (antidiagSplitting Hpt).exact
  have hSβ : (ShortComplex.mk beltAntidiag (HgrpMap 0 (toPt (TopCat.of belt1)))
      beltAntidiag_comp_aug).Exact := by
    refine ShortComplex.exact_of_iso ?_ hex0
    refine ShortComplex.isoMk (Iso.refl _) beltOneSplitIso (Iso.refl _) ?_ ?_
    · exact Category.id_comp beltAntidiag
    · exact beltOneSplitIso_hom_comp.trans (Category.comp_id _).symm
  have hSα := exact_of_eq_comp_mono hSβ
    (mvIota (X := S1) (sphLowerCap 0) (sphUpperCap 0) 0)
    (biprod.lift (hgrpZeroToPtIso (TopCat.of (sphLowerCap 0))).inv
      (hgrpZeroToPtIso (TopCat.of (sphUpperCap 0))).inv)
    (mvIota_zero_factor (X := S1) (sphLowerCap 0) (sphUpperCap 0))
    (by rw [mvIota_zero_factor (X := S1), ← Category.assoc,
      beltAntidiag_comp_aug, zero_comp])
  exact IsLimit.conePointUniqueUpToIso
    ((mayerVietoris_exact_δ_iota (X := S1) (sphLowerCap 0) (sphUpperCap 0) hcov 0).fIsKernel)
    hSα.fIsKernel

/-- **`H₁(S¹) ≅ ℤ`.** -/
def hgrpOneSphereOneIso : Hgrp 1 (TopCat.of (Sph 1)) ≅ AddCommGrpCat.of ℤ :=
  hgrpOneSphereOneIsoPt ≪≫ hgrpZeroIso (TopCat.of PUnit.{1})

/-- **`Hₙ(Sⁿ) ≅ ℤ` for `n ≥ 1`.** -/
def hgrpSphereSelfIsoZ (n : ℕ) :
    Hgrp (n + 1) (TopCat.of (Sph (n + 1))) ≅ AddCommGrpCat.of ℤ :=
  hgrpSphereSelfIso n ≪≫ hgrpOneSphereOneIso

/-- **`H̃ₙ(Sⁿ) ≅ ℤ` for `n ≥ 1`.** -/
def hredSphereSelfIsoZ (n : ℕ) (x : (TopCat.of (Sph (n + 1)) : TopCat.{0})) :
    Hred (n + 1) x ≅ AddCommGrpCat.of ℤ :=
  hredSphereSelfIso n x ≪≫ hgrpOneSphereOneIso

end Submission
