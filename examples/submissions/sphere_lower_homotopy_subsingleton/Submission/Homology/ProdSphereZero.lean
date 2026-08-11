/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.SphereZeroSplit
import Submission.Homology.WangPathFibration

/-!
# The product formula for `S⁰`: the base case

`S⁰` is two points, so `F × S⁰` is the disjoint union of the two clopen slices `F × {p_b}`, each
homeomorphic to `F` by the projection.  Mayer–Vietoris for a clopen partition therefore gives
`Hₙ(F × S⁰) ≅ Hₙ(F) ⊞ Hₙ(F)` in every degree.

The point of the file is not the abstract isomorphism but the **compatibility with the
projection**: the splitting is arranged so that its first component is literally
`HgrpMap n (prodFstMap F (Sph 0))`, which is what `Submission.ProdSphereSplitting` demands and what
the Wang sequence consumes.  Concretely, if `j_b : F ≅ F × {p_b}` are the two slices, the
isomorphism used is

`(u, v) ↦ (j₀)_* (u + v) - (j₁)_* v`,

whose composite with the projection is `(u, v) ↦ (u + v) - v = u`.

## Main definitions

* `Submission.prodSectMap` — the section `F ⟶ F × S`, `f ↦ (f, s)`, which splits the projection.
* `Submission.prodSphZeroSet` — the two clopen slices of `F × S⁰`.
* `Submission.prodSphereSplittingZero` — the `d = 0` case of `Submission.ProdSphereSplitting`.

## Main results

* `Submission.isIso_mvKappa_of_isEmpty_inter` — additivity of singular homology over a clopen
  partition, in every degree (the degree `0` case was already in
  `Submission/Homology/RightExact.lean`).
* `Submission.prodSphZeroSplitIso_hom_comp_fst` — the projection compatibility.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-! ### Additivity of homology over a clopen partition, in every degree -/

/-- **Additivity of singular homology over a clopen partition.**  If `A` and `B` are disjoint and
their interiors cover `X`, then `Hₙ(A) ⊞ Hₙ(B) ⟶ Hₙ(X)` is an isomorphism in every degree. -/
theorem isIso_mvKappa_of_isEmpty_inter {X : TopCat.{0}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) [IsEmpty (A ∩ B : Set X)] (n : ℕ) :
    IsIso (mvKappa A B n) := by
  cases n with
  | zero => exact isIso_mvKappa_zero_of_isEmpty_inter A B h
  | succ m =>
    have hmono : Mono (mvKappa A B (m + 1)) :=
      (mayerVietoris_exact_iota_kappa A B h (m + 1)).mono_g
        ((isZero_Hgrp_of_isEmpty (TopCat.of (A ∩ B : Set X)) (m + 1)).eq_zero_of_src _)
    have hepi : Epi (mvKappa A B (m + 1)) :=
      (mayerVietoris_exact_kappa_δ A B h m).epi_f
        ((isZero_Hgrp_of_isEmpty (TopCat.of (A ∩ B : Set X)) m).eq_zero_of_tgt _)
    exact isIso_of_mono_of_epi _

/-- `Hₙ(A) ⊞ Hₙ(B) ≅ Hₙ(X)` for a clopen partition `X = A ⊔ B`. -/
def mvKappaIso {X : TopCat.{0}} (A B : Set X) (h : interior A ∪ interior B = Set.univ)
    [IsEmpty (A ∩ B : Set X)] (n : ℕ) : mvSum A B n ≅ Hgrp n X :=
  haveI := isIso_mvKappa_of_isEmpty_inter A B h n
  asIso (mvKappa A B n)

@[simp]
theorem mvKappaIso_hom {X : TopCat.{0}} (A B : Set X) (h : interior A ∪ interior B = Set.univ)
    [IsEmpty (A ∩ B : Set X)] (n : ℕ) : (mvKappaIso A B h n).hom = mvKappa A B n := rfl

/-! ### The shear automorphism of a biproduct -/

/-- The automorphism `(u, v) ↦ (u + v, v)` of a biproduct. -/
def shearIso {C : Type*} [Category* C] [Preadditive C] (Y : C) [HasBinaryBiproduct Y Y] :
    Y ⊞ Y ≅ Y ⊞ Y where
  hom := biprod.lift (biprod.desc (𝟙 Y) (𝟙 Y)) biprod.snd
  inv := biprod.lift (biprod.desc (𝟙 Y) (-𝟙 Y)) biprod.snd
  hom_inv_id := by apply biprod.hom_ext <;> simp [biprod.desc_eq]
  inv_hom_id := by apply biprod.hom_ext <;> simp [biprod.desc_eq]

/-! ### The section of the projection -/

variable (F : TopCat.{0})

/-- The section `F ⟶ F × S` of the projection at a point `s : S`. -/
def prodSectMap {S : Type} [TopologicalSpace S] (s : S) : F ⟶ TopCat.of (↥F × S) :=
  TopCat.ofHom ⟨fun f => (f, s), by fun_prop⟩

@[reassoc (attr := simp)]
theorem prodSectMap_comp_prodFstMap {S : Type} [TopologicalSpace S] (s : S) :
    prodSectMap F s ≫ prodFstMap F S = 𝟙 F := rfl

/-! ### The two slices of `F × S⁰` -/

/-- `F × S⁰` as an object of `TopCat`. -/
abbrev prodSphZero : TopCat.{0} := TopCat.of (↥F × Sph 0)

/-- The slice `F × {p_b}` of `F × S⁰`. -/
def prodSphZeroSet (b : Bool) : Set ↥(prodSphZero F) := Prod.snd ⁻¹' sphZeroPtSet b

theorem isOpen_prodSphZeroSet (b : Bool) : IsOpen (prodSphZeroSet F b) :=
  (isOpen_discrete _).preimage continuous_snd

theorem prodSphZeroSet_interior_union :
    interior (prodSphZeroSet F false) ∪ interior (prodSphZeroSet F true) = Set.univ := by
  rw [(isOpen_prodSphZeroSet F false).interior_eq, (isOpen_prodSphZeroSet F true).interior_eq]
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨b, hb⟩ := sphZeroOfBool_surjective z.2
  match b, hb with
  | false, hb => exact Or.inl hb.symm
  | true, hb => exact Or.inr hb.symm

instance instIsEmptyProdSphZeroInter :
    IsEmpty ((prodSphZeroSet F false ∩ prodSphZeroSet F true : Set ↥(prodSphZero F))) := by
  refine ⟨fun z => ?_⟩
  have h0 : (z : ↥(prodSphZero F)).2 = sphZeroOfBool false := z.2.1
  have h1 : (z : ↥(prodSphZero F)).2 = sphZeroOfBool true := z.2.2
  exact Bool.noConfusion (sphZeroOfBool_injective (h0.symm.trans h1))

/-- The projection from a slice of `F × S⁰` down to `F`. -/
def prodSphZeroProj (b : Bool) : TopCat.of ↥(prodSphZeroSet F b) ⟶ F :=
  subIncl (prodSphZeroSet F b) ≫ prodFstMap F (Sph 0)

/-- The inverse of the projection from a slice of `F × S⁰`. -/
def prodSphZeroSect (b : Bool) : F ⟶ TopCat.of ↥(prodSphZeroSet F b) :=
  TopCat.ofHom ⟨fun f => ⟨(f, sphZeroOfBool b), rfl⟩, Continuous.subtype_mk (by fun_prop) _⟩

theorem prodSphZeroProj_comp_sect (b : Bool) :
    prodSphZeroProj F b ≫ prodSphZeroSect F b = 𝟙 _ := by
  refine TopCat.hom_ext (ContinuousMap.ext fun z => Subtype.ext ?_)
  obtain ⟨⟨f, s⟩, hs⟩ := z
  obtain rfl : s = sphZeroOfBool b := hs
  rfl

theorem prodSphZeroSect_comp_proj (b : Bool) :
    prodSphZeroSect F b ≫ prodSphZeroProj F b = 𝟙 F :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

/-- Each slice `F × {p_b}` is isomorphic to `F`, via the projection. -/
def prodSphZeroIso (b : Bool) : TopCat.of ↥(prodSphZeroSet F b) ≅ F where
  hom := prodSphZeroProj F b
  inv := prodSphZeroSect F b
  hom_inv_id := prodSphZeroProj_comp_sect F b
  inv_hom_id := prodSphZeroSect_comp_proj F b

@[simp]
theorem prodSphZeroIso_hom (b : Bool) : (prodSphZeroIso F b).hom = prodSphZeroProj F b := rfl

/-- The isomorphism on homology induced by the projection from a slice. -/
def hgrpSliceIso (b : Bool) (n : ℕ) :
    Hgrp n (TopCat.of ↥(prodSphZeroSet F b)) ≅ Hgrp n F :=
  hgrpIsoOfIso n (prodSphZeroIso F b)

theorem hgrpSliceIso_hom (b : Bool) (n : ℕ) :
    (hgrpSliceIso F b n).hom = HgrpMap n (prodSphZeroProj F b) := rfl

/-! ### The splitting -/

/-- The isomorphism `Hₙ(F) ⊞ Hₙ(F) ≅ Hₙ(F × S⁰)` used for the base case of the product formula. -/
def prodSphZeroSplitIso (n : ℕ) : Hgrp n F ⊞ Hgrp n F ≅ Hgrp n (prodSphZero F) :=
  shearIso (Hgrp n F) ≪≫
    biprod.mapIso (hgrpSliceIso F false n).symm (hgrpSliceIso F true n).symm ≪≫
    mvKappaIso (prodSphZeroSet F false) (prodSphZeroSet F true)
      (prodSphZeroSet_interior_union F) n

theorem mvKappa_prodSphZero_comp_fst (n : ℕ) :
    mvKappa (prodSphZeroSet F false) (prodSphZeroSet F true) n ≫
        HgrpMap n (prodFstMap F (Sph 0)) =
      biprod.desc (hgrpSliceIso F false n).hom (-(hgrpSliceIso F true n).hom) := by
  rw [mvKappa]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc_assoc, biprod.inl_desc, ← HgrpMap_comp]
    rfl
  · rw [biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.neg_comp, ← HgrpMap_comp]
    rfl

/-- **The projection compatibility.**  Composing the splitting with the map induced by the
projection `F × S⁰ ⟶ F` gives the first projection of the biproduct. -/
theorem prodSphZeroSplitIso_hom_comp_fst (n : ℕ) :
    (prodSphZeroSplitIso F n).hom ≫ HgrpMap n (prodFstMap F (Sph 0)) = biprod.fst := by
  have hmd : biprod.map (hgrpSliceIso F false n).symm.hom (hgrpSliceIso F true n).symm.hom ≫
      biprod.desc (hgrpSliceIso F false n).hom (-(hgrpSliceIso F true n).hom) =
      biprod.desc (𝟙 (Hgrp n F)) (-(𝟙 (Hgrp n F))) :=
    biprod.hom_ext' _ _ (by simp) (by simp)
  rw [prodSphZeroSplitIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    mvKappaIso_hom, mvKappa_prodSphZero_comp_fst, biprod.mapIso_hom, hmd, shearIso]
  simp [biprod.desc_eq]

/-- **The base case of the product formula:** `Hₙ(F × S⁰) ≅ Hₙ(F) ⊞ Hₙ(F)`, with first component
the map induced by the projection. -/
def prodSphereSplittingZero : ProdSphereSplitting F 0 where
  iso n := (prodSphZeroSplitIso F n).symm
  iso_fst n := by
    show (prodSphZeroSplitIso F n).symm.hom ≫ biprod.fst = HgrpMap n (prodFstMap F (Sph 0))
    rw [Iso.symm_hom, ← prodSphZeroSplitIso_hom_comp_fst F n, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]

end Submission
