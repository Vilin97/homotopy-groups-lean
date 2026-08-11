/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.ProdSplitTools

/-!
# Setup for the inductive step of the product formula

The induction `d → d + 1` for `H_*(F × Sᵈ)` runs Mayer–Vietoris on the cover of `F × S^{d+1}` by
the two slices `F × D₋` and `F × D₊` over the enlarged hemispheres of
`Submission/Homotopy/ContractionData.lean`.  This file contains the geometry of that cover, with
everything phrased so that the comparison maps are literally `prodFstMap`:

* a slice `Prod.snd ⁻¹' D` of `F × Sᵐ` is canonically homeomorphic to `F × D`
  (`Submission.prodSliceIso`), compatibly with the projections on the nose
  (`Submission.prodSliceIso_hom_comp_fst`, which is `rfl`);
* hence for contractible `D` the projection `F × D ⟶ F` is a homology isomorphism
  (`Submission.isIso_HgrpMap_prodSlice_fst`) — this applies to both hemispheres, so the two maps
  out of the homology of the overlap really are the same projection;
* the two hemisphere slices cover, and their intersection is the belt slice;
* the belt slice is homotopy equivalent to `F × Sᵈ`, again compatibly with the projections
  (`Submission.prodBeltEquiv_fst`), which is what feeds the inductive hypothesis in.

**What is not here.**  The Mayer–Vietoris chase that identifies
`kernel (HgrpMap k (prodFstMap F (Sph (d+1))))` with
`kernel (HgrpMap (k-1) (prodFstMap F (Sph d)))` — and hence, with
`Submission.hgrpProdSplitIso`, produces `ProdSphereSplitting F (d+1)` and
`ProdSphereLowIso F (d+1)` — is **not** proved.  Nothing in this file is partial: every declaration
below is complete.

## Main definitions

* `Submission.prodSlice F D` — the slice `F × D` as a subset of `F × Sᵐ`.
* `Submission.prodSliceIso` — its canonical identification with `F × D`.
* `Submission.prodBeltEquiv` — the belt slice is `F × Sᵈ` up to homotopy.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable (F : TopCat.{0})

/-- `F × Sᵐ` as an object of `TopCat`. -/
abbrev prodSph (m : ℕ) : TopCat.{0} := TopCat.of (↥F × Sph m)

/-- The slice of `F × Sᵐ` lying over a subset `D` of the sphere. -/
def prodSlice {m : ℕ} (D : Set (Sph m)) : Set ↥(prodSph F m) := Prod.snd ⁻¹' D

theorem mem_prodSlice {m : ℕ} {D : Set (Sph m)} {z : ↥(prodSph F m)} :
    z ∈ prodSlice F D ↔ z.2 ∈ D := Iff.rfl

/-! ### A slice is a product -/

/-- A slice of `F × Sᵐ` is canonically homeomorphic to the product `F × D`. -/
def prodSliceHomeo {m : ℕ} (D : Set (Sph m)) : ↥(prodSlice F D) ≃ₜ (↥F × ↥D) where
  toFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · exact Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd)) _

/-- The canonical identification of a slice with a product, in `TopCat`. -/
def prodSliceIso {m : ℕ} (D : Set (Sph m)) :
    TopCat.of ↥(prodSlice F D) ≅ TopCat.of (↥F × ↥D) :=
  TopCat.isoOfHomeo (prodSliceHomeo F D)

/-- The identification of a slice with a product is compatible with the projections, on the
nose. -/
theorem prodSliceIso_hom_comp_fst {m : ℕ} (D : Set (Sph m)) :
    (prodSliceIso F D).hom ≫ prodFstMap F ↥D =
      subIncl (prodSlice F D) ≫ prodFstMap F (Sph m) := rfl

/-- For a contractible piece `D` of the sphere, the projection from the slice over `D` down to `F`
is an isomorphism on homology. -/
theorem isIso_HgrpMap_prodSlice_fst {m : ℕ} (D : Set (Sph m)) [ContractibleSpace ↥D] (k : ℕ) :
    IsIso (HgrpMap k (subIncl (prodSlice F D) ≫ prodFstMap F (Sph m))) := by
  rw [← prodSliceIso_hom_comp_fst, HgrpMap_comp]
  haveI : IsIso (HgrpMap k (prodSliceIso F D).hom) := (hgrpIsoOfIso k (prodSliceIso F D)).isIso_hom
  haveI : IsIso (HgrpMap k (prodFstMap F ↥D)) :=
    isIso_HgrpMap_prodFstMap_of_contractible F ↥D k
  infer_instance

/-! ### The two hemisphere slices cover, and meet in the belt slice -/

variable {d : ℕ}

theorem prodSlice_interior_union :
    interior (prodSlice F (sphLowerCap d)) ∪ interior (prodSlice F (sphUpperCap d)) =
      Set.univ := by
  have hsub : ∀ D : Set (Sph (d + 1)),
      Prod.snd ⁻¹' interior D ⊆ interior (prodSlice F D) := fun D =>
    interior_maximal (Set.preimage_mono interior_subset)
      (isOpen_interior.preimage continuous_snd)
  refine Set.eq_univ_of_forall fun z => ?_
  rcases Set.eq_univ_iff_forall.1 (interior_union_sphCaps (d := d)) z.2 with hz | hz
  · exact Or.inl (hsub _ hz)
  · exact Or.inr (hsub _ hz)

theorem prodSlice_inter :
    prodSlice F (sphLowerCap d) ∩ prodSlice F (sphUpperCap d) = prodSlice F (sphBelt d) := rfl

/-! ### The belt slice is `F × Sᵈ` up to homotopy -/

variable (d) in
/-- The belt of `S^{d+1}`, crossed with `F`, is homotopy equivalent to `F × Sᵈ`. -/
def prodBeltEquiv : ContinuousMap.HomotopyEquiv (↥F × ↥(sphBelt d)) (↥F × Sph d) :=
  (ContinuousMap.HomotopyEquiv.refl _).prodCongr (sphBeltHomotopyEquiv d)

/-- The belt identification is compatible with the projections, on the nose. -/
theorem prodBeltEquiv_fst :
    TopCat.ofHom (prodBeltEquiv F d).toFun ≫ prodFstMap F (Sph d) =
      prodFstMap F ↥(sphBelt d) :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

/-- The projection from the belt slice of `F × S^{d+1}` down to `F` factors through `F × Sᵈ`. -/
theorem prodBelt_fst_factor :
    (prodSliceIso F (sphBelt d)).hom ≫ TopCat.ofHom (prodBeltEquiv F d).toFun ≫
        prodFstMap F (Sph d) =
      subIncl (prodSlice F (sphBelt d)) ≫ prodFstMap F (Sph (d + 1)) := by
  rw [prodBeltEquiv_fst, prodSliceIso_hom_comp_fst]

/-- On homology, the belt slice and `F × Sᵈ` have the same projection to `Hₖ(F)`: an isomorphism
`Hₖ(F × belt) ≅ Hₖ(F × Sᵈ)` intertwining the two projections. -/
def hgrpProdBeltIso (k : ℕ) :
    Hgrp k (TopCat.of ↥(prodSlice F (sphBelt d))) ≅ Hgrp k (TopCat.of (↥F × Sph d)) :=
  hgrpIsoOfIso k (prodSliceIso F (sphBelt d)) ≪≫
    hgrpIsoOfHEquiv (prodBeltEquiv F d) k

theorem hgrpProdBeltIso_hom_comp_fst (k : ℕ) :
    (hgrpProdBeltIso F k).hom ≫ HgrpMap k (prodFstMap F (Sph d)) =
      HgrpMap k (subIncl (prodSlice F (sphBelt d)) ≫ prodFstMap F (Sph (d + 1))) := by
  have h : (hgrpProdBeltIso F k).hom =
      HgrpMap k (prodSliceIso F (sphBelt d)).hom ≫
        HgrpMap k (TopCat.ofHom (prodBeltEquiv F d).toFun) := rfl
  rw [h, Category.assoc, ← HgrpMap_comp, ← HgrpMap_comp, prodBelt_fst_factor]


/-! ### Abstract: the complement of a split epimorphism is its kernel -/

section KernelLemmas

variable {C : Type*} [Category* C] [Abelian C] {W N M Z : C}

/-- Transporting a kernel along an isomorphism of the source. -/
def kernelIsoCompIso (e : W ≅ N) (g : N ⟶ M) : kernel (e.hom ≫ g) ≅ kernel g where
  hom := kernel.lift g (kernel.ι _ ≫ e.hom) (by
    rw [Category.assoc]; exact kernel.condition _)
  inv := kernel.lift _ (kernel.ι g ≫ e.inv) (by
    rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp]
    exact kernel.condition g)
  hom_inv_id := by
    refine (cancel_mono (kernel.ι _)).1 ?_
    rw [Category.assoc, kernel.lift_ι, ← Category.assoc, kernel.lift_ι, Category.assoc,
      e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine (cancel_mono (kernel.ι g)).1 ?_
    rw [Category.assoc, kernel.lift_ι, ← Category.assoc, kernel.lift_ι, Category.assoc,
      e.inv_hom_id, Category.comp_id, Category.id_comp]

/-- If an isomorphism `e : N ≅ M ⊞ Z` identifies `π` with the first projection, then `Z` is the
kernel of `π`. -/
def kernelIsoOfSplitting (π : N ⟶ M) (e : N ≅ M ⊞ Z) (he : e.hom ≫ biprod.fst = π) :
    kernel π ≅ Z where
  hom := kernel.ι π ≫ e.hom ≫ biprod.snd
  inv := kernel.lift π (biprod.inr ≫ e.inv) (by
    rw [← he, Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
      biprod.inr_fst])
  hom_inv_id := by
    have key : (kernel.ι π ≫ e.hom) ≫ biprod.snd ≫ biprod.inr = kernel.ι π ≫ e.hom := by
      refine biprod.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, biprod.inr_fst, comp_zero]
        rw [he, kernel.condition]
      · simp only [Category.assoc, biprod.inr_snd, Category.comp_id]
    refine (cancel_mono (kernel.ι π)).1 ?_
    rw [Category.assoc, kernel.lift_ι, Category.id_comp,
      show (kernel.ι π ≫ e.hom ≫ biprod.snd) ≫ biprod.inr ≫ e.inv
        = ((kernel.ι π ≫ e.hom) ≫ biprod.snd ≫ biprod.inr) ≫ e.inv by
          simp only [Category.assoc],
      key, Category.assoc, e.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    rw [← Category.assoc, kernel.lift_ι]
    simp only [Category.assoc]
    rw [← Category.assoc e.inv, e.inv_hom_id, Category.id_comp, biprod.inr_snd]

/-- A split epimorphism with zero kernel is an isomorphism. -/
theorem isIso_of_splitting_of_isZero (π : N ⟶ M) (e : N ≅ M ⊞ Z) (he : e.hom ≫ biprod.fst = π)
    (hZ : IsZero Z) : IsIso π := by
  haveI : IsIso (biprod.fst : M ⊞ Z ⟶ M) := by
    refine ⟨biprod.inl, ?_, biprod.inl_fst⟩
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, biprod.inl_snd, comp_zero, Category.id_comp]
      exact (hZ.eq_zero_of_tgt _).symm
  rw [← he]
  infer_instance

end KernelLemmas

/-! ### The Mayer–Vietoris data of the hemisphere cover -/

variable (d)

/-- A point of the belt of `S^{d+1}`, used as the basepoint of the section. -/
def beltPt : ↥(sphBelt d) := (sphBeltHomotopyEquiv d).invFun (Classical.arbitrary (Sph d))

theorem beltPt_mem_lower : ((beltPt d : Sph (d + 1))) ∈ sphLowerCap d := (beltPt d).2.1

theorem beltPt_mem_upper : ((beltPt d : Sph (d + 1))) ∈ sphUpperCap d := (beltPt d).2.2

/-- The lower hemisphere slice of `F × S^{d+1}`. -/
abbrev capA : Set ↥(prodSph F (d + 1)) := prodSlice F (sphLowerCap d)

/-- The upper hemisphere slice of `F × S^{d+1}`. -/
abbrev capB : Set ↥(prodSph F (d + 1)) := prodSlice F (sphUpperCap d)

theorem capCover : interior (capA F d) ∪ interior (capB F d) = Set.univ :=
  prodSlice_interior_union F

/-- The projection `Hₖ(F × S^{d+1}) ⟶ Hₖ(F)`. -/
abbrev projX (k : ℕ) : Hgrp k (prodSph F (d + 1)) ⟶ Hgrp k F :=
  HgrpMap k (prodFstMap F (Sph (d + 1)))

/-- The projection from the lower slice down to `F`. -/
abbrev projA (k : ℕ) : Hgrp k (TopCat.of ↥(capA F d)) ⟶ Hgrp k F :=
  HgrpMap k (subIncl (capA F d) ≫ prodFstMap F (Sph (d + 1)))

/-- The projection from the upper slice down to `F`. -/
abbrev projB (k : ℕ) : Hgrp k (TopCat.of ↥(capB F d)) ⟶ Hgrp k F :=
  HgrpMap k (subIncl (capB F d) ≫ prodFstMap F (Sph (d + 1)))

/-- The projection from the overlap down to `F`. -/
abbrev projInter (k : ℕ) : Hgrp k (TopCat.of ↥(capA F d ∩ capB F d)) ⟶ Hgrp k F :=
  HgrpMap k (subIncl (capA F d ∩ capB F d) ≫ prodFstMap F (Sph (d + 1)))

instance isIso_projA (k : ℕ) : IsIso (projA F d k) :=
  isIso_HgrpMap_prodSlice_fst F (sphLowerCap d) k

instance isIso_projB (k : ℕ) : IsIso (projB F d k) :=
  isIso_HgrpMap_prodSlice_fst F (sphUpperCap d) k

/-- The section `F ⟶ F × S^{d+1}` at the belt point. -/
abbrev sectX : F ⟶ prodSph F (d + 1) := prodSectMap F ((beltPt d : Sph (d + 1)))

/-- The section of the projection from the lower slice. -/
def sectA : F ⟶ TopCat.of ↥(capA F d) :=
  TopCat.ofHom ⟨fun f => ⟨(f, (beltPt d : Sph (d + 1))), beltPt_mem_lower d⟩,
    Continuous.subtype_mk (by fun_prop) _⟩

/-- The section of the projection from the upper slice. -/
def sectB : F ⟶ TopCat.of ↥(capB F d) :=
  TopCat.ofHom ⟨fun f => ⟨(f, (beltPt d : Sph (d + 1))), beltPt_mem_upper d⟩,
    Continuous.subtype_mk (by fun_prop) _⟩

theorem sectA_comp_subIncl : sectA F d ≫ subIncl (capA F d) = sectX F d := rfl

theorem sectB_comp_subIncl : sectB F d ≫ subIncl (capB F d) = sectX F d := rfl

theorem sectA_comp_proj : sectA F d ≫ subIncl (capA F d) ≫ prodFstMap F (Sph (d + 1)) = 𝟙 F := rfl

theorem sectB_comp_proj : sectB F d ≫ subIncl (capB F d) ≫ prodFstMap F (Sph (d + 1)) = 𝟙 F := rfl

theorem inv_projA (k : ℕ) : inv (projA F d k) = HgrpMap k (sectA F d) := by
  have h : HgrpMap k (sectA F d) ≫ projA F d k = 𝟙 _ := by
    rw [← HgrpMap_comp, sectA_comp_proj, HgrpMap_id]
  rw [← Category.id_comp (inv (projA F d k)), ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

theorem inv_projB (k : ℕ) : inv (projB F d k) = HgrpMap k (sectB F d) := by
  have h : HgrpMap k (sectB F d) ≫ projB F d k = 𝟙 _ := by
    rw [← HgrpMap_comp, sectB_comp_proj, HgrpMap_id]
  rw [← Category.id_comp (inv (projB F d k)), ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

theorem inv_projA_comp (k : ℕ) :
    inv (projA F d k) ≫ HgrpMap k (subIncl (capA F d)) = HgrpMap k (sectX F d) := by
  rw [inv_projA, ← HgrpMap_comp, sectA_comp_subIncl]

theorem inv_projB_comp (k : ℕ) :
    inv (projB F d k) ≫ HgrpMap k (subIncl (capB F d)) = HgrpMap k (sectX F d) := by
  rw [inv_projB, ← HgrpMap_comp, sectB_comp_subIncl]

theorem sectX_comp_projX (k : ℕ) : HgrpMap k (sectX F d) ≫ projX F d k = 𝟙 _ := by
  rw [← HgrpMap_comp, prodSectMap_comp_prodFstMap, HgrpMap_id]

theorem mvIota_comp_map (k : ℕ) :
    mvIota (capA F d) (capB F d) k ≫ biprod.map (projA F d k) (projB F d k) =
      biprod.lift (projInter F d k) (projInter F d k) := by
  rw [mvIota]
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst, biprod.lift_fst,
      ← HgrpMap_comp]
    rfl
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd, biprod.lift_snd,
      ← HgrpMap_comp]
    rfl

theorem mvKappa_comp_projX (k : ℕ) :
    mvKappa (capA F d) (capB F d) k ≫ projX F d k =
      biprod.desc (projA F d k) (-(projB F d k)) := by
  rw [mvKappa]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc_assoc, biprod.inl_desc, ← HgrpMap_comp]
  · rw [biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.neg_comp, ← HgrpMap_comp]

theorem map_inv_comp_mvKappa (k : ℕ) :
    biprod.map (inv (projA F d k)) (inv (projB F d k)) ≫ mvKappa (capA F d) (capB F d) k =
      biprod.desc (HgrpMap k (sectX F d)) (-(HgrpMap k (sectX F d))) := by
  rw [mvKappa]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc, inv_projA_comp]
  · rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc, Preadditive.comp_neg,
      inv_projB_comp]

/-! ### The chase -/

/-- The difference map `(u, v) ↦ u - v`. -/
abbrev diffMap (k : ℕ) : Hgrp k F ⊞ Hgrp k F ⟶ Hgrp k F := biprod.desc (𝟙 _) (-(𝟙 _))

theorem mvKappa_eq (k : ℕ) :
    mvKappa (capA F d) (capB F d) k =
      biprod.map (projA F d k) (projB F d k) ≫ diffMap F k ≫ HgrpMap k (sectX F d) := by
  have h : diffMap F k ≫ HgrpMap k (sectX F d) =
      biprod.desc (HgrpMap k (sectX F d)) (-(HgrpMap k (sectX F d))) := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, biprod.inl_desc, Category.id_comp]
    · rw [biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.neg_comp, Category.id_comp]
  have hid : biprod.map (projA F d k) (projB F d k) ≫
      biprod.map (inv (projA F d k)) (inv (projB F d k)) = 𝟙 _ := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  rw [h, ← map_inv_comp_mvKappa, ← Category.assoc, hid, Category.id_comp]

theorem mvKappa_comp_projX' (k : ℕ) :
    mvKappa (capA F d) (capB F d) k ≫ projX F d k =
      biprod.map (projA F d k) (projB F d k) ≫ diffMap F k := by
  rw [mvKappa_comp_projX]
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [biprod.inl_desc, biprod.inl_map_assoc, biprod.inl_desc, Category.comp_id]
  · rw [biprod.inr_desc, biprod.inr_map_assoc, biprod.inr_desc, Preadditive.comp_neg,
      Category.comp_id]

theorem sectX_comp_mvδ (j : ℕ) :
    HgrpMap (j + 1) (sectX F d) ≫ mvδ (capA F d) (capB F d) (capCover F d) j = 0 := by
  haveI : Epi (diffMap F (j + 1)) :=
    ⟨fun {_} u v h => by
      have := congrArg (fun w => biprod.inl ≫ w) h
      simpa using this⟩
  haveI : Epi (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫ diffMap F (j + 1)) :=
    epi_comp _ _
  refine (cancel_epi (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫
    diffMap F (j + 1))).1 ?_
  rw [comp_zero, show (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫ diffMap F (j + 1)) ≫
      HgrpMap (j + 1) (sectX F d) ≫ mvδ (capA F d) (capB F d) (capCover F d) j
      = (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫ diffMap F (j + 1) ≫
          HgrpMap (j + 1) (sectX F d)) ≫ mvδ (capA F d) (capB F d) (capCover F d) j by
        simp only [Category.assoc], ← mvKappa_eq]
  exact mvKappa_comp_mvδ _ _ _ _

theorem mvδ_comp_projInter (j : ℕ) :
    mvδ (capA F d) (capB F d) (capCover F d) j ≫ projInter F d j = 0 := by
  have h2 : mvδ (capA F d) (capB F d) (capCover F d) j ≫
      biprod.lift (projInter F d j) (projInter F d j) = 0 := by
    rw [← mvIota_comp_map, ← Category.assoc, mvδ_comp_mvIota, zero_comp]
  have := congrArg (fun u => u ≫ (biprod.fst : Hgrp j F ⊞ Hgrp j F ⟶ Hgrp j F)) h2
  simpa using this

/-- The comparison map from the kernel of the projection of `F × S^{d+1}` to the kernel of the
projection of the overlap, given by the Mayer–Vietoris connecting map. -/
def stepMap (j : ℕ) : kernel (projX F d (j + 1)) ⟶ kernel (projInter F d j) :=
  kernel.lift (projInter F d j)
    (kernel.ι (projX F d (j + 1)) ≫ mvδ (capA F d) (capB F d) (capCover F d) j)
    (by rw [Category.assoc, mvδ_comp_projInter, comp_zero])

@[reassoc]
theorem stepMap_comp_ι (j : ℕ) :
    stepMap F d j ≫ kernel.ι (projInter F d j) =
      kernel.ι (projX F d (j + 1)) ≫ mvδ (capA F d) (capB F d) (capCover F d) j :=
  kernel.lift_ι _ _ _

theorem mono_stepMap (j : ℕ) : Mono (stepMap F d j) := by
  rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  have h1 : mvδ (capA F d) (capB F d) (capCover F d) j
      (kernel.ι (projX F d (j + 1)) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← stepMap_comp_ι, ConcreteCategory.comp_apply, hx,
      map_zero]
  obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_kappa_δ (capA F d) (capB F d) (capCover F d) j) _ h1
  have h2 : (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫ diffMap F (j + 1)) w = 0 := by
    rw [← mvKappa_comp_projX', ConcreteCategory.comp_apply, hw, ← ConcreteCategory.comp_apply,
      kernel.condition]
    simp
  have hkappa : mvKappa (capA F d) (capB F d) (j + 1)
      = (biprod.map (projA F d (j + 1)) (projB F d (j + 1)) ≫ diffMap F (j + 1)) ≫
        HgrpMap (j + 1) (sectX F d) := by
    rw [mvKappa_eq]
    simp only [Category.assoc]
  refine (AddCommGrpCat.mono_iff_injective (kernel.ι (projX F d (j + 1)))).1 inferInstance ?_
  rw [map_zero, ← hw, ConcreteCategory.congr_hom hkappa w, ConcreteCategory.comp_apply, h2,
    map_zero]

theorem epi_stepMap (j : ℕ) : Epi (stepMap F d j) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  have hy0 : projInter F d j (kernel.ι (projInter F d j) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, kernel.condition]
    simp
  have hiota : mvIota (capA F d) (capB F d) j (kernel.ι (projInter F d j) y) = 0 := by
    have hmap := ConcreteCategory.congr_hom (mvIota_comp_map F d j)
      (kernel.ι (projInter F d j) y)
    rw [ConcreteCategory.comp_apply] at hmap
    have hlift : biprod.lift (projInter F d j) (projInter F d j) =
        projInter F d j ≫ biprod.lift (𝟙 _) (𝟙 _) := by
      refine biprod.hom_ext _ _ ?_ ?_ <;> simp
    rw [hlift, ConcreteCategory.comp_apply, hy0, map_zero] at hmap
    refine (AddCommGrpCat.mono_iff_injective
      (biprod.map (projA F d j) (projB F d j))).1 inferInstance ?_
    rw [map_zero, hmap]
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_δ_iota (capA F d) (capB F d) (capCover F d) j) _ hiota
  set x' := z - HgrpMap (j + 1) (sectX F d) (projX F d (j + 1) z) with hx'
  have hx'0 : projX F d (j + 1) x' = 0 := by
    rw [hx', map_sub, ← ConcreteCategory.comp_apply, sectX_comp_projX,
      ConcreteCategory.id_apply, sub_self]
  have hk : (ShortComplex.mk (kernel.ι (projX F d (j + 1))) (projX F d (j + 1))
      (kernel.condition _)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 hk x' hx'0
  refine ⟨x, ?_⟩
  refine (AddCommGrpCat.mono_iff_injective (kernel.ι (projInter F d j))).1 inferInstance ?_
  rw [← ConcreteCategory.comp_apply, stepMap_comp_ι, ConcreteCategory.comp_apply, hx, hx',
    map_sub, ← ConcreteCategory.comp_apply, sectX_comp_mvδ]
  simp [hz]

instance isIso_stepMap (j : ℕ) : IsIso (stepMap F d j) :=
  haveI := mono_stepMap F d j
  haveI := epi_stepMap F d j
  isIso_of_mono_of_epi _

/-- **The inductive step, in kernel form.**  The kernel of the projection of `F × S^{d+1}` in
degree `j + 1` is the kernel of the projection of `F × Sᵈ` in degree `j`. -/
def stepKernelIso (j : ℕ) :
    kernel (projX F d (j + 1)) ≅ kernel (HgrpMap j (prodFstMap F (Sph d))) :=
  asIso (stepMap F d j) ≪≫
    kernelIsoOfEq (hgrpProdBeltIso_hom_comp_fst (d := d) F j).symm ≪≫
      kernelIsoCompIso (hgrpProdBeltIso F j) (HgrpMap j (prodFstMap F (Sph d)))

/-! ### The inductive step -/

/-- In degree zero the projection is always an isomorphism, because the two hemisphere slices meet
and Mayer–Vietoris is right exact at `H₀`. -/
theorem isIso_projX_zero : IsIso (projX F d 0) := by
  haveI hepi : Epi (mvKappa (capA F d) (capB F d) 0) := epi_mvKappa_zero _ _ (capCover F d)
  rw [mvKappa_eq] at hepi
  haveI : Epi (diffMap F 0 ≫ HgrpMap 0 (sectX F d)) :=
    epi_of_epi (biprod.map (projA F d 0) (projB F d 0)) _
  haveI : Epi (HgrpMap 0 (sectX F d)) := epi_of_epi (diffMap F 0) _
  haveI : IsSplitMono (HgrpMap 0 (sectX F d)) :=
    IsSplitMono.mk' ⟨projX F d 0, sectX_comp_projX F d 0⟩
  haveI : IsIso (HgrpMap 0 (sectX F d)) := isIso_of_mono_of_epi _
  have hp : projX F d 0 = inv (HgrpMap 0 (sectX F d)) := by
    rw [← Category.id_comp (projX F d 0), ← IsIso.inv_hom_id (HgrpMap 0 (sectX F d)),
      Category.assoc, sectX_comp_projX, Category.comp_id]
  rw [hp]
  infer_instance

/-- **The inductive step for the splitting.**  If `H_*(F × Sᵈ)` splits along the projection, so
does `H_*(F × S^{d+1})`, with the complement shifted by one. -/
def prodSphereSplittingSucc (P : ProdSphereSplitting F d) : ProdSphereSplitting F (d + 1) where
  iso n :=
    hgrpProdSplitIso F ((beltPt d : Sph (d + 1))) (n + d + 1) ≪≫
      biprod.mapIso (Iso.refl _)
        (stepKernelIso F d (n + d) ≪≫
          kernelIsoOfSplitting (HgrpMap (n + d) (prodFstMap F (Sph d))) (P.iso n) (P.iso_fst n))
  iso_fst n := by
    show (hgrpProdSplitIso F ((beltPt d : Sph (d + 1))) (n + d + 1) ≪≫
      biprod.mapIso (Iso.refl _) _).hom ≫ biprod.fst =
        HgrpMap (n + d + 1) (prodFstMap F (Sph (d + 1)))
    rw [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, Iso.refl_hom,
      Category.comp_id, hgrpProdSplitIso_hom_comp_fst]

/-- **The inductive step for the low-degree isomorphism.** -/
theorem prodSphereLowIsoSucc (L : ProdSphereLowIso F d) : ProdSphereLowIso F (d + 1) := by
  intro n hn
  cases n with
  | zero => exact isIso_projX_zero F d
  | succ j =>
    haveI : IsIso (HgrpMap j (prodFstMap F (Sph d))) := L j (by omega)
    have hz : IsZero (kernel (projX F d (j + 1))) :=
      IsZero.of_iso (isZero_kernel_of_mono (HgrpMap j (prodFstMap F (Sph d))))
        (stepKernelIso F d j)
    exact isIso_of_splitting_of_isZero (projX F d (j + 1))
      (hgrpProdSplitIso F ((beltPt d : Sph (d + 1))) (j + 1))
      (hgrpProdSplitIso_hom_comp_fst _ _ _) hz

/-! ### The product formula -/

/-- **The product formula `H_{n+d}(F × Sᵈ) ≅ H_{n+d}(F) ⊞ Hₙ(F)`**, with the first component
induced by the projection.  This is the hypothesis `Submission.ProdSphereSplitting` assumed by the
Wang sequence. -/
def prodSphereSplitting : ∀ d : ℕ, ProdSphereSplitting F d
  | 0 => prodSphereSplittingZero F
  | d + 1 => prodSphereSplittingSucc F d (prodSphereSplitting d)

/-- **Below the dimension of the sphere the projection `F × Sᵈ → F` is a homology
isomorphism.**  This is the hypothesis `Submission.ProdSphereLowIso` assumed by the Wang
sequence. -/
theorem prodSphereLowIso : ∀ d : ℕ, ProdSphereLowIso F d
  | 0 => fun n hn => absurd hn (Nat.not_lt_zero n)
  | d + 1 => prodSphereLowIsoSucc F d (prodSphereLowIso d)

end Submission
