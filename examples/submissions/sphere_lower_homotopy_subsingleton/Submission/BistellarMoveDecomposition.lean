/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Submission.BistellarLocalGluing
import Submission.Cohomology.FiniteOrderedComplexBistellar
import Submission.Cohomology.FiniteOrderedComplexSSet

/-!
# Pushout decomposition of a bistellar move

A valid bistellar move replaces the local ball `A * ∂B` by `∂A * B`.  This file separates
the unchanged outside facets from those two local facet families and proves that their actual
attachment subcomplex is identical on both sides.  Consequently the old and new ordered
simplicial sets are pushouts along the same outside subcomplex, and geometric realization carries
both squares to topological pushouts.

The remaining realization-invariance step is local: construct a homeomorphism between the two
realized bistellar balls that is the identity on their common boundary.  The pushout results here
then provide the gluing interface for extending that homeomorphism by the identity outside.

## Main results

* `Submission.FiniteOrderedComplex.old_inf_new_eq_common`: the two local balls intersect in
  `∂A * ∂B`;
* `Submission.FiniteOrderedComplex.outside_inf_old_eq_outside_inf_new`: their actual attachment
  to the unchanged facets agrees;
* `Submission.FiniteOrderedComplex.bistellarOldRealization_isPushout` and
  `Submission.FiniteOrderedComplex.bistellarNewRealization_isPushout`: the realized old and new
  complexes are the corresponding topological pushouts;
* `Submission.FiniteOrderedComplex.bistellarMoveRealizationIsoOfLocal`: a local isomorphism that
  agrees on the attachment glues with the identity outside to an isomorphism of total
  realizations.
-/

noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.IsPushout

variable {C : Type u} [Category.{v} C]
  {Z X Y₁ Y₂ P₁ P₂ : C}
  {f : Z ⟶ X} {g₁ : Z ⟶ Y₁} {g₂ : Z ⟶ Y₂}
  {inl₁ : X ⟶ P₁} {inr₁ : Y₁ ⟶ P₁}
  {inl₂ : X ⟶ P₂} {inr₂ : Y₂ ⟶ P₂}

/-- Replace the right object in a pushout span by an isomorphic object. -/
theorem changeRightIso (h₂ : IsPushout f g₂ inl₂ inr₂)
    (e : Y₁ ≅ Y₂) (he : g₁ ≫ e.hom = g₂) :
    IsPushout f g₁ inl₂ (e.hom ≫ inr₂) := by
  apply h₂.of_iso (Iso.refl Z) (Iso.refl X) e.symm (Iso.refl P₂)
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp, Iso.symm_hom,
      Iso.comp_inv_eq] using he.symm
  · simp
  · simp

/-- Isomorphic right legs of two pushout spans induce an isomorphism of their pushout objects. -/
noncomputable def isoOfRightIso
    (h₁ : IsPushout f g₁ inl₁ inr₁) (h₂ : IsPushout f g₂ inl₂ inr₂)
    (e : Y₁ ≅ Y₂) (he : g₁ ≫ e.hom = g₂) : P₁ ≅ P₂ :=
  h₁.isoIsPushout X Y₁ (h₂.changeRightIso e he)

@[reassoc (attr := simp)]
theorem inl_isoOfRightIso_hom
    (h₁ : IsPushout f g₁ inl₁ inr₁) (h₂ : IsPushout f g₂ inl₂ inr₂)
    (e : Y₁ ≅ Y₂) (he : g₁ ≫ e.hom = g₂) :
    inl₁ ≫ (h₁.isoOfRightIso h₂ e he).hom = inl₂ := by
  apply inl_isoIsPushout_hom

@[reassoc (attr := simp)]
theorem inr_isoOfRightIso_hom
    (h₁ : IsPushout f g₁ inl₁ inr₁) (h₂ : IsPushout f g₂ inl₂ inr₂)
    (e : Y₁ ≅ Y₂) (he : g₁ ≫ e.hom = g₂) :
    inr₁ ≫ (h₁.isoOfRightIso h₂ e he).hom = e.hom ≫ inr₂ := by
  apply inr_isoIsPushout_hom

end CategoryTheory.IsPushout

namespace Submission.FiniteOrderedComplex

open CategoryTheory Limits

variable {V : Type} [LinearOrder V]

/-- The facets unchanged by a bistellar replacement. -/
def bistellarOutsideFacets (facets : Finset (Finset V)) (A B : Finset V) :
    Finset (Finset V) :=
  facets \ bistellarOldFacets A B

/-- The common boundary facets `∂A * ∂B` of the two bistellar balls. -/
def bistellarCommonFacets (A B : Finset V) : Finset (Finset V) :=
  A.biUnion fun a ↦ B.image fun b ↦ A.erase a ∪ B.erase b

/-- Generating an ordered subcomplex commutes with union of facet families. -/
theorem orderedSubcomplex_union (facets₁ facets₂ : Finset (Finset V)) :
    orderedSubcomplex (facets₁ ∪ facets₂) =
      orderedSubcomplex facets₁ ⊔ orderedSubcomplex facets₂ := by
  ext Δ x
  simp [orderedSubcomplex]
  aesop

/-- Every old local facet named by a valid move is a facet of the original complex. -/
theorem bistellarOldFacets_subset_of_isBistellarMove
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    bistellarOldFacets A B ⊆ facets := by
  rcases h with ⟨_, _, _, _, _, hstar, _⟩
  intro σ hσ
  have hA : A ⊆ σ := by
    rcases Finset.mem_image.mp hσ with ⟨b, hb, rfl⟩
    exact Finset.subset_union_left
  have hmem : σ ∈ facets.filter (fun τ ↦ A ⊆ τ) := by
    rw [hstar]
    exact hσ
  exact (Finset.mem_filter.mp hmem).1

/-- A valid move partitions the original facets into unchanged and old local facets. -/
theorem facets_eq_outside_union_old
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    facets = bistellarOutsideFacets facets A B ∪ bistellarOldFacets A B := by
  rw [bistellarOutsideFacets, Finset.sdiff_union_of_subset]
  exact bistellarOldFacets_subset_of_isBistellarMove h

/-- The original ordered complex is the union of the unchanged outside and the old local ball. -/
theorem orderedSubcomplex_eq_outside_sup_old
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    orderedSubcomplex facets =
      orderedSubcomplex (bistellarOutsideFacets facets A B) ⊔
        orderedSubcomplex (bistellarOldFacets A B) := by
  exact (congrArg (fun fs ↦ orderedSubcomplex fs) (facets_eq_outside_union_old h)).trans
    (orderedSubcomplex_union _ _)

/-- The moved ordered complex is the union of the unchanged outside and the new local ball. -/
theorem orderedSubcomplex_bistellarMove_eq_outside_sup_new
    (facets : Finset (Finset V)) (A B : Finset V) :
    orderedSubcomplex (bistellarMove facets A B) =
      orderedSubcomplex (bistellarOutsideFacets facets A B) ⊔
        orderedSubcomplex (bistellarNewFacets A B) := by
  rw [bistellarMove, bistellarOutsideFacets, orderedSubcomplex_union]

/-- Membership in the old local ball, expressed by its omitted `B` vertex. -/
theorem mem_orderedSubcomplex_bistellarOldFacets
    {A B : Finset V} {Δ : SimplexCategoryᵒᵖ} (x : (CategoryTheory.nerve V).obj Δ) :
    x ∈ (orderedSubcomplex (bistellarOldFacets A B)).obj Δ ↔
      ∃ b ∈ B, ∀ i, x.obj i ∈ A ∪ B.erase b := by
  simp only [orderedSubcomplex, bistellarOldFacets, Finset.mem_image]
  aesop

/-- Membership in the new local ball, expressed by its omitted `A` vertex. -/
theorem mem_orderedSubcomplex_bistellarNewFacets
    {A B : Finset V} {Δ : SimplexCategoryᵒᵖ} (x : (CategoryTheory.nerve V).obj Δ) :
    x ∈ (orderedSubcomplex (bistellarNewFacets A B)).obj Δ ↔
      ∃ a ∈ A, ∀ i, x.obj i ∈ A.erase a ∪ B := by
  simp only [orderedSubcomplex, bistellarNewFacets, Finset.mem_image]
  aesop

/-- Membership in the common boundary, expressed by omitted vertices in both cores. -/
theorem mem_orderedSubcomplex_bistellarCommonFacets
    {A B : Finset V} {Δ : SimplexCategoryᵒᵖ} (x : (CategoryTheory.nerve V).obj Δ) :
    x ∈ (orderedSubcomplex (bistellarCommonFacets A B)).obj Δ ↔
      ∃ a ∈ A, ∃ b ∈ B, ∀ i, x.obj i ∈ A.erase a ∪ B.erase b := by
  simp only [orderedSubcomplex, bistellarCommonFacets, Finset.mem_biUnion,
    Finset.mem_image]
  aesop

/-- For disjoint cores, the old and new local balls intersect in exactly `∂A * ∂B`. -/
theorem old_inf_new_eq_common {A B : Finset V} (hdisj : Disjoint A B) :
    orderedSubcomplex (bistellarOldFacets A B) ⊓
        orderedSubcomplex (bistellarNewFacets A B) =
      orderedSubcomplex (bistellarCommonFacets A B) := by
  ext Δ x
  change
    (x ∈ (orderedSubcomplex (bistellarOldFacets A B)).obj Δ ∧
      x ∈ (orderedSubcomplex (bistellarNewFacets A B)).obj Δ) ↔
        x ∈ (orderedSubcomplex (bistellarCommonFacets A B)).obj Δ
  rw [mem_orderedSubcomplex_bistellarOldFacets,
    mem_orderedSubcomplex_bistellarNewFacets,
    mem_orderedSubcomplex_bistellarCommonFacets]
  constructor
  · rintro ⟨⟨b, hb, hold⟩, ⟨a, ha, hnew⟩⟩
    refine ⟨a, ha, b, hb, fun i ↦ ?_⟩
    have holdi := hold i
    have hnewi := hnew i
    simp only [Finset.mem_union, Finset.mem_erase] at holdi hnewi ⊢
    rcases holdi with hA | hB
    · rcases hnewi with hA' | hB'
      · exact Or.inl hA'
      · exact False.elim ((Finset.disjoint_left.mp hdisj) hA hB')
    · exact Or.inr hB
  · rintro ⟨a, ha, b, hb, hcommon⟩
    refine ⟨⟨b, hb, fun i ↦ ?_⟩, ⟨a, ha, fun i ↦ ?_⟩⟩
    · have hcommoni := hcommon i
      simp only [Finset.mem_union, Finset.mem_erase] at hcommoni ⊢
      exact hcommoni.imp (fun h ↦ h.2) id
    · have hcommoni := hcommon i
      simp only [Finset.mem_union, Finset.mem_erase] at hcommoni ⊢
      exact hcommoni.imp id (fun h ↦ h.2)

/-- Membership in the unchanged outside facet family. -/
theorem mem_orderedSubcomplex_bistellarOutsideFacets
    {facets : Finset (Finset V)} {A B : Finset V} {Δ : SimplexCategoryᵒᵖ}
    (x : (CategoryTheory.nerve V).obj Δ) :
    x ∈ (orderedSubcomplex (bistellarOutsideFacets facets A B)).obj Δ ↔
      ∃ facet ∈ facets, facet ∉ bistellarOldFacets A B ∧
        ∀ i, x.obj i ∈ facet := by
  simp only [orderedSubcomplex, bistellarOutsideFacets, Finset.mem_sdiff]
  aesop

/-- The old and new local balls meet the unchanged outside in the same subcomplex. -/
theorem outside_inf_old_eq_outside_inf_new
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    orderedSubcomplex (bistellarOutsideFacets facets A B) ⊓
        orderedSubcomplex (bistellarOldFacets A B) =
      orderedSubcomplex (bistellarOutsideFacets facets A B) ⊓
        orderedSubcomplex (bistellarNewFacets A B) := by
  rcases h with ⟨_, _, _, _, _, hstar, habsent⟩
  ext Δ x
  change
    (x ∈ (orderedSubcomplex (bistellarOutsideFacets facets A B)).obj Δ ∧
      x ∈ (orderedSubcomplex (bistellarOldFacets A B)).obj Δ) ↔
    (x ∈ (orderedSubcomplex (bistellarOutsideFacets facets A B)).obj Δ ∧
      x ∈ (orderedSubcomplex (bistellarNewFacets A B)).obj Δ)
  rw [mem_orderedSubcomplex_bistellarOutsideFacets,
    mem_orderedSubcomplex_bistellarOldFacets,
    mem_orderedSubcomplex_bistellarNewFacets]
  constructor
  · rintro ⟨⟨facet, hfacet, hfacetNotOld, hfacetContains⟩, ⟨b, hb, hold⟩⟩
    refine ⟨⟨facet, hfacet, hfacetNotOld, hfacetContains⟩, ?_⟩
    let vertices : Finset V := Finset.univ.image fun i ↦ x.obj i
    by_cases hA : A ⊆ vertices
    · have hAfacet : A ⊆ facet := by
        intro a ha
        rcases Finset.mem_image.mp (hA ha) with ⟨i, _, hi⟩
        simpa [hi] using hfacetContains i
      have hfacetStar : facet ∈ facets.filter (fun σ ↦ A ⊆ σ) :=
        Finset.mem_filter.mpr ⟨hfacet, hAfacet⟩
      rw [hstar] at hfacetStar
      exact False.elim (hfacetNotOld hfacetStar)
    · rcases Finset.not_subset.mp hA with ⟨a, ha, haNotVertices⟩
      refine ⟨a, ha, fun i ↦ ?_⟩
      have hxiNe : x.obj i ≠ a := by
        intro hia
        apply haNotVertices
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hia⟩
      have holdi := hold i
      simp only [Finset.mem_union, Finset.mem_erase] at holdi ⊢
      exact holdi.imp (fun hxiA ↦ ⟨hxiNe, hxiA⟩) (fun hxiB ↦ hxiB.2)
  · rintro ⟨⟨facet, hfacet, hfacetNotOld, hfacetContains⟩, ⟨a, ha, hnew⟩⟩
    refine ⟨⟨facet, hfacet, hfacetNotOld, hfacetContains⟩, ?_⟩
    let vertices : Finset V := Finset.univ.image fun i ↦ x.obj i
    by_cases hB : B ⊆ vertices
    · have hBfacet : B ⊆ facet := by
        intro b hb
        rcases Finset.mem_image.mp (hB hb) with ⟨i, _, hi⟩
        simpa [hi] using hfacetContains i
      have hfacetNew : facet ∈ facets.filter (fun σ ↦ B ⊆ σ) :=
        Finset.mem_filter.mpr ⟨hfacet, hBfacet⟩
      rw [habsent] at hfacetNew
      simp at hfacetNew
    · rcases Finset.not_subset.mp hB with ⟨b, hb, hbNotVertices⟩
      refine ⟨b, hb, fun i ↦ ?_⟩
      have hxiNe : x.obj i ≠ b := by
        intro hib
        apply hbNotVertices
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hib⟩
      have hnewi := hnew i
      simp only [Finset.mem_union, Finset.mem_erase] at hnewi ⊢
      exact hnewi.imp (fun hxiA ↦ hxiA.2) (fun hxiB ↦ ⟨hxiNe, hxiB⟩)

/-- The actual attachment subcomplex where the unchanged outside meets the old local ball. -/
def bistellarAttachmentSubcomplex (facets : Finset (Finset V)) (A B : Finset V) :
    (CategoryTheory.nerve V).Subcomplex :=
  orderedSubcomplex (bistellarOutsideFacets facets A B) ⊓
    orderedSubcomplex (bistellarOldFacets A B)

/-- The original complex is a bicartesian lattice square of its outside and old local ball. -/
theorem bistellarOldBicartSq
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    Lattice.BicartSq
      (bistellarAttachmentSubcomplex facets A B)
      (orderedSubcomplex (bistellarOutsideFacets facets A B))
      (orderedSubcomplex (bistellarOldFacets A B))
      (orderedSubcomplex facets) where
  sup_eq := (orderedSubcomplex_eq_outside_sup_old h).symm
  inf_eq := rfl

/-- The moved complex is a bicartesian lattice square of its outside and new local ball. -/
theorem bistellarNewBicartSq
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    Lattice.BicartSq
      (bistellarAttachmentSubcomplex facets A B)
      (orderedSubcomplex (bistellarOutsideFacets facets A B))
      (orderedSubcomplex (bistellarNewFacets A B))
      (orderedSubcomplex (bistellarMove facets A B)) where
  sup_eq := (orderedSubcomplex_bistellarMove_eq_outside_sup_new facets A B).symm
  inf_eq := (outside_inf_old_eq_outside_inf_new h).symm

/-- The actual attachment lies in the full common boundary `∂A * ∂B`. -/
theorem bistellarAttachmentSubcomplex_le_common
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    bistellarAttachmentSubcomplex facets A B ≤
      orderedSubcomplex (bistellarCommonFacets A B) := by
  rw [← old_inf_new_eq_common h.2.2.2.1]
  refine le_inf inf_le_right ?_
  rw [bistellarAttachmentSubcomplex, outside_inf_old_eq_outside_inf_new h]
  exact inf_le_right

/-- The original ordered simplicial set is the pushout of its outside and old local ball. -/
theorem bistellarOld_isPushout
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    let sq := bistellarOldBicartSq h
    IsPushout
      (SSet.Subcomplex.homOfLE sq.le₁₂)
      (SSet.Subcomplex.homOfLE sq.le₁₃)
      (SSet.Subcomplex.homOfLE sq.le₂₄)
      (SSet.Subcomplex.homOfLE sq.le₃₄) := by
  dsimp
  exact SSet.Subcomplex.BicartSq.isPushout (bistellarOldBicartSq h)

/-- The moved ordered simplicial set is the pushout of its outside and new local ball. -/
theorem bistellarNew_isPushout
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    let sq := bistellarNewBicartSq h
    IsPushout
      (SSet.Subcomplex.homOfLE sq.le₁₂)
      (SSet.Subcomplex.homOfLE sq.le₁₃)
      (SSet.Subcomplex.homOfLE sq.le₂₄)
      (SSet.Subcomplex.homOfLE sq.le₃₄) := by
  dsimp
  exact SSet.Subcomplex.BicartSq.isPushout (bistellarNewBicartSq h)

/-- Realization carries the original-complex decomposition to a topological pushout. -/
theorem bistellarOldRealization_isPushout
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    let sq := bistellarOldBicartSq h
    IsPushout
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₁₂))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₁₃))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₂₄))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₃₄)) := by
  dsimp
  exact (bistellarOld_isPushout h).map SSet.toTop

/-- Realization carries the moved-complex decomposition to a topological pushout. -/
theorem bistellarNewRealization_isPushout
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    let sq := bistellarNewBicartSq h
    IsPushout
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₁₂))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₁₃))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₂₄))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE sq.le₃₄)) := by
  dsimp
  exact (bistellarNew_isPushout h).map SSet.toTop

/-- A boundary-compatible isomorphism of the two local realized balls glues with the identity on
the unchanged outside to an isomorphism of the whole realizations. -/
noncomputable def bistellarMoveRealizationIsoOfLocal
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B)
    (e : SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≅
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)))
    (he :
      let oldSq := bistellarOldBicartSq h
      let newSq := bistellarNewBicartSq h
      SSet.toTop.map (SSet.Subcomplex.homOfLE oldSq.le₁₃) ≫ e.hom =
        SSet.toTop.map (SSet.Subcomplex.homOfLE newSq.le₁₃)) :
    SSet.toTop.obj (orderedSSet facets) ≅
      SSet.toTop.obj (orderedSSet (bistellarMove facets A B)) :=
  (bistellarOldRealization_isPushout h).isoOfRightIso
    (bistellarNewRealization_isPushout h) e he

/-- The glued realization isomorphism restricts to the identity on the unchanged outside. -/
@[reassoc (attr := simp)]
theorem bistellarMoveRealizationIsoOfLocal_hom_outside
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B)
    (e : SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≅
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)))
    (he :
      let oldSq := bistellarOldBicartSq h
      let newSq := bistellarNewBicartSq h
      SSet.toTop.map (SSet.Subcomplex.homOfLE oldSq.le₁₃) ≫ e.hom =
        SSet.toTop.map (SSet.Subcomplex.homOfLE newSq.le₁₃)) :
    let oldSq := bistellarOldBicartSq h
    let newSq := bistellarNewBicartSq h
    SSet.toTop.map (SSet.Subcomplex.homOfLE oldSq.le₂₄) ≫
        (bistellarMoveRealizationIsoOfLocal h e he).hom =
      SSet.toTop.map (SSet.Subcomplex.homOfLE newSq.le₂₄) := by
  apply CategoryTheory.IsPushout.inl_isoOfRightIso_hom

/-- The glued realization isomorphism restricts to the supplied local isomorphism. -/
@[reassoc (attr := simp)]
theorem bistellarMoveRealizationIsoOfLocal_hom_local
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B)
    (e : SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≅
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)))
    (he :
      let oldSq := bistellarOldBicartSq h
      let newSq := bistellarNewBicartSq h
      SSet.toTop.map (SSet.Subcomplex.homOfLE oldSq.le₁₃) ≫ e.hom =
        SSet.toTop.map (SSet.Subcomplex.homOfLE newSq.le₁₃)) :
    let oldSq := bistellarOldBicartSq h
    let newSq := bistellarNewBicartSq h
    SSet.toTop.map (SSet.Subcomplex.homOfLE oldSq.le₃₄) ≫
        (bistellarMoveRealizationIsoOfLocal h e he).hom =
      e.hom ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE newSq.le₃₄) := by
  apply CategoryTheory.IsPushout.inr_isoOfRightIso_hom

end Submission.FiniteOrderedComplex
