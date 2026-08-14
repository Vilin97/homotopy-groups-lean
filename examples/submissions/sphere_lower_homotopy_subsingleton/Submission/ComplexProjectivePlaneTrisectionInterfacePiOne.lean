/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianEssentiality
import Submission.ComplexProjectivePlaneTrisectionInterfaceHomotopy
import Submission.ComplexProjectivePlaneTrisectionCentralTorusProductTopology

/-!
# Fundamental-group maps of the projective-plane trisection

This file identifies the maps on `π₁` induced by the three inclusions from the central torus
into the pairwise solid-torus interfaces.  The central technical point is relative control of the
four certified bistellar moves: the global realization homeomorphism fixes both the unchanged
outside and the common boundary of the old and new local balls.  A pushout argument glues these
two fixed regions, and an explicit finite certificate shows that they carry the central interface
throughout the zero-five reduction.

The resulting commuting square compares the actual zero-five inclusion with the boundary
inclusion of the standard seven-vertex solid torus.  The latter is surjective on `π₁` because
the standard solid torus collapses to its displayed core circle.  Exact cyclic reindexing squares
then transport surjectivity to the five-four and four-zero interfaces.  Finally, naturality of
change of basepoint transports these results from the displayed core to the three explicit
meridian basepoints.

Together with the explicit noninjectivity results in
`ComplexProjectivePlaneTrisectionMeridianEssentiality`, this proves the two characteristic
features of all three solid-torus filling maps at the same concrete basepoints: each is
surjective, while its corresponding meridian supplies a nontrivial kernel class.  In every
degree above one, the previously computed vanishing of both groups makes each induced map
bijective at every basepoint.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

/-! ## General transport lemmas -/

/-- The inverse continuous map of a homotopy equivalence induces a bijection on every positive
finite-dimensional homotopy group. -/
theorem homotopyGroup_map_invFun_bijective
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (y : Y) :
    Function.Bijective
      (HomotopyGroup.map (N := N) (x := y) (y := e.invFun y)
        e.invFun rfl) := by
  let equivalence :=
    homotopyGroupMulEquivOfHomotopyEquiv (N := N) e.symm y
  have hfun : (fun a => equivalence a) =
      HomotopyGroup.map (N := N) (x := y) (y := e.invFun y)
        e.invFun rfl := by
    funext a
    exact homotopyGroupMulEquivOfHomotopyEquiv_apply
      (N := N) e.symm y a
  rw [← hfun]
  exact equivalence.bijective

/-- Postcomposition commutes exactly with change of basepoint along the image of a path. -/
theorem GenLoop.map_transport
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x' : X} (gamma : Path x x')
    (p : GenLoop N X x) :
    GenLoop.map f rfl (GenLoop.transport gamma p) =
      GenLoop.transport (gamma.map f.continuous) (GenLoop.map f rfl p) := by
  apply GenLoop.ext
  intro t
  simp only [GenLoop.map_apply, GenLoop.transport_apply]
  unfold transportFun
  split_ifs <;> rfl

/-- The induced map on a positive finite-dimensional homotopy group commutes exactly with
change of basepoint along the image of a path. -/
theorem HomotopyGroup.map_transport
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x' : X} (gamma : Path x x')
    (a : HomotopyGroup N X x) :
    HomotopyGroup.map f rfl (HomotopyGroup.transport gamma a) =
      HomotopyGroup.transport (gamma.map f.continuous)
        (HomotopyGroup.map f rfl a) := by
  induction a using Quotient.ind with
  | _ p =>
      rw [HomotopyGroup.transport_mk, HomotopyGroup.map_mk,
        HomotopyGroup.map_mk, HomotopyGroup.transport_mk,
        GenLoop.map_transport f gamma p]

/-- Surjectivity of an induced positive finite-dimensional homotopy-group map transports from
one basepoint to any other basepoint joined to it by a path. -/
theorem homotopyGroup_map_surjective_of_joined
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x' : X} (gamma : Path x x')
    (hsurjective : Function.Surjective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Surjective
      (HomotopyGroup.map (N := N) (x := x') (y := f x') f rfl) := by
  intro b'
  let delta : Path (f x) (f x') := gamma.map f.continuous
  let b := (HomotopyGroup.transportMulEquiv delta).symm b'
  obtain ⟨a, ha⟩ := hsurjective b
  refine ⟨HomotopyGroup.transport gamma a, ?_⟩
  rw [HomotopyGroup.map_transport]
  change HomotopyGroup.transportMulEquiv delta
      (HomotopyGroup.map f rfl a) = b'
  rw [ha]
  exact (HomotopyGroup.transportMulEquiv delta).apply_symm_apply b'

/-- On a path-connected source, surjectivity of an induced positive finite-dimensional
homotopy-group map is independent of the chosen basepoint. -/
theorem homotopyGroup_map_surjective_of_pathConnected
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (f : C(X, Y)) {x x' : X}
    (hsurjective : Function.Surjective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Surjective
      (HomotopyGroup.map (N := N) (x := x') (y := f x') f rfl) :=
  homotopyGroup_map_surjective_of_joined f
    (PathConnectedSpace.somePath x x') hsurjective

/-- Replacing the definitional target basepoint of an induced map by a propositionally equal
one preserves surjectivity. -/
theorem homotopyGroup_map_surjective_of_base_eq
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (hsurjective : Function.Surjective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl)) :
    Function.Surjective
      (HomotopyGroup.map (N := N) (x := x) (y := y) f h) := by
  subst y
  simpa only using hsurjective

/-- A map between two trivial positive finite-dimensional homotopy groups is bijective. -/
theorem homotopyGroup_map_bijective_of_subsingleton
    {N X Y : Type*} [Fintype N] [Nonempty N] [DecidableEq N]
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}
    [Subsingleton (HomotopyGroup N X x)]
    [Subsingleton (HomotopyGroup N Y y)]
    (f : C(X, Y)) (h : f x = y) :
    Function.Bijective (HomotopyGroup.map (N := N) f h) := by
  constructor
  · intro p q _
    exact Subsingleton.elim p q
  · intro q
    exact ⟨1, Subsingleton.elim _ q⟩

/-- Surjectivity of an induced homotopy-group map is invariant under a commuting square whose
vertical maps are homeomorphisms. -/
theorem homotopyGroup_map_surjective_of_homeomorph_square
    {N X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, Y)) (f' : C(X', Y'))
    (sourceEquiv : X ≃ₜ X') (targetEquiv : Y ≃ₜ Y')
    (hsquare :
      (⟨targetEquiv, targetEquiv.continuous⟩ : C(Y, Y')).comp f =
        f'.comp ⟨sourceEquiv, sourceEquiv.continuous⟩)
    (x : X) (x' : X') (hsource : sourceEquiv x = x')
    {y' : Y'} (hf' : f' x' = y')
    (hsurjective : Function.Surjective
      (HomotopyGroup.map (N := N) (x := x') (y := y') f' hf')) :
    Function.Surjective
      (HomotopyGroup.map (N := N) (x := x) (y := f x) f rfl) := by
  intro q
  have hbase : targetEquiv (f x) = y' :=
    (congrArg (fun k => k x) hsquare).trans
      ((congrArg f' hsource).trans hf')
  let sourcePiEquiv := HomotopyGroup.homeomorphEquivOfEq
    (N := N) sourceEquiv hsource
  let targetPiEquiv := HomotopyGroup.homeomorphEquivOfEq
    (N := N) targetEquiv hbase
  obtain ⟨p', hp'⟩ := hsurjective (targetPiEquiv q)
  let p := sourcePiEquiv.symm p'
  refine ⟨p, targetPiEquiv.injective ?_⟩
  calc
    targetPiEquiv (HomotopyGroup.map f rfl p) =
        HomotopyGroup.map
          ((⟨targetEquiv, targetEquiv.continuous⟩ : C(Y, Y')).comp f)
          (by simpa using hbase) p := by
      rw [HomotopyGroup.homeomorphEquivOfEq_apply,
        HomotopyGroup.map_comp_apply]
    _ = HomotopyGroup.map
          (f'.comp ⟨sourceEquiv, sourceEquiv.continuous⟩)
          (by simpa [hsource] using hf') p := by
      exact HomotopyGroup.map_congr hsquare _ _ p
    _ = HomotopyGroup.map f' hf'
          (HomotopyGroup.map
            (⟨sourceEquiv, sourceEquiv.continuous⟩ : C(X, X'))
            hsource p) := by
      symm
      exact HomotopyGroup.map_comp_apply f' hf'
        ⟨sourceEquiv, sourceEquiv.continuous⟩ hsource p
    _ = HomotopyGroup.map f' hf' p' := by
      apply congrArg (HomotopyGroup.map f' hf')
      change sourcePiEquiv p = p'
      exact sourcePiEquiv.apply_symm_apply p'
    _ = targetPiEquiv q := hp'

theorem comp_commuting_squares
    {C : Type*} [Category C]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    {f₀ : X₀ ⟶ Y₀} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {source₀ : X₀ ⟶ X₁} {source₁ : X₁ ⟶ X₂}
    {target₀ : Y₀ ⟶ Y₁} {target₁ : Y₁ ⟶ Y₂}
    (h₀ : f₀ ≫ target₀ = source₀ ≫ f₁)
    (h₁ : f₁ ≫ target₁ = source₁ ≫ f₂) :
    f₀ ≫ (target₀ ≫ target₁) =
      (source₀ ≫ source₁) ≫ f₂ := by
  rw [← Category.assoc, h₀, Category.assoc, h₁, ← Category.assoc]

theorem iso_square_inv
    {C : Type*} [Category C]
    {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (sourceEquiv : X ≅ X') (targetEquiv : Y ≅ Y')
    (h : f ≫ targetEquiv.hom = sourceEquiv.hom ≫ g) :
    g ≫ targetEquiv.inv = sourceEquiv.inv ≫ f := by
  rw [← cancel_epi sourceEquiv.hom]
  calc
    _ = (sourceEquiv.hom ≫ g) ≫ targetEquiv.inv := by
      rw [Category.assoc]
    _ = (f ≫ targetEquiv.hom) ≫ targetEquiv.inv := by rw [h]
    _ = f := by simp
    _ = sourceEquiv.hom ≫ (sourceEquiv.inv ≫ f) := by simp

namespace FiniteOrderedComplex

/-! ## Naturality for finite ordered complexes -/

variable {V : Type} [LinearOrder V]

omit [LinearOrder V] in
theorem FacetFamilyLE.trans
    {first second third : Finset (Finset V)}
    (hfirstSecond : FacetFamilyLE first second)
    (hsecondThird : FacetFamilyLE second third) :
    FacetFamilyLE first third := by
  intro facet hfacet
  obtain ⟨middleFacet, hmiddleFacet, hfacetMiddle⟩ :=
    hfirstSecond facet hfacet
  obtain ⟨lastFacet, hlastFacet, hmiddleLast⟩ :=
    hsecondThird middleFacet hmiddleFacet
  exact ⟨lastFacet, hlastFacet, hfacetMiddle.trans hmiddleLast⟩

theorem FacetFamilyLE.union
    {left right target : Finset (Finset V)}
    (hleft : FacetFamilyLE left target)
    (hright : FacetFamilyLE right target) :
    FacetFamilyLE (left ∪ right) target := by
  intro facet hfacet
  rcases Finset.mem_union.mp hfacet with hfacet | hfacet
  · exact hleft facet hfacet
  · exact hright facet hfacet

omit [LinearOrder V] in
theorem mapFacets_facetFamilyLE
    {W : Type} [LinearOrder W] (e : V ↪ W)
    {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    FacetFamilyLE (mapFacets e source) (mapFacets e target) := by
  intro mappedFacet hmappedFacet
  obtain ⟨facet, hfacet, rfl⟩ := Finset.mem_map.mp hmappedFacet
  obtain ⟨targetFacet, htargetFacet, hsubset⟩ := h facet hfacet
  exact ⟨targetFacet.map e,
    Finset.mem_map.mpr ⟨targetFacet, htargetFacet, rfl⟩,
    Finset.map_subset_map.mpr hsubset⟩

theorem orderedSSetMapFacetsIso_naturality
    {W : Type} [LinearOrder W] (e : V ↪o W)
    {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    orderedSSetHomOfFacetFamilyLE h ≫
        (orderedSSetMapFacetsIso e target).hom =
      (orderedSSetMapFacetsIso e source).hom ≫
        orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h) := by
  rw [← cancel_mono
    (orderedSubcomplex (mapFacets e.toEmbedding target)).ι]
  simp only [Category.assoc, orderedSSetMapFacetsIso_hom_ι]
  rfl

theorem orderedSSetMapFacetsIso_inv_naturality
    {W : Type} [LinearOrder W] (e : V ↪o W)
    {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h) ≫
        (orderedSSetMapFacetsIso e target).inv =
      (orderedSSetMapFacetsIso e source).inv ≫
        orderedSSetHomOfFacetFamilyLE h := by
  rw [← cancel_epi (orderedSSetMapFacetsIso e source).hom]
  calc
    _ = ((orderedSSetMapFacetsIso e source).hom ≫
          orderedSSetHomOfFacetFamilyLE
            (mapFacets_facetFamilyLE e.toEmbedding h)) ≫
        (orderedSSetMapFacetsIso e target).inv := by
      rw [Category.assoc]
    _ = (orderedSSetHomOfFacetFamilyLE h ≫
          (orderedSSetMapFacetsIso e target).hom) ≫
        (orderedSSetMapFacetsIso e target).inv := by
      rw [orderedSSetMapFacetsIso_naturality e h]
    _ = orderedSSetHomOfFacetFamilyLE h := by simp
    _ = (orderedSSetMapFacetsIso e source).hom ≫
        ((orderedSSetMapFacetsIso e source).inv ≫
          orderedSSetHomOfFacetFamilyLE h) := by simp

theorem orderedSSetHomOfFacetFamilyLE_eqToIso_inv_naturality
    {source target source' target' : Finset (Finset V)}
    (hsource : source = source') (htarget : target = target')
    (h : FacetFamilyLE source target)
    (h' : FacetFamilyLE source' target') :
    orderedSSetHomOfFacetFamilyLE h' ≫
        (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex htarget)).inv =
      (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex hsource)).inv ≫
        orderedSSetHomOfFacetFamilyLE h := by
  subst source'
  subst target'
  rfl

theorem orderedSSetHomOfFacetFamilyLE_eqToIso_naturality
    {source target source' target' : Finset (Finset V)}
    (hsource : source = source') (htarget : target = target')
    (h : FacetFamilyLE source target)
    (h' : FacetFamilyLE source' target') :
    orderedSSetHomOfFacetFamilyLE h ≫
        (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex htarget)).hom =
      (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex hsource)).hom ≫
        orderedSSetHomOfFacetFamilyLE h' := by
  subst source'
  subst target'
  rfl

omit [LinearOrder V] in
theorem facetFamilyCarrierReindexHomeomorph_naturality
    [Fintype V] {W : Type} [Fintype W] [LinearOrder W]
    (e : V ≃ W) {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    facetFamilyCarrierHomOfFacetFamilyLE h ≫
        (TopCat.isoOfHomeo
          (facetFamilyCarrierReindexHomeomorph e target)).hom =
      (TopCat.isoOfHomeo
          (facetFamilyCarrierReindexHomeomorph e source)).hom ≫
        facetFamilyCarrierHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

theorem facetFamilyCarrierHom_comp_orderedRealizationFrom_naturality
    [Fintype V] {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    facetFamilyCarrierHomOfFacetFamilyLE h ≫
        orderedRealizationFromFacetFamilyCarrier target =
      orderedRealizationFromFacetFamilyCarrier source ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) := by
  have hnatural := orderedRealizationToFacetFamilyCarrier_naturality h
  rw [← cancel_epi (TopCat.isoOfHomeo
    (orderedRealizationHomeomorphFacetFamilyCarrier source)).hom]
  change orderedRealizationToFacetFamilyCarrier source ≫
      (facetFamilyCarrierHomOfFacetFamilyLE h ≫
        orderedRealizationFromFacetFamilyCarrier target) =
    orderedRealizationToFacetFamilyCarrier source ≫
      (orderedRealizationFromFacetFamilyCarrier source ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h))
  calc
    _ = (orderedRealizationToFacetFamilyCarrier source ≫
          facetFamilyCarrierHomOfFacetFamilyLE h) ≫
        orderedRealizationFromFacetFamilyCarrier target := by
      rw [Category.assoc]
    _ = (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) ≫
          orderedRealizationToFacetFamilyCarrier target) ≫
        orderedRealizationFromFacetFamilyCarrier target := by
      exact congrArg (fun k ↦ k ≫
        orderedRealizationFromFacetFamilyCarrier target) hnatural.symm
    _ = SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) := by
      rw [Category.assoc,
        orderedRealizationToFacetFamilyCarrier_comp_fromCarrier,
        Category.comp_id]
    _ = orderedRealizationToFacetFamilyCarrier source ≫
        (orderedRealizationFromFacetFamilyCarrier source ≫
          SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h)) := by
      rw [← Category.assoc,
        orderedRealizationToFacetFamilyCarrier_comp_fromCarrier,
        Category.id_comp]

theorem orderedRealizationReindexHomeomorph_component_naturality
    [Fintype V] {W : Type} [Fintype W] [LinearOrder W]
    (e : V ≃ W) {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) ≫
        ((orderedRealizationToFacetFamilyCarrier target ≫
            (TopCat.isoOfHomeo
              (facetFamilyCarrierReindexHomeomorph e target)).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            (mapFacets e.toEmbedding target)) =
      ((orderedRealizationToFacetFamilyCarrier source ≫
          (TopCat.isoOfHomeo
            (facetFamilyCarrierReindexHomeomorph e source)).hom) ≫
        orderedRealizationFromFacetFamilyCarrier
          (mapFacets e.toEmbedding source)) ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h)) := by
  have h₀ := orderedRealizationToFacetFamilyCarrier_naturality h
  have h₁ := facetFamilyCarrierReindexHomeomorph_naturality e h
  have h₂ := facetFamilyCarrierHom_comp_orderedRealizationFrom_naturality
    (mapFacets_facetFamilyLE e.toEmbedding h)
  exact comp_commuting_squares (comp_commuting_squares h₀ h₁) h₂

theorem orderedRealizationReindexHomeomorph_naturality
    [Fintype V] {W : Type} [Fintype W] [LinearOrder W]
    (e : V ≃ W) {source target : Finset (Finset V)}
    (h : FacetFamilyLE source target) :
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) ≫
        (TopCat.isoOfHomeo
          (orderedRealizationReindexHomeomorph e target)).hom =
      (TopCat.isoOfHomeo
          (orderedRealizationReindexHomeomorph e source)).hom ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h)) := by
  change
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) ≫
        (orderedRealizationToFacetFamilyCarrier target ≫
          ((TopCat.isoOfHomeo
              (facetFamilyCarrierReindexHomeomorph e target)).hom ≫
            orderedRealizationFromFacetFamilyCarrier
              (mapFacets e.toEmbedding target))) =
      (orderedRealizationToFacetFamilyCarrier source ≫
        ((TopCat.isoOfHomeo
            (facetFamilyCarrierReindexHomeomorph e source)).hom ≫
          orderedRealizationFromFacetFamilyCarrier
            (mapFacets e.toEmbedding source))) ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE e.toEmbedding h))
  simpa only [Category.assoc] using
    orderedRealizationReindexHomeomorph_component_naturality e h

/-! ## Bistellar homeomorphisms relative to their stable boundary -/

theorem bistellarOutsideFacets_le_original
    (facets : Finset (Finset V)) (A B : Finset V) :
    FacetFamilyLE (bistellarOutsideFacets facets A B) facets := by
  intro facet hfacet
  exact ⟨facet, (Finset.mem_sdiff.mp hfacet).1, Finset.Subset.rfl⟩

theorem bistellarOutsideFacets_le_move
    (facets : Finset (Finset V)) (A B : Finset V) :
    FacetFamilyLE (bistellarOutsideFacets facets A B)
      (bistellarMove facets A B) := by
  intro facet hfacet
  exact ⟨facet, Finset.mem_union_left _ hfacet, Finset.Subset.rfl⟩

theorem bistellarCommonFacets_le_old
    (A B : Finset V) :
    FacetFamilyLE (bistellarCommonFacets A B)
      (bistellarOldFacets A B) := by
  intro facet hfacet
  rw [bistellarCommonFacets, Finset.mem_biUnion] at hfacet
  obtain ⟨a, ha, hfacet⟩ := hfacet
  rw [Finset.mem_image] at hfacet
  obtain ⟨b, hb, rfl⟩ := hfacet
  refine ⟨A ∪ B.erase b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
  exact Finset.union_subset_union (Finset.erase_subset _ _) Finset.Subset.rfl

theorem bistellarCommonFacets_le_new
    (A B : Finset V) :
    FacetFamilyLE (bistellarCommonFacets A B)
      (bistellarNewFacets A B) := by
  intro facet hfacet
  rw [bistellarCommonFacets, Finset.mem_biUnion] at hfacet
  obtain ⟨a, ha, hfacet⟩ := hfacet
  rw [Finset.mem_image] at hfacet
  obtain ⟨b, hb, rfl⟩ := hfacet
  refine ⟨A.erase a ∪ B, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  exact Finset.union_subset_union Finset.Subset.rfl (Finset.erase_subset _ _)

theorem bistellarOldFacets_le_original
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (hmove : IsBistellarMove facets dimension A B) :
    FacetFamilyLE (bistellarOldFacets A B) facets := by
  intro facet hfacet
  exact ⟨facet, bistellarOldFacets_subset_of_isBistellarMove hmove hfacet,
    Finset.Subset.rfl⟩

theorem bistellarNewFacets_le_move
    (facets : Finset (Finset V)) (A B : Finset V) :
    FacetFamilyLE (bistellarNewFacets A B)
      (bistellarMove facets A B) := by
  intro facet hfacet
  exact ⟨facet, Finset.mem_union_right _ hfacet, Finset.Subset.rfl⟩

/-- The canonical bistellar realization homeomorphism is pointwise fixed on the common local
boundary. -/
theorem bistellarMoveRealizationIso_hom_common
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (hmove : IsBistellarMove facets dimension A B) :
    SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          ((bistellarCommonFacets_le_old A B).trans
            (bistellarOldFacets_le_original hmove))) ≫
        (bistellarMoveRealizationIso hmove).hom =
      SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          ((bistellarCommonFacets_le_new A B).trans
            (bistellarNewFacets_le_move facets A B))) := by
  let commonToOld := orderedSSetHomOfFacetFamilyLE
    (bistellarCommonFacets_le_old A B)
  let commonToNew := orderedSSetHomOfFacetFamilyLE
    (bistellarCommonFacets_le_new A B)
  have hsource :
      orderedSSetHomOfFacetFamilyLE
          ((bistellarCommonFacets_le_old A B).trans
            (bistellarOldFacets_le_original hmove)) =
        commonToOld ≫
          SSet.Subcomplex.homOfLE (bistellarOldBicartSq hmove).le₃₄ := by
    rfl
  have htarget :
      orderedSSetHomOfFacetFamilyLE
          ((bistellarCommonFacets_le_new A B).trans
            (bistellarNewFacets_le_move facets A B)) =
        commonToNew ≫
          SSet.Subcomplex.homOfLE (bistellarNewBicartSq hmove).le₃₄ := by
    rfl
  have hlocal :
      SSet.toTop.map commonToOld ≫
          (TopCat.isoOfHomeo
            (bistellarMoveCompatibleLocalRealizationHomeomorph hmove)).hom =
        SSet.toTop.map commonToNew := by
    apply bistellarMoveCompatibleLocalRealizationHomeomorph_natural_of_ambient
    rfl
  rw [hsource, htarget, SSet.toTop.map_comp, SSet.toTop.map_comp,
    Category.assoc, bistellarMoveRealizationIso_hom_local,
    ← Category.assoc, hlocal]

/-- The stable facet family of a bistellar move consists of the unchanged outside together with
the common boundary of the old and new local balls. -/
def bistellarStableFacets
    (facets : Finset (Finset V)) (A B : Finset V) :
    Finset (Finset V) :=
  bistellarOutsideFacets facets A B ∪ bistellarCommonFacets A B

theorem bistellarStableFacets_le_original
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (hmove : IsBistellarMove facets dimension A B) :
    FacetFamilyLE (bistellarStableFacets facets A B) facets := by
  exact FacetFamilyLE.union
    (bistellarOutsideFacets_le_original facets A B)
    ((bistellarCommonFacets_le_old A B).trans
      (bistellarOldFacets_le_original hmove))

theorem bistellarStableFacets_le_move
    (facets : Finset (Finset V)) (A B : Finset V) :
    FacetFamilyLE (bistellarStableFacets facets A B)
      (bistellarMove facets A B) := by
  exact FacetFamilyLE.union
    (bistellarOutsideFacets_le_move facets A B)
    ((bistellarCommonFacets_le_new A B).trans
      (bistellarNewFacets_le_move facets A B))

/-- A global bistellar realization homeomorphism is the identity on the union of its unchanged
outside and its common local boundary. -/
theorem bistellarMoveRealizationIso_hom_stable
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (hmove : IsBistellarMove facets dimension A B) :
    SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          (bistellarStableFacets_le_original hmove)) ≫
        (bistellarMoveRealizationIso hmove).hom =
      SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          (bistellarStableFacets_le_move facets A B)) := by
  let outside := orderedSubcomplex (bistellarOutsideFacets facets A B)
  let common := orderedSubcomplex (bistellarCommonFacets A B)
  let stable := orderedSubcomplex (bistellarStableFacets facets A B)
  let sq : Lattice.BicartSq (outside ⊓ common) outside common stable := {
    sup_eq := by
      exact (orderedSubcomplex_union
        (bistellarOutsideFacets facets A B)
        (bistellarCommonFacets A B)).symm
    inf_eq := rfl
  }
  have hpushout := (SSet.Subcomplex.BicartSq.isPushout sq).map SSet.toTop
  apply hpushout.hom_ext
  · change SSet.toTop.map _ ≫
        (SSet.toTop.map _ ≫ (bistellarMoveRealizationIso hmove).hom) =
      SSet.toTop.map _ ≫ SSet.toTop.map _
    rw [← Category.assoc, ← SSet.toTop.map_comp,
      ← SSet.toTop.map_comp]
    exact bistellarMoveRealizationIso_hom_outside hmove
  · change SSet.toTop.map _ ≫
        (SSet.toTop.map _ ≫ (bistellarMoveRealizationIso hmove).hom) =
      SSet.toTop.map _ ≫ SSet.toTop.map _
    rw [← Category.assoc, ← SSet.toTop.map_comp,
      ← SSet.toTop.map_comp]
    exact bistellarMoveRealizationIso_hom_common hmove

/-- A bistellar realization homeomorphism is the identity on every subcomplex carried by the
stable union of the unchanged outside and common local boundary. -/
theorem bistellarMoveRealizationIso_hom_fixed_stable
    {facets fixed : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (hmove : IsBistellarMove facets dimension A B)
    (hfixed : FacetFamilyLE fixed (bistellarStableFacets facets A B)) :
    SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          (hfixed.trans (bistellarStableFacets_le_original hmove))) ≫
        (bistellarMoveRealizationIso hmove).hom =
      SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE
          (hfixed.trans (bistellarStableFacets_le_move facets A B))) := by
  let fixedToStable := orderedSSetHomOfFacetFamilyLE hfixed
  have hsource :
      orderedSSetHomOfFacetFamilyLE
          (hfixed.trans (bistellarStableFacets_le_original hmove)) =
        fixedToStable ≫
          orderedSSetHomOfFacetFamilyLE
            (bistellarStableFacets_le_original hmove) := by
    rfl
  have htarget :
      orderedSSetHomOfFacetFamilyLE
          (hfixed.trans (bistellarStableFacets_le_move facets A B)) =
        fixedToStable ≫
          orderedSSetHomOfFacetFamilyLE
            (bistellarStableFacets_le_move facets A B) := by
    rfl
  rw [hsource, htarget, SSet.toTop.map_comp, SSet.toTop.map_comp,
    Category.assoc, bistellarMoveRealizationIso_hom_stable]

/-- A fixed facet family lies in the stable relative-boundary region at every step of a
bistellar sequence. -/
def IsStableByBistellarMoveSequence
    (fixed facets : Finset (Finset V))
    (moves : List (BistellarMoveData V)) : Prop :=
  match moves with
  | [] => FacetFamilyLE fixed facets
  | move :: moves =>
      FacetFamilyLE fixed
          (bistellarStableFacets facets move.oldCore move.newCore) ∧
        IsStableByBistellarMoveSequence fixed
          (bistellarMove facets move.oldCore move.newCore) moves

theorem IsStableByBistellarMoveSequence.initialLE
    {fixed facets : Finset (Finset V)} {dimension : ℕ}
    {moves : List (BistellarMoveData V)}
    (hvalid : IsValidBistellarMoveSequence facets dimension moves)
    (hstable : IsStableByBistellarMoveSequence fixed facets moves) :
    FacetFamilyLE fixed facets := by
  cases moves with
  | nil => exact hstable
  | cons move moves =>
      exact hstable.1.trans
        (bistellarStableFacets_le_original hvalid.1)

theorem IsStableByBistellarMoveSequence.finalLE
    {fixed facets : Finset (Finset V)} {dimension : ℕ}
    {moves : List (BistellarMoveData V)}
    (hvalid : IsValidBistellarMoveSequence facets dimension moves)
    (hstable : IsStableByBistellarMoveSequence fixed facets moves) :
    FacetFamilyLE fixed (applyBistellarMoves facets moves) := by
  induction moves generalizing facets with
  | nil => exact hstable
  | cons move moves ih =>
      exact ih hvalid.2 hstable.2

/-- A valid bistellar sequence restricts to the identity on every facet family carried by the
stable relative-boundary region at every step. -/
theorem bistellarMoveSequenceRealizationIso_hom_fixed_stable
    {fixed facets : Finset (Finset V)} {dimension : ℕ}
    {moves : List (BistellarMoveData V)}
    (hvalid : IsValidBistellarMoveSequence facets dimension moves)
    (hstable : IsStableByBistellarMoveSequence fixed facets moves) :
    SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE (hstable.initialLE hvalid)) ≫
        (bistellarMoveSequenceRealizationIso
          facets dimension moves hvalid).hom =
      SSet.toTop.map
        (orderedSSetHomOfFacetFamilyLE (hstable.finalLE hvalid)) := by
  induction moves generalizing facets with
  | nil =>
      change SSet.toTop.map _ ≫ 𝟙 _ = SSet.toTop.map _
      rw [Category.comp_id]
      congr 1
  | cons move moves ih =>
      have hvalid' :
          IsBistellarMove facets dimension move.oldCore move.newCore ∧
            IsValidBistellarMoveSequence
              (bistellarMove facets move.oldCore move.newCore)
              dimension moves := by
        simpa only [IsValidBistellarMoveSequence] using hvalid
      have hstable' :
          FacetFamilyLE fixed
              (bistellarStableFacets facets move.oldCore move.newCore) ∧
            IsStableByBistellarMoveSequence fixed
              (bistellarMove facets move.oldCore move.newCore) moves := by
        simpa only [IsStableByBistellarMoveSequence] using hstable
      change SSet.toTop.map _ ≫
          ((bistellarMoveRealizationIso hvalid'.1).hom ≫
            (bistellarMoveSequenceRealizationIso
              (bistellarMove facets move.oldCore move.newCore)
              dimension moves hvalid'.2).hom) =
        SSet.toTop.map _
      rw [← Category.assoc,
        bistellarMoveRealizationIso_hom_fixed_stable
          hvalid'.1 hstable'.1]
      exact ih hvalid'.2 hstable'.2

end FiniteOrderedComplex

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem pathConnectedSpace_centralInterfaceRealization :
    PathConnectedSpace
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) := by
  letI : PathConnectedSpace (SphereSpace 1 × SphereSpace 1) := inferInstance
  exact centralInterfaceRealizationHomeomorphSphereOneProduct.symm.surjective.pathConnectedSpace
    centralInterfaceRealizationHomeomorphSphereOneProduct.symm.continuous

/-! ## The standard boundary-torus map is surjective on `π₁` -/

theorem standardTriangleBoundaryFacets_le_standardSevenVertexTorus :
    FacetFamilyLE standardTriangleBoundaryFacets standardSevenVertexTorusFacets := by
  unfold FacetFamilyLE IsFace
  decide

theorem standardTriangleBoundaryVertexZero :
    IsFace standardTriangleBoundaryFacets ({0} : Finset (Fin 7)) := by
  unfold IsFace
  decide

/-- The vertex `0` on the displayed core triangle, used to select one concrete core
basepoint before transporting surjectivity to the meridian basepoints. -/
def standardTriangleBoundaryCarrierBase :
    facetFamilyCarrier standardTriangleBoundaryFacets :=
  facetFamilyVertexOfIsFace 0 standardTriangleBoundaryVertexZero

theorem standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus :
    FacetFamilyLE standardSevenVertexTorusFacets
      standardSevenVertexSolidTorusFacets := by
  unfold FacetFamilyLE IsFace
  decide

theorem orderedStandardSevenVertexTorusFacets_le_solidTorus :
    FacetFamilyLE orderedStandardSevenVertexTorusFacets
      orderedStandardSevenVertexSolidTorusFacets := by
  exact mapFacets_facetFamilyLE
    centralInterfaceOrderCoordinate.symm.toEmbedding
    standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus

def orderedStandardSevenVertexTorusInclSolidTorus :
    orderedSSet orderedStandardSevenVertexTorusFacets ⟶
      orderedSSet orderedStandardSevenVertexSolidTorusFacets :=
  orderedSSetHomOfFacetFamilyLE
    orderedStandardSevenVertexTorusFacets_le_solidTorus

theorem orderedStandardSevenVertexCarrierHomeomorph_naturality :
    facetFamilyCarrierHomOfFacetFamilyLE
          orderedStandardSevenVertexTorusFacets_le_solidTorus ≫
        (TopCat.isoOfHomeo
          orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom =
      (TopCat.isoOfHomeo
          orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom ≫
        facetFamilyCarrierHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

theorem standardSevenVertexCarrierInclSolidTorus_realization_inv_naturality :
    facetFamilyCarrierHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets =
      orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexTorusFacets ≫
        SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) := by
  have hnatural := orderedRealizationToFacetFamilyCarrier_naturality
    standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus
  rw [← cancel_epi (TopCat.isoOfHomeo
    (orderedRealizationHomeomorphFacetFamilyCarrier
      standardSevenVertexTorusFacets)).hom]
  change orderedRealizationToFacetFamilyCarrier
      standardSevenVertexTorusFacets ≫
        (facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexSolidTorusFacets) =
    orderedRealizationToFacetFamilyCarrier
      standardSevenVertexTorusFacets ≫
        (orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets ≫
          SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus))
  calc
    _ = (orderedRealizationToFacetFamilyCarrier
          standardSevenVertexTorusFacets ≫
        facetFamilyCarrierHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets := by
      rw [Category.assoc]
    _ = (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) ≫
        orderedRealizationToFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets) ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets := by
      exact congrArg (fun k ↦ k ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets) hnatural.symm
    _ = SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) := by
      rw [Category.assoc,
        orderedRealizationToFacetFamilyCarrier_comp_fromCarrier,
        Category.comp_id]
    _ = orderedRealizationToFacetFamilyCarrier
          standardSevenVertexTorusFacets ≫
        (orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexTorusFacets ≫
          SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus)) := by
      rw [← Category.assoc,
        orderedRealizationToFacetFamilyCarrier_comp_fromCarrier,
        Category.id_comp]

theorem standardTriangleBoundaryFacets_le_standardSevenVertexSolidTorus :
    FacetFamilyLE standardTriangleBoundaryFacets
      standardSevenVertexSolidTorusFacets := by
  intro facet hfacet
  obtain ⟨torusFacet, htorusFacet, hfacetTorus⟩ :=
    standardTriangleBoundaryFacets_le_standardSevenVertexTorus facet hfacet
  obtain ⟨solidFacet, hsolidFacet, htorusSolid⟩ :=
    standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus
      torusFacet htorusFacet
  exact ⟨solidFacet, hsolidFacet, hfacetTorus.trans htorusSolid⟩

def standardTriangleBoundaryCarrierInclTorus :
    C(facetFamilyCarrier standardTriangleBoundaryFacets,
      facetFamilyCarrier standardSevenVertexTorusFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryFacets_le_standardSevenVertexTorus,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryFacets_le_standardSevenVertexTorus⟩

def standardSevenVertexTorusCarrierInclSolidTorus :
    C(facetFamilyCarrier standardSevenVertexTorusFacets,
      facetFamilyCarrier standardSevenVertexSolidTorusFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus⟩

def standardTriangleBoundaryCarrierInclSolidTorus :
    C(facetFamilyCarrier standardTriangleBoundaryFacets,
      facetFamilyCarrier standardSevenVertexSolidTorusFacets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryFacets_le_standardSevenVertexSolidTorus,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      standardTriangleBoundaryFacets_le_standardSevenVertexSolidTorus⟩

theorem standardTriangleBoundaryCarrierIncl_factor :
    standardSevenVertexTorusCarrierInclSolidTorus.comp
        standardTriangleBoundaryCarrierInclTorus =
      standardTriangleBoundaryCarrierInclSolidTorus := by
  rfl

theorem standardTriangleBoundaryCarrierInclSolidTorus_eq_invFun :
    standardTriangleBoundaryCarrierInclSolidTorus =
      standardSevenVertexSolidTorusCarrierHomotopyEquivTriangleBoundary.invFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem standardTriangleBoundaryCarrierInclSolidTorus_piOne_bijective
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 1) (x := x)
        (y := standardTriangleBoundaryCarrierInclSolidTorus x)
        standardTriangleBoundaryCarrierInclSolidTorus rfl) := by
  rw [standardTriangleBoundaryCarrierInclSolidTorus_eq_invFun]
  exact homotopyGroup_map_invFun_bijective
    standardSevenVertexSolidTorusCarrierHomotopyEquivTriangleBoundary x

theorem standardSevenVertexTorusCarrierInclSolidTorus_base_eq
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    standardSevenVertexTorusCarrierInclSolidTorus
        (standardTriangleBoundaryCarrierInclTorus x) =
      standardTriangleBoundaryCarrierInclSolidTorus x := by
  exact congrArg (fun f => f x) standardTriangleBoundaryCarrierIncl_factor

theorem standardSevenVertexTorusCarrierInclSolidTorus_piOne_surjective_at_core
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (x := standardTriangleBoundaryCarrierInclTorus x)
        (y := standardTriangleBoundaryCarrierInclSolidTorus x)
        standardSevenVertexTorusCarrierInclSolidTorus
        (standardSevenVertexTorusCarrierInclSolidTorus_base_eq x)) := by
  intro q
  obtain ⟨p, hp⟩ :=
    (standardTriangleBoundaryCarrierInclSolidTorus_piOne_bijective x).2 q
  refine ⟨HomotopyGroup.map standardTriangleBoundaryCarrierInclTorus rfl p, ?_⟩
  rw [HomotopyGroup.map_comp_apply]
  have hbaseComp :
      (standardSevenVertexTorusCarrierInclSolidTorus.comp
        standardTriangleBoundaryCarrierInclTorus) x =
        standardTriangleBoundaryCarrierInclSolidTorus x :=
    congrArg (fun f => f x) standardTriangleBoundaryCarrierIncl_factor
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    standardTriangleBoundaryCarrierIncl_factor hbaseComp rfl p
  exact hcongr.trans hp

def standardTriangleBoundaryInclTorus :
    orderedSSet standardTriangleBoundaryFacets ⟶
      orderedSSet standardSevenVertexTorusFacets :=
  orderedSSetHomOfFacetFamilyLE
    standardTriangleBoundaryFacets_le_standardSevenVertexTorus

def standardSevenVertexTorusInclSolidTorus :
    orderedSSet standardSevenVertexTorusFacets ⟶
      orderedSSet standardSevenVertexSolidTorusFacets :=
  orderedSSetHomOfFacetFamilyLE
    standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus

theorem standardSevenVertexTorusInclSolidTorus_realization_carrier_naturality :
    (⟨orderedRealizationHomeomorphFacetFamilyCarrier
        standardSevenVertexSolidTorusFacets,
      (orderedRealizationHomeomorphFacetFamilyCarrier
        standardSevenVertexSolidTorusFacets).continuous⟩ :
        C(SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets),
          facetFamilyCarrier standardSevenVertexSolidTorusFacets)).comp
        (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom =
      standardSevenVertexTorusCarrierInclSolidTorus.comp
        ⟨orderedRealizationHomeomorphFacetFamilyCarrier
            standardSevenVertexTorusFacets,
          (orderedRealizationHomeomorphFacetFamilyCarrier
            standardSevenVertexTorusFacets).continuous⟩ := by
  exact congrArg TopCat.Hom.hom
    (orderedRealizationToFacetFamilyCarrier_naturality
      standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus)

noncomputable def standardSevenVertexTorusRealizationCoreBase
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    SSet.toTop.obj (orderedSSet standardSevenVertexTorusFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    standardSevenVertexTorusFacets).symm
      (standardTriangleBoundaryCarrierInclTorus x)

theorem standardSevenVertexTorusInclSolidTorus_piOne_surjective_at_core
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (x := standardSevenVertexTorusRealizationCoreBase x)
        (y := (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom
          (standardSevenVertexTorusRealizationCoreBase x))
        (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom rfl) := by
  let sourceEquiv := orderedRealizationHomeomorphFacetFamilyCarrier
    standardSevenVertexTorusFacets
  let targetEquiv := orderedRealizationHomeomorphFacetFamilyCarrier
    standardSevenVertexSolidTorusFacets
  apply homotopyGroup_map_surjective_of_homeomorph_square
    (N := Fin 1)
    (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom
    standardSevenVertexTorusCarrierInclSolidTorus
    sourceEquiv targetEquiv
    standardSevenVertexTorusInclSolidTorus_realization_carrier_naturality
    (standardSevenVertexTorusRealizationCoreBase x)
    (standardTriangleBoundaryCarrierInclTorus x)
    (by simp [sourceEquiv, standardSevenVertexTorusRealizationCoreBase])
    (y' := standardTriangleBoundaryCarrierInclSolidTorus x)
    (standardSevenVertexTorusCarrierInclSolidTorus_base_eq x)
  exact standardSevenVertexTorusCarrierInclSolidTorus_piOne_surjective_at_core x

/-! ## Relative-boundary certificate for the zero-five bistellar reduction -/

def centralInterfaceExplicitFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3}, {1, 2, 8}, {1, 3, 7}, {1, 6, 7},
    {1, 8, 12}, {1, 6, 12}, {2, 7, 12}, {2, 6, 7},
    {2, 3, 12}, {2, 6, 8}, {3, 7, 8}, {7, 8, 12},
    {3, 6, 12}, {3, 6, 8} }

theorem centralInterfaceFacets_eq_explicit :
    centralInterfaceFacets = centralInterfaceExplicitFacets := by
  rw [← map_orderedStandardSevenVertexTorusFacets_central]
  decide

def zeroFiveInterfaceBistellarStageZeroFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3, 8}, {1, 3, 7, 8}, {1, 6, 7, 9},
    {1, 6, 9, 12}, {1, 7, 8, 9}, {1, 8, 9, 12},
    {2, 3, 6, 8}, {2, 3, 6, 9}, {2, 3, 9, 12},
    {2, 6, 7, 9}, {2, 7, 9, 12}, {3, 6, 9, 12},
    {7, 8, 9, 12} }

theorem pairwiseInterfaceFacets_zero_five_eq_stageZero :
    pairwiseInterfaceFacets 0 5 =
      zeroFiveInterfaceBistellarStageZeroFacets := by
  rw [← zeroFiveInterface_ball_decomposition]
  decide

def zeroFiveInterfaceBistellarStageOneFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3, 8}, {1, 3, 7, 8}, {1, 6, 7, 9},
    {1, 6, 9, 12}, {1, 7, 8, 9}, {1, 8, 9, 12},
    {2, 3, 6, 8}, {2, 6, 7, 9}, {2, 7, 9, 12},
    {7, 8, 9, 12}, {2, 3, 6, 12}, {2, 6, 9, 12} }

theorem zeroFiveInterfaceBistellarStageZero_move_eq_stageOne :
    bistellarMove zeroFiveInterfaceBistellarStageZeroFacets
        {9, 3} {2, 6, 12} =
      zeroFiveInterfaceBistellarStageOneFacets := by
  decide

def zeroFiveInterfaceBistellarStageTwoFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3, 8}, {1, 3, 7, 8}, {1, 6, 7, 9},
    {1, 6, 9, 12}, {1, 7, 8, 9}, {1, 8, 9, 12},
    {2, 3, 6, 8}, {7, 8, 9, 12}, {2, 3, 6, 12},
    {2, 6, 7, 12}, {6, 7, 9, 12} }

theorem zeroFiveInterfaceBistellarStageOne_move_eq_stageTwo :
    bistellarMove zeroFiveInterfaceBistellarStageOneFacets
        {9, 2} {6, 7, 12} =
      zeroFiveInterfaceBistellarStageTwoFacets := by
  decide

def zeroFiveInterfaceBistellarStageThreeFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3, 8}, {1, 3, 7, 8}, {1, 7, 8, 9},
    {1, 8, 9, 12}, {2, 3, 6, 8}, {7, 8, 9, 12},
    {2, 3, 6, 12}, {2, 6, 7, 12}, {1, 6, 7, 12},
    {1, 7, 9, 12} }

theorem zeroFiveInterfaceBistellarStageTwo_move_eq_stageThree :
    bistellarMove zeroFiveInterfaceBistellarStageTwoFacets
        {9, 6} {1, 7, 12} =
      zeroFiveInterfaceBistellarStageThreeFacets := by
  decide

def zeroFiveInterfaceBistellarStageFourFacets :
    Finset (Finset TrisectionVertex) :=
  { {1, 2, 3, 8}, {1, 3, 7, 8}, {2, 3, 6, 8},
    {2, 3, 6, 12}, {2, 6, 7, 12}, {1, 6, 7, 12},
    {1, 7, 8, 12} }

theorem zeroFiveInterfaceBistellarStageThree_move_eq_stageFour :
    bistellarMove zeroFiveInterfaceBistellarStageThreeFacets
        {9} {1, 7, 8, 12} =
      zeroFiveInterfaceBistellarStageFourFacets := by
  decide

theorem centralInterfaceExplicitFacets_le_stageZero_stable :
    FacetFamilyLE centralInterfaceExplicitFacets
      (bistellarStableFacets zeroFiveInterfaceBistellarStageZeroFacets
        {9, 3} {2, 6, 12}) := by
  intro facet hfacet
  simp only [centralInterfaceExplicitFacets, Finset.mem_insert,
    Finset.mem_singleton] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 9}, by decide, by decide⟩
  · exact ⟨{1, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{1, 6, 9, 12}, by decide, by decide⟩
  · exact ⟨{2, 7, 9, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 9}, by decide, by decide⟩
  · exact ⟨{2, 3, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{7, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

theorem centralInterfaceExplicitFacets_le_stageOne_stable :
    FacetFamilyLE centralInterfaceExplicitFacets
      (bistellarStableFacets zeroFiveInterfaceBistellarStageOneFacets
        {9, 2} {6, 7, 12}) := by
  intro facet hfacet
  simp only [centralInterfaceExplicitFacets, Finset.mem_insert,
    Finset.mem_singleton] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 9}, by decide, by decide⟩
  · exact ⟨{1, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{1, 6, 9, 12}, by decide, by decide⟩
  · exact ⟨{2, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{7, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

theorem centralInterfaceExplicitFacets_le_stageTwo_stable :
    FacetFamilyLE centralInterfaceExplicitFacets
      (bistellarStableFacets zeroFiveInterfaceBistellarStageTwoFacets
        {9, 6} {1, 7, 12}) := by
  intro facet hfacet
  simp only [centralInterfaceExplicitFacets, Finset.mem_insert,
    Finset.mem_singleton] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 6, 7}, by decide, by decide⟩
  · exact ⟨{1, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{1, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{7, 8, 9, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

theorem centralInterfaceExplicitFacets_le_stageThree_stable :
    FacetFamilyLE centralInterfaceExplicitFacets
      (bistellarStableFacets zeroFiveInterfaceBistellarStageThreeFacets
        {9} {1, 7, 8, 12}) := by
  intro facet hfacet
  simp only [centralInterfaceExplicitFacets, Finset.mem_insert,
    Finset.mem_singleton] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{1, 8, 12}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{7, 8, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

theorem centralInterfaceExplicitFacets_le_stageFour :
    FacetFamilyLE centralInterfaceExplicitFacets
      zeroFiveInterfaceBistellarStageFourFacets := by
  intro facet hfacet
  simp only [centralInterfaceExplicitFacets, Finset.mem_insert,
    Finset.mem_singleton] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 3, 8}, by decide, by decide⟩
  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{1, 7, 8, 12}, by decide, by decide⟩
  · exact ⟨{1, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 6, 7, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

  · exact ⟨{1, 3, 7, 8}, by decide, by decide⟩
  · exact ⟨{1, 7, 8, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 12}, by decide, by decide⟩
  · exact ⟨{2, 3, 6, 8}, by decide, by decide⟩

theorem zeroFiveInterfaceBistellarSolidTorusMoves_stable_central :
    IsStableByBistellarMoveSequence centralInterfaceFacets
      (pairwiseInterfaceFacets 0 5)
      zeroFiveInterfaceBistellarSolidTorusMoves := by
  simp only [zeroFiveInterfaceBistellarSolidTorusMoves,
    zeroFiveInterfaceBallTwoBaseBistellarMoves,
    coneBistellarMoveData, IsStableByBistellarMoveSequence,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [centralInterfaceFacets_eq_explicit,
    pairwiseInterfaceFacets_zero_five_eq_stageZero,
    zeroFiveInterfaceBistellarStageZero_move_eq_stageOne,
    zeroFiveInterfaceBistellarStageOne_move_eq_stageTwo,
    zeroFiveInterfaceBistellarStageTwo_move_eq_stageThree,
    zeroFiveInterfaceBistellarStageThree_move_eq_stageFour]
  exact ⟨centralInterfaceExplicitFacets_le_stageZero_stable,
    centralInterfaceExplicitFacets_le_stageOne_stable,
    centralInterfaceExplicitFacets_le_stageTwo_stable,
    centralInterfaceExplicitFacets_le_stageThree_stable,
    centralInterfaceExplicitFacets_le_stageFour⟩

theorem centralInterfaceFacets_le_zeroFiveBistellarSolidTorusResult :
    FacetFamilyLE centralInterfaceFacets
      zeroFiveInterfaceBistellarSolidTorusResult := by
  rw [← map_orderedStandardSevenVertexTorusFacets_central,
    ← map_orderedStandardSevenVertexSolidTorusFacets_result]
  exact mapFacets_facetFamilyLE centralInterfaceOrderEmbedding.toEmbedding
    orderedStandardSevenVertexTorusFacets_le_solidTorus

def centralInterfaceInclZeroFiveBistellarSolidTorusResult :
    orderedSSet centralInterfaceFacets ⟶
      orderedSSet zeroFiveInterfaceBistellarSolidTorusResult :=
  orderedSSetHomOfFacetFamilyLE
    centralInterfaceFacets_le_zeroFiveBistellarSolidTorusResult

theorem orderedStandardSevenVertexSSetIso_inv_naturality :
    centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        orderedStandardSevenVertexSolidTorusSSetIsoResult.inv =
      orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
        orderedStandardSevenVertexTorusInclSolidTorus := by
  let mappedLE := mapFacets_facetFamilyLE
    centralInterfaceOrderEmbedding.toEmbedding
    orderedStandardSevenVertexTorusFacets_le_solidTorus
  have heq := orderedSSetHomOfFacetFamilyLE_eqToIso_inv_naturality
    map_orderedStandardSevenVertexTorusFacets_central
    map_orderedStandardSevenVertexSolidTorusFacets_result
    mappedLE centralInterfaceFacets_le_zeroFiveBistellarSolidTorusResult
  have hreindex := orderedSSetMapFacetsIso_inv_naturality
    centralInterfaceOrderEmbedding
    orderedStandardSevenVertexTorusFacets_le_solidTorus
  change
    orderedSSetHomOfFacetFamilyLE
          centralInterfaceFacets_le_zeroFiveBistellarSolidTorusResult ≫
        ((SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
            map_orderedStandardSevenVertexSolidTorusFacets_result)).inv ≫
          (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
            orderedStandardSevenVertexSolidTorusFacets).inv) =
      ((SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
            map_orderedStandardSevenVertexTorusFacets_central)).inv ≫
          (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
            orderedStandardSevenVertexTorusFacets).inv) ≫
        orderedSSetHomOfFacetFamilyLE
          orderedStandardSevenVertexTorusFacets_le_solidTorus
  calc
    _ = (orderedSSetHomOfFacetFamilyLE
          centralInterfaceFacets_le_zeroFiveBistellarSolidTorusResult ≫
        (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          map_orderedStandardSevenVertexSolidTorusFacets_result)).inv) ≫
        (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
          orderedStandardSevenVertexSolidTorusFacets).inv := by
      rw [Category.assoc]
    _ = ((SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          map_orderedStandardSevenVertexTorusFacets_central)).inv ≫
        orderedSSetHomOfFacetFamilyLE mappedLE) ≫
        (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
          orderedStandardSevenVertexSolidTorusFacets).inv := by
      rw [heq]
    _ = (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          map_orderedStandardSevenVertexTorusFacets_central)).inv ≫
        (orderedSSetHomOfFacetFamilyLE mappedLE ≫
          (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
            orderedStandardSevenVertexSolidTorusFacets).inv) := by
      rw [Category.assoc]
    _ = (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          map_orderedStandardSevenVertexTorusFacets_central)).inv ≫
        ((orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
            orderedStandardSevenVertexTorusFacets).inv ≫
          orderedSSetHomOfFacetFamilyLE
            orderedStandardSevenVertexTorusFacets_le_solidTorus) := by
      rw [hreindex]
    _ = ((SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          map_orderedStandardSevenVertexTorusFacets_central)).inv ≫
        (orderedSSetMapFacetsIso centralInterfaceOrderEmbedding
          orderedStandardSevenVertexTorusFacets).inv) ≫
        orderedSSetHomOfFacetFamilyLE
          orderedStandardSevenVertexTorusFacets_le_solidTorus := by
      rw [Category.assoc]

theorem orderedStandardSevenVertexRealizationIso_inv_naturality :
    SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        SSet.toTop.map
          orderedStandardSevenVertexSolidTorusSSetIsoResult.inv =
      SSet.toTop.map
          orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
        SSet.toTop.map orderedStandardSevenVertexTorusInclSolidTorus := by
  have h := congrArg (fun k ↦ SSet.toTop.map k)
    orderedStandardSevenVertexSSetIso_inv_naturality
  simpa only [Functor.map_comp] using h

theorem zeroFiveInterfaceBistellarSolidTorusResult_component_naturality :
    SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        (((SSet.toTop.map
              orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexSolidTorusFacets) =
      (((SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets) ≫
        SSet.toTop.map standardSevenVertexTorusInclSolidTorus := by
  have h₁ := orderedStandardSevenVertexRealizationIso_inv_naturality
  have h₂ :
      SSet.toTop.map orderedStandardSevenVertexTorusInclSolidTorus ≫
          orderedRealizationToFacetFamilyCarrier
            orderedStandardSevenVertexSolidTorusFacets =
        orderedRealizationToFacetFamilyCarrier
            orderedStandardSevenVertexTorusFacets ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            orderedStandardSevenVertexTorusFacets_le_solidTorus := by
    exact orderedRealizationToFacetFamilyCarrier_naturality
      orderedStandardSevenVertexTorusFacets_le_solidTorus
  have h₃ := orderedStandardSevenVertexCarrierHomeomorph_naturality
  have h₄ :
      facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexSolidTorusFacets =
        orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets ≫
          SSet.toTop.map standardSevenVertexTorusInclSolidTorus := by
    exact standardSevenVertexCarrierInclSolidTorus_realization_inv_naturality
  have h₁₂ :
      SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
          (SSet.toTop.map
              orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets) =
        (SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            orderedStandardSevenVertexTorusFacets_le_solidTorus := by
    calc
      _ = (SSet.toTop.map
            centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
          SSet.toTop.map
            orderedStandardSevenVertexSolidTorusSSetIsoResult.inv) ≫
          orderedRealizationToFacetFamilyCarrier
            orderedStandardSevenVertexSolidTorusFacets := by
        simp only [Category.assoc]
      _ = (SSet.toTop.map
            orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
          SSet.toTop.map orderedStandardSevenVertexTorusInclSolidTorus) ≫
          orderedRealizationToFacetFamilyCarrier
            orderedStandardSevenVertexSolidTorusFacets := by rw [h₁]
      _ = SSet.toTop.map
            orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
          (SSet.toTop.map orderedStandardSevenVertexTorusInclSolidTorus ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets) := by
        simp only [Category.assoc]
      _ = SSet.toTop.map
            orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
          (orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets ≫
            facetFamilyCarrierHomOfFacetFamilyLE
              orderedStandardSevenVertexTorusFacets_le_solidTorus) := by
        rw [h₂]
      _ = (SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            orderedStandardSevenVertexTorusFacets_le_solidTorus := by
        simp only [Category.assoc]
  have h₁₂₃ :
      SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
          ((SSet.toTop.map
                orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
              orderedRealizationToFacetFamilyCarrier
                orderedStandardSevenVertexSolidTorusFacets) ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom) =
        ((SSet.toTop.map
                orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
              orderedRealizationToFacetFamilyCarrier
                orderedStandardSevenVertexTorusFacets) ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus := by
    calc
      _ = (SSet.toTop.map
            centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
          (SSet.toTop.map
              orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets)) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom := by
        simp only [Category.assoc]
      _ = ((SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            orderedStandardSevenVertexTorusFacets_le_solidTorus) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom := by
        rw [h₁₂]
      _ = (SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          (facetFamilyCarrierHomOfFacetFamilyLE
              orderedStandardSevenVertexTorusFacets_le_solidTorus ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom) := by
        simp only [Category.assoc]
      _ = (SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          ((TopCat.isoOfHomeo
              orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom ≫
            facetFamilyCarrierHomOfFacetFamilyLE
              standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) := by
        rw [h₃]
      _ = ((SSet.toTop.map
                orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
              orderedRealizationToFacetFamilyCarrier
                orderedStandardSevenVertexTorusFacets) ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus := by
        simp only [Category.assoc]
  calc
    _ = (SSet.toTop.map
          centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        ((SSet.toTop.map
              orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom)) ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets := by
      simp only [Category.assoc]
    _ = (((SSet.toTop.map
                orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
              orderedRealizationToFacetFamilyCarrier
                orderedStandardSevenVertexTorusFacets) ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus) ≫
        orderedRealizationFromFacetFamilyCarrier
          standardSevenVertexSolidTorusFacets := by rw [h₁₂₃]
    _ = ((SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
        (facetFamilyCarrierHomOfFacetFamilyLE
            standardSevenVertexTorusFacets_le_standardSevenVertexSolidTorus ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexSolidTorusFacets) := by
      simp only [Category.assoc]
    _ = ((SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
        (orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets ≫
          SSet.toTop.map standardSevenVertexTorusInclSolidTorus) := by
      rw [h₄]
    _ = (((SSet.toTop.map
                orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
              orderedRealizationToFacetFamilyCarrier
                orderedStandardSevenVertexTorusFacets) ≫
            (TopCat.isoOfHomeo
              orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets) ≫
        SSet.toTop.map standardSevenVertexTorusInclSolidTorus := by
      simp only [Category.assoc]

theorem zeroFiveInterfaceBistellarSolidTorusResult_homeomorph_naturality :
    SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard).hom =
      (TopCat.isoOfHomeo
          centralInterfaceRealizationHomeomorphStandardSevenVertexTorus).hom ≫
        SSet.toTop.map standardSevenVertexTorusInclSolidTorus := by
  change
    SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        (((SSet.toTop.map
              orderedStandardSevenVertexSolidTorusSSetIsoResult.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexSolidTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexSolidTorusCarrierHomeomorphStandard).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexSolidTorusFacets) =
      (((SSet.toTop.map
              orderedStandardSevenVertexTorusSSetIsoCentralInterface.inv ≫
            orderedRealizationToFacetFamilyCarrier
              orderedStandardSevenVertexTorusFacets) ≫
          (TopCat.isoOfHomeo
            orderedStandardSevenVertexTorusCarrierHomeomorphStandard).hom) ≫
          orderedRealizationFromFacetFamilyCarrier
            standardSevenVertexTorusFacets) ≫
        SSet.toTop.map standardSevenVertexTorusInclSolidTorus
  exact zeroFiveInterfaceBistellarSolidTorusResult_component_naturality

theorem zeroFiveInterfaceBistellarSolidTorusRealizationIso_hom_central :
    SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
        zeroFiveInterfaceBistellarSolidTorusRealizationIso.hom =
      SSet.toTop.map centralInterfaceInclZeroFiveBistellarSolidTorusResult := by
  have h := bistellarMoveSequenceRealizationIso_hom_fixed_stable
    zeroFiveInterfaceBistellarSolidTorusMoves_valid
    zeroFiveInterfaceBistellarSolidTorusMoves_stable_central
  simpa only [zeroFiveCentralInterfaceInclPairwise,
    zeroFiveInterfaceBistellarSolidTorusRealizationIso,
    zeroFiveInterfaceBistellarSolidTorusResult,
    centralInterfaceInclZeroFiveBistellarSolidTorusResult] using h

theorem zeroFiveCentralInterfaceInclPairwise_homeomorph_naturality :
    SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus).hom =
      (TopCat.isoOfHomeo
          centralInterfaceRealizationHomeomorphStandardSevenVertexTorus).hom ≫
        SSet.toTop.map standardSevenVertexTorusInclSolidTorus := by
  change SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
      (zeroFiveInterfaceBistellarSolidTorusRealizationIso.hom ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard).hom) = _
  calc
    _ = (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
          zeroFiveInterfaceBistellarSolidTorusRealizationIso.hom) ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard).hom := by
      simp only [Category.assoc]
    _ = SSet.toTop.map
          centralInterfaceInclZeroFiveBistellarSolidTorusResult ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceBistellarSolidTorusResultRealizationHomeomorphStandard).hom := by
      rw [zeroFiveInterfaceBistellarSolidTorusRealizationIso_hom_central]
    _ = _ :=
      zeroFiveInterfaceBistellarSolidTorusResult_homeomorph_naturality

theorem zeroFiveCentralInterfaceInclPairwise_continuousMap_naturality :
    (⟨zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus,
      zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus.continuous⟩ :
        C(SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)),
          SSet.toTop.obj (orderedSSet standardSevenVertexSolidTorusFacets))).comp
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom =
      (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom.comp
        ⟨centralInterfaceRealizationHomeomorphStandardSevenVertexTorus,
          centralInterfaceRealizationHomeomorphStandardSevenVertexTorus.continuous⟩ := by
  exact congrArg TopCat.Hom.hom
    zeroFiveCentralInterfaceInclPairwise_homeomorph_naturality

noncomputable def zeroFiveCentralInterfaceRealizationCoreBase
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  centralInterfaceRealizationHomeomorphStandardSevenVertexTorus.symm
    (standardSevenVertexTorusRealizationCoreBase x)

theorem zeroFiveCentralInterfaceInclPairwise_piOne_surjective_at_core
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (x := zeroFiveCentralInterfaceRealizationCoreBase x)
        (y := (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
          (zeroFiveCentralInterfaceRealizationCoreBase x))
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom rfl) := by
  let sourceEquiv :=
    centralInterfaceRealizationHomeomorphStandardSevenVertexTorus
  let targetEquiv :=
    zeroFiveInterfaceRealizationHomeomorphStandardSevenVertexSolidTorus
  apply homotopyGroup_map_surjective_of_homeomorph_square
    (N := Fin 1)
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
    (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom
    sourceEquiv targetEquiv
    zeroFiveCentralInterfaceInclPairwise_continuousMap_naturality
    (zeroFiveCentralInterfaceRealizationCoreBase x)
    (standardSevenVertexTorusRealizationCoreBase x)
    (by simp [sourceEquiv, zeroFiveCentralInterfaceRealizationCoreBase])
    (y' := (SSet.toTop.map standardSevenVertexTorusInclSolidTorus).hom
      (standardSevenVertexTorusRealizationCoreBase x))
    rfl
  exact standardSevenVertexTorusInclSolidTorus_piOne_surjective_at_core x

/-! ## Cyclic transport to the five-four and four-zero interfaces -/

theorem trisectionRotationEquiv_map_centralInterface :
    mapFacets trisectionRotationEquiv.toEmbedding centralInterfaceFacets =
      centralInterfaceFacets := by
  rw [centralInterfaceFacets_eq_explicit]
  decide

noncomputable def centralInterfaceRealizationRotation :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) ≃ₜ
      SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  (orderedRealizationReindexHomeomorph trisectionRotationEquiv
      centralInterfaceFacets).trans
    (orderedRealizationHomeomorphOfFacetEq
      trisectionRotationEquiv_map_centralInterface)

theorem zeroFiveCentralInterfaceFacetsLE :
    FacetFamilyLE centralInterfaceFacets (pairwiseInterfaceFacets 0 5) :=
  centralInterfaceFacets_le_pairwiseInterface
    0 (by decide) 5 (by decide) (by decide)

theorem fiveFourCentralInterfaceFacetsLE :
    FacetFamilyLE centralInterfaceFacets (pairwiseInterfaceFacets 5 4) :=
  centralInterfaceFacets_le_pairwiseInterface
    5 (by decide) 4 (by decide) (by decide)

theorem trisectionRotationEquiv_eqToIso_inclusion_naturality :
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE trisectionRotationEquiv.toEmbedding
            zeroFiveCentralInterfaceFacetsLE)) ≫
        SSet.toTop.map (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_zeroFiveInterface)).hom =
      SSet.toTop.map (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_centralInterface)).hom ≫
        SSet.toTop.map fiveFourCentralInterfaceInclPairwise := by
  have h := orderedSSetHomOfFacetFamilyLE_eqToIso_naturality
    trisectionRotationEquiv_map_centralInterface
    trisectionRotationEquiv_map_zeroFiveInterface
    (mapFacets_facetFamilyLE trisectionRotationEquiv.toEmbedding
      zeroFiveCentralInterfaceFacetsLE)
    fiveFourCentralInterfaceFacetsLE
  have hmap := congrArg (fun k ↦ SSet.toTop.map k) h
  simpa only [Functor.map_comp, fiveFourCentralInterfaceInclPairwise] using hmap

theorem zeroFiveCentralInterfaceInclPairwise_rotation_naturality :
    SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceRealizationHomeomorphFiveFour).hom =
      (TopCat.isoOfHomeo centralInterfaceRealizationRotation).hom ≫
        SSet.toTop.map fiveFourCentralInterfaceInclPairwise := by
  have hreindex := orderedRealizationReindexHomeomorph_naturality
    trisectionRotationEquiv zeroFiveCentralInterfaceFacetsLE
  have heq := trisectionRotationEquiv_eqToIso_inclusion_naturality
  have hcomp := comp_commuting_squares hreindex heq
  change SSet.toTop.map zeroFiveCentralInterfaceInclPairwise ≫
      ((TopCat.isoOfHomeo
          (orderedRealizationReindexHomeomorph trisectionRotationEquiv
            (pairwiseInterfaceFacets 0 5))).hom ≫
        SSet.toTop.map (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex
            trisectionRotationEquiv_map_zeroFiveInterface)).hom) =
    ((TopCat.isoOfHomeo
        (orderedRealizationReindexHomeomorph trisectionRotationEquiv
          centralInterfaceFacets)).hom ≫
      SSet.toTop.map (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_centralInterface)).hom) ≫
      SSet.toTop.map fiveFourCentralInterfaceInclPairwise
  simpa only [zeroFiveCentralInterfaceInclPairwise] using hcomp

theorem fourZeroCentralInterfaceFacetsLE :
    FacetFamilyLE centralInterfaceFacets (pairwiseInterfaceFacets 4 0) :=
  centralInterfaceFacets_le_pairwiseInterface
    4 (by decide) 0 (by decide) (by decide)

theorem trisectionRotationEquiv_eqToIso_fiveFour_inclusion_naturality :
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (mapFacets_facetFamilyLE trisectionRotationEquiv.toEmbedding
            fiveFourCentralInterfaceFacetsLE)) ≫
        SSet.toTop.map (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_fiveFourInterface)).hom =
      SSet.toTop.map (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_centralInterface)).hom ≫
        SSet.toTop.map fourZeroCentralInterfaceInclPairwise := by
  have h := orderedSSetHomOfFacetFamilyLE_eqToIso_naturality
    trisectionRotationEquiv_map_centralInterface
    trisectionRotationEquiv_map_fiveFourInterface
    (mapFacets_facetFamilyLE trisectionRotationEquiv.toEmbedding
      fiveFourCentralInterfaceFacetsLE)
    fourZeroCentralInterfaceFacetsLE
  have hmap := congrArg (fun k ↦ SSet.toTop.map k) h
  simpa only [Functor.map_comp, fourZeroCentralInterfaceInclPairwise] using hmap

theorem fiveFourCentralInterfaceInclPairwise_rotation_naturality :
    SSet.toTop.map fiveFourCentralInterfaceInclPairwise ≫
        (TopCat.isoOfHomeo
          fiveFourInterfaceRealizationHomeomorphFourZero).hom =
      (TopCat.isoOfHomeo centralInterfaceRealizationRotation).hom ≫
        SSet.toTop.map fourZeroCentralInterfaceInclPairwise := by
  have hreindex := orderedRealizationReindexHomeomorph_naturality
    trisectionRotationEquiv fiveFourCentralInterfaceFacetsLE
  have heq :=
    trisectionRotationEquiv_eqToIso_fiveFour_inclusion_naturality
  have hcomp := comp_commuting_squares hreindex heq
  change SSet.toTop.map fiveFourCentralInterfaceInclPairwise ≫
      ((TopCat.isoOfHomeo
          (orderedRealizationReindexHomeomorph trisectionRotationEquiv
            (pairwiseInterfaceFacets 5 4))).hom ≫
        SSet.toTop.map (SSet.Subcomplex.eqToIso
          (congrArg orderedSubcomplex
            trisectionRotationEquiv_map_fiveFourInterface)).hom) =
    ((TopCat.isoOfHomeo
        (orderedRealizationReindexHomeomorph trisectionRotationEquiv
          centralInterfaceFacets)).hom ≫
      SSet.toTop.map (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          trisectionRotationEquiv_map_centralInterface)).hom) ≫
      SSet.toTop.map fourZeroCentralInterfaceInclPairwise
  simpa only [fiveFourCentralInterfaceInclPairwise] using hcomp

theorem fiveFourCentralInterfaceInclPairwise_rotation_inv_naturality :
    SSet.toTop.map fiveFourCentralInterfaceInclPairwise ≫
        (TopCat.isoOfHomeo
          zeroFiveInterfaceRealizationHomeomorphFiveFour).inv =
      (TopCat.isoOfHomeo centralInterfaceRealizationRotation).inv ≫
        SSet.toTop.map zeroFiveCentralInterfaceInclPairwise := by
  exact iso_square_inv
    (TopCat.isoOfHomeo centralInterfaceRealizationRotation)
    (TopCat.isoOfHomeo zeroFiveInterfaceRealizationHomeomorphFiveFour)
    zeroFiveCentralInterfaceInclPairwise_rotation_naturality

theorem fourZeroCentralInterfaceInclPairwise_rotation_inv_naturality :
    SSet.toTop.map fourZeroCentralInterfaceInclPairwise ≫
        (TopCat.isoOfHomeo
          fiveFourInterfaceRealizationHomeomorphFourZero).inv =
      (TopCat.isoOfHomeo centralInterfaceRealizationRotation).inv ≫
        SSet.toTop.map fiveFourCentralInterfaceInclPairwise := by
  exact iso_square_inv
    (TopCat.isoOfHomeo centralInterfaceRealizationRotation)
    (TopCat.isoOfHomeo fiveFourInterfaceRealizationHomeomorphFourZero)
    fiveFourCentralInterfaceInclPairwise_rotation_naturality

theorem fiveFourCentralInterfaceInclPairwise_rotation_inv_continuousMap_naturality :
    (⟨zeroFiveInterfaceRealizationHomeomorphFiveFour.symm,
      zeroFiveInterfaceRealizationHomeomorphFiveFour.symm.continuous⟩ :
        C(SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)),
          SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)))).comp
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom =
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom.comp
        ⟨centralInterfaceRealizationRotation.symm,
          centralInterfaceRealizationRotation.symm.continuous⟩ := by
  exact congrArg TopCat.Hom.hom
    fiveFourCentralInterfaceInclPairwise_rotation_inv_naturality

theorem fourZeroCentralInterfaceInclPairwise_rotation_inv_continuousMap_naturality :
    (⟨fiveFourInterfaceRealizationHomeomorphFourZero.symm,
      fiveFourInterfaceRealizationHomeomorphFourZero.symm.continuous⟩ :
        C(SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0)),
          SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)))).comp
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom =
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom.comp
        ⟨centralInterfaceRealizationRotation.symm,
          centralInterfaceRealizationRotation.symm.continuous⟩ := by
  exact congrArg TopCat.Hom.hom
    fourZeroCentralInterfaceInclPairwise_rotation_inv_naturality

noncomputable def fiveFourCentralInterfaceRealizationCoreBase
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  centralInterfaceRealizationRotation
    (zeroFiveCentralInterfaceRealizationCoreBase x)

theorem fiveFourCentralInterfaceInclPairwise_piOne_surjective_at_core
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (x := fiveFourCentralInterfaceRealizationCoreBase x)
        (y := (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
          (fiveFourCentralInterfaceRealizationCoreBase x))
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom rfl) := by
  let sourceEquiv := centralInterfaceRealizationRotation.symm
  let targetEquiv :=
    zeroFiveInterfaceRealizationHomeomorphFiveFour.symm
  apply homotopyGroup_map_surjective_of_homeomorph_square
    (N := Fin 1)
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
    sourceEquiv targetEquiv
    fiveFourCentralInterfaceInclPairwise_rotation_inv_continuousMap_naturality
    (fiveFourCentralInterfaceRealizationCoreBase x)
    (zeroFiveCentralInterfaceRealizationCoreBase x)
    (by simp [sourceEquiv, fiveFourCentralInterfaceRealizationCoreBase])
    (y' := (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      (zeroFiveCentralInterfaceRealizationCoreBase x))
    rfl
  exact zeroFiveCentralInterfaceInclPairwise_piOne_surjective_at_core x

noncomputable def fourZeroCentralInterfaceRealizationCoreBase
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) :=
  centralInterfaceRealizationRotation
    (fiveFourCentralInterfaceRealizationCoreBase x)

theorem fourZeroCentralInterfaceInclPairwise_piOne_surjective_at_core
    (x : facetFamilyCarrier standardTriangleBoundaryFacets) :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (x := fourZeroCentralInterfaceRealizationCoreBase x)
        (y := (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
          (fourZeroCentralInterfaceRealizationCoreBase x))
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom rfl) := by
  let sourceEquiv := centralInterfaceRealizationRotation.symm
  let targetEquiv :=
    fiveFourInterfaceRealizationHomeomorphFourZero.symm
  apply homotopyGroup_map_surjective_of_homeomorph_square
    (N := Fin 1)
    (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
    sourceEquiv targetEquiv
    fourZeroCentralInterfaceInclPairwise_rotation_inv_continuousMap_naturality
    (fourZeroCentralInterfaceRealizationCoreBase x)
    (fiveFourCentralInterfaceRealizationCoreBase x)
    (by simp [sourceEquiv, fourZeroCentralInterfaceRealizationCoreBase])
    (y' := (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      (fiveFourCentralInterfaceRealizationCoreBase x))
    rfl
  exact fiveFourCentralInterfaceInclPairwise_piOne_surjective_at_core x

/-! ## Higher homotopy-group maps -/

/-- Every inclusion from the central interface to a pairwise interface induces a bijection in
each degree above one, at every basepoint.  Both groups are trivial in those degrees. -/
theorem centralInterfaceInclPairwise_higher_pi_bijective
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b)
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin (k + 2)) (x := x)
        (y := (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (centralInterfaceFacets_le_pairwiseInterface a ha b hb hab))).hom x)
        (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (centralInterfaceFacets_le_pairwiseInterface a ha b hb hab))).hom
        rfl) := by
  letI : Subsingleton
      (HomotopyGroup.Pi (k + 2)
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) x) :=
    centralInterface_higher_homotopy_subsingleton k x
  letI : Subsingleton
      (HomotopyGroup.Pi (k + 2)
        (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets a b)))
        ((SSet.toTop.map (orderedSSetHomOfFacetFamilyLE
          (centralInterfaceFacets_le_pairwiseInterface a ha b hb hab))).hom x)) :=
    pairwiseInterface_higher_homotopy_subsingleton
      a ha b hb hab k _
  exact homotopyGroup_map_bijective_of_subsingleton _ rfl

theorem zeroFiveCentralInterfaceInclPairwise_higher_pi_bijective
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin (k + 2))
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        (x := x) rfl) := by
  simpa only [zeroFiveCentralInterfaceInclPairwise] using
    centralInterfaceInclPairwise_higher_pi_bijective
      0 (by decide) 5 (by decide) (by decide) k x

theorem fiveFourCentralInterfaceInclPairwise_higher_pi_bijective
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin (k + 2))
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        (x := x) rfl) := by
  simpa only [fiveFourCentralInterfaceInclPairwise] using
    centralInterfaceInclPairwise_higher_pi_bijective
      5 (by decide) 4 (by decide) (by decide) k x

theorem fourZeroCentralInterfaceInclPairwise_higher_pi_bijective
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin (k + 2))
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        (x := x) rfl) := by
  simpa only [fourZeroCentralInterfaceInclPairwise] using
    centralInterfaceInclPairwise_higher_pi_bijective
      4 (by decide) 0 (by decide) (by decide) k x

/-! ## Surjective noninjective maps at the meridian basepoints -/

/-- The zero-five central-to-pairwise map is surjective at the exact basepoint used by its
explicit nonzero meridian kernel class. -/
theorem zeroFiveCentralInterfaceInclPairwise_piOne_map_surjective :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        zeroFiveCentralRealizationBase_map_pairwise_eq) := by
  letI : PathConnectedSpace
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :=
    pathConnectedSpace_centralInterfaceRealization
  apply homotopyGroup_map_surjective_of_base_eq
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
    zeroFiveCentralRealizationBase_map_pairwise_eq
  apply homotopyGroup_map_surjective_of_pathConnected
    (x := zeroFiveCentralInterfaceRealizationCoreBase
      standardTriangleBoundaryCarrierBase)
  exact zeroFiveCentralInterfaceInclPairwise_piOne_surjective_at_core
    standardTriangleBoundaryCarrierBase

/-- The five-four central-to-pairwise map is surjective at the exact basepoint used by its
explicit nonzero meridian kernel class. -/
theorem fiveFourCentralInterfaceInclPairwise_piOne_map_surjective :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        fiveFourCentralRealizationBase_map_pairwise_eq) := by
  letI : PathConnectedSpace
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :=
    pathConnectedSpace_centralInterfaceRealization
  apply homotopyGroup_map_surjective_of_base_eq
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
    fiveFourCentralRealizationBase_map_pairwise_eq
  apply homotopyGroup_map_surjective_of_pathConnected
    (x := fiveFourCentralInterfaceRealizationCoreBase
      standardTriangleBoundaryCarrierBase)
  exact fiveFourCentralInterfaceInclPairwise_piOne_surjective_at_core
    standardTriangleBoundaryCarrierBase

/-- The four-zero central-to-pairwise map is surjective at the exact basepoint used by its
explicit nonzero meridian kernel class. -/
theorem fourZeroCentralInterfaceInclPairwise_piOne_map_surjective :
    Function.Surjective
      (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        fourZeroCentralRealizationBase_map_pairwise_eq) := by
  letI : PathConnectedSpace
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :=
    pathConnectedSpace_centralInterfaceRealization
  apply homotopyGroup_map_surjective_of_base_eq
    (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
    fourZeroCentralRealizationBase_map_pairwise_eq
  apply homotopyGroup_map_surjective_of_pathConnected
    (x := fourZeroCentralInterfaceRealizationCoreBase
      standardTriangleBoundaryCarrierBase)
  exact fourZeroCentralInterfaceInclPairwise_piOne_surjective_at_core
    standardTriangleBoundaryCarrierBase

/-- At its meridian basepoint, the zero-five filling map is surjective but not injective. -/
theorem zeroFiveCentralInterfaceInclPairwise_piOne_map_surjective_not_injective :
    Function.Surjective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
          zeroFiveCentralRealizationBase_map_pairwise_eq) ∧
      ¬ Function.Injective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
          zeroFiveCentralRealizationBase_map_pairwise_eq) :=
  ⟨zeroFiveCentralInterfaceInclPairwise_piOne_map_surjective,
    zeroFiveCentralInterfaceInclPairwise_piOne_map_not_injective⟩

/-- At its meridian basepoint, the five-four filling map is surjective but not injective. -/
theorem fiveFourCentralInterfaceInclPairwise_piOne_map_surjective_not_injective :
    Function.Surjective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
          fiveFourCentralRealizationBase_map_pairwise_eq) ∧
      ¬ Function.Injective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
          fiveFourCentralRealizationBase_map_pairwise_eq) :=
  ⟨fiveFourCentralInterfaceInclPairwise_piOne_map_surjective,
    fiveFourCentralInterfaceInclPairwise_piOne_map_not_injective⟩

/-- At its meridian basepoint, the four-zero filling map is surjective but not injective. -/
theorem fourZeroCentralInterfaceInclPairwise_piOne_map_surjective_not_injective :
    Function.Surjective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
          fourZeroCentralRealizationBase_map_pairwise_eq) ∧
      ¬ Function.Injective
        (HomotopyGroup.map (N := Fin 1)
          (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
          fourZeroCentralRealizationBase_map_pairwise_eq) :=
  ⟨fourZeroCentralInterfaceInclPairwise_piOne_map_surjective,
    fourZeroCentralInterfaceInclPairwise_piOne_map_not_injective⟩

end ComplexProjectivePlaneTriangulation
end Submission
