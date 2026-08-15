/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierHomeomorph

/-!
# Functoriality of finite ordered-complex carriers

An inclusion of finite facet presentations induces compatible maps on the ordered simplicial
sets, their realizations, and their affine carriers. The cone-base specialization supplies the
naturality square used to identify realized finite cone inclusions pointwise.
-/

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Every listed facet of one presentation is a face of another presentation. -/
def FacetFamilyLE (facets facets' : Finset (Finset V)) : Prop :=
  ∀ facet ∈ facets, IsFace facets' facet

omit [Fintype V] in
theorem orderedSubcomplex_mono_of_facetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    orderedSubcomplex facets ≤ orderedSubcomplex facets' := by
  intro D s hs
  rcases hs with ⟨facet, hfacet, hs⟩
  rcases h facet hfacet with ⟨facet', hfacet', hsubset⟩
  exact ⟨facet', hfacet', fun i ↦ hsubset (hs i)⟩

def orderedSSetHomOfFacetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    orderedSSet facets ⟶ orderedSSet facets' :=
  SSet.Subcomplex.homOfLE (orderedSubcomplex_mono_of_facetFamilyLE h)

def facetFamilyCarrierMapOfFacetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets')
    (x : facetFamilyCarrier facets) : facetFamilyCarrier facets' :=
  ⟨x.1, by
    obtain ⟨facet, hfacet, hsupport⟩ :=
      (mem_facetFamilyCarrier_iff facets x.1).mp x.2
    obtain ⟨facet', hfacet', hsubset⟩ := h facet hfacet
    exact (mem_facetFamilyCarrier_iff facets' x.1).mpr
      ⟨facet', hfacet', fun v hv ↦
        hsupport v (fun hvfacet ↦ hv (hsubset hvfacet))⟩⟩

omit [LinearOrder V] in
theorem continuous_facetFamilyCarrierMapOfFacetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    Continuous (facetFamilyCarrierMapOfFacetFamilyLE h) :=
  Continuous.subtype_mk continuous_subtype_val _

def facetFamilyCarrierHomOfFacetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    TopCat.of (facetFamilyCarrier facets) ⟶
      TopCat.of (facetFamilyCarrier facets') :=
  TopCat.ofHom ⟨facetFamilyCarrierMapOfFacetFamilyLE h,
    continuous_facetFamilyCarrierMapOfFacetFamilyLE h⟩

theorem facetFamilyToSingular_naturality_facetFamilyLE
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    orderedSSetHomOfFacetFamilyLE h ≫ facetFamilyToSingular facets' =
      facetFamilyToSingular facets ≫
        TopCat.toSSet.map (facetFamilyCarrierHomOfFacetFamilyLE h) := by
  ext D s
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem orderedRealizationToFacetFamilyCarrier_naturality
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) ≫
        orderedRealizationToFacetFamilyCarrier facets' =
      orderedRealizationToFacetFamilyCarrier facets ≫
        facetFamilyCarrierHomOfFacetFamilyLE h := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [show (sSetTopAdj.homEquiv _ _)
      (orderedRealizationToFacetFamilyCarrier facets') =
        facetFamilyToSingular facets' by exact Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_naturality_right]
  rw [show (sSetTopAdj.homEquiv _ _)
      (orderedRealizationToFacetFamilyCarrier facets) =
        facetFamilyToSingular facets by exact Equiv.apply_symm_apply _ _]
  exact facetFamilyToSingular_naturality_facetFamilyLE h

omit [LinearOrder V] in
/-- Inclusion of one finite facet-family carrier into another is injective. -/
theorem facetFamilyCarrierHomOfFacetFamilyLE_injective
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    Function.Injective (facetFamilyCarrierHomOfFacetFamilyLE h) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg
    (fun z : facetFamilyCarrier facets' ↦ (z : stdSimplex ℝ V)) hab

/-- Geometric realization preserves inclusions between finite ordered facet families. -/
theorem orderedRealizationMapOfFacetFamilyLE_injective
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    Function.Injective (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h)) := by
  intro x y hxy
  apply (orderedRealizationHomeomorphFacetFamilyCarrier facets).injective
  change orderedRealizationToFacetFamilyCarrier facets x =
    orderedRealizationToFacetFamilyCarrier facets y
  apply facetFamilyCarrierHomOfFacetFamilyLE_injective h
  calc
    _ = orderedRealizationToFacetFamilyCarrier facets'
        (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) x) := by
      simpa only [ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom
          (orderedRealizationToFacetFamilyCarrier_naturality h) x).symm
    _ = orderedRealizationToFacetFamilyCarrier facets'
        (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h) y) := congrArg _ hxy
    _ = _ := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          (orderedRealizationToFacetFamilyCarrier_naturality h) y

/-- A finite ordered facet-family inclusion realizes as a closed topological embedding. -/
theorem orderedRealizationMapOfFacetFamilyLE_isClosedEmbedding
    {facets facets' : Finset (Finset V)}
    (h : FacetFamilyLE facets facets') :
    Topology.IsClosedEmbedding
      (SSet.toTop.map (orderedSSetHomOfFacetFamilyLE h)) := by
  letI : CompactSpace (SSet.toTop.obj (orderedSSet facets)) :=
    (orderedRealizationHomeomorphFacetFamilyCarrier facets).symm.compactSpace
  letI : T2Space (SSet.toTop.obj (orderedSSet facets')) :=
    (orderedRealizationHomeomorphFacetFamilyCarrier facets').symm.t2Space
  exact (SSet.toTop.map
      (orderedSSetHomOfFacetFamilyLE h)).hom.continuous.isClosedEmbedding
    (orderedRealizationMapOfFacetFamilyLE_injective h)

omit [Fintype V] in
theorem facetFamilyLE_cone (facets : Finset (Finset V)) (apex : V) :
    FacetFamilyLE facets (facets.image (fun facet ↦ insert apex facet)) := by
  intro facet hfacet
  exact ⟨insert apex facet, Finset.mem_image.mpr ⟨facet, hfacet, rfl⟩,
    Finset.subset_insert apex facet⟩

def orderedConeBaseIncl (facets : Finset (Finset V)) (apex : V) :
    orderedSSet facets ⟶
      orderedSSet (facets.image (fun facet ↦ insert apex facet)) :=
  orderedSSetHomOfFacetFamilyLE (facetFamilyLE_cone facets apex)

def facetFamilyConeBaseIncl (facets : Finset (Finset V)) (apex : V) :
    TopCat.of (facetFamilyCarrier facets) ⟶
      TopCat.of
        (facetFamilyCarrier (facets.image (fun facet ↦ insert apex facet))) :=
  facetFamilyCarrierHomOfFacetFamilyLE (facetFamilyLE_cone facets apex)

theorem orderedRealizationToFacetFamilyCarrier_naturality_cone
    (facets : Finset (Finset V)) (apex : V) :
    SSet.toTop.map (orderedConeBaseIncl facets apex) ≫
        orderedRealizationToFacetFamilyCarrier
          (facets.image (fun facet ↦ insert apex facet)) =
      orderedRealizationToFacetFamilyCarrier facets ≫
        facetFamilyConeBaseIncl facets apex :=
  orderedRealizationToFacetFamilyCarrier_naturality
    (facetFamilyLE_cone facets apex)

end Submission.FiniteOrderedComplex
