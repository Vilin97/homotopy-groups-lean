/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierHomeomorph
import Submission.Cohomology.FiniteOrderedComplexMap

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

section MonotoneMap

variable {W : Type} [Fintype W] [LinearOrder W]

/-- Push barycentric coordinates forward along a monotone vertex map.  A finite-complex map
ensures that the resulting point lies in the target facet-family carrier. -/
def facetFamilyCarrierMapOfMonotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target)
    (x : facetFamilyCarrier source) : facetFamilyCarrier target :=
  ⟨stdSimplex.map f x.1, by
    obtain ⟨facet, hfacet, hsupport⟩ :=
      (mem_facetFamilyCarrier_iff source x.1).mp x.2
    obtain ⟨targetFacet, htargetFacet, himage⟩ := h facet hfacet
    refine (mem_facetFamilyCarrier_iff target _).mpr
      ⟨targetFacet, htargetFacet, ?_⟩
    intro w hw
    change (FunOnFinite.linearMap ℝ ℝ f x.1) w = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro v hv
    rw [Finset.mem_filter] at hv
    apply hsupport v
    intro hvfacet
    apply hw
    exact himage (Finset.mem_image.mpr ⟨v, hvfacet, hv.2⟩)⟩

theorem continuous_facetFamilyCarrierMapOfMonotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target) :
    Continuous (facetFamilyCarrierMapOfMonotone f h) :=
  Continuous.subtype_mk
    ((stdSimplex.continuous_map f).comp continuous_subtype_val) _

def facetFamilyCarrierHomOfMonotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target) :
    TopCat.of (facetFamilyCarrier source) ⟶
      TopCat.of (facetFamilyCarrier target) :=
  TopCat.ofHom ⟨facetFamilyCarrierMapOfMonotone f h,
    continuous_facetFamilyCarrierMapOfMonotone f h⟩

/-- The simplicial map induced by a monotone vertex map agrees with affine pushforward after
passing to singular simplices of the two carriers. -/
theorem facetFamilyToSingular_naturality_monotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target) :
    orderedSSetMapOfMonotone f h ≫ facetFamilyToSingular target =
      facetFamilyToSingular source ≫
        TopCat.toSSet.map (facetFamilyCarrierHomOfMonotone f h) := by
  ext D s
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change stdSimplex.map (fun i ↦ f (s.1.obj i)) x =
    stdSimplex.map f (stdSimplex.map (fun i ↦ s.1.obj i) x)
  rw [stdSimplex.map_comp_apply]
  rfl

/-- The canonical realization/carrier homeomorphisms are natural for every monotone map of
finite facet families, including quotient maps that identify vertices. -/
theorem orderedRealizationToFacetFamilyCarrier_naturality_monotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target) :
    SSet.toTop.map (orderedSSetMapOfMonotone f h) ≫
        orderedRealizationToFacetFamilyCarrier target =
      orderedRealizationToFacetFamilyCarrier source ≫
        facetFamilyCarrierHomOfMonotone f h := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [show (sSetTopAdj.homEquiv _ _)
      (orderedRealizationToFacetFamilyCarrier target) =
        facetFamilyToSingular target by exact Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_naturality_right]
  rw [show (sSetTopAdj.homEquiv _ _)
      (orderedRealizationToFacetFamilyCarrier source) =
        facetFamilyToSingular source by exact Equiv.apply_symm_apply _ _]
  exact facetFamilyToSingular_naturality_monotone f h

end MonotoneMap

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

omit [Fintype V] in
/-- If every left/right facet intersection is a face of `common`, and every common facet is a
face on both sides, then the generated ordered subcomplexes intersect exactly in `common`. -/
theorem orderedSubcomplex_inf_eq_of_pairwise_intersections
    (common left right : Finset (Finset V))
    (hinter : ∀ leftFacet ∈ left, ∀ rightFacet ∈ right,
      IsFace common (leftFacet ∩ rightFacet))
    (hleft : FacetFamilyLE common left)
    (hright : FacetFamilyLE common right) :
    orderedSubcomplex left ⊓ orderedSubcomplex right =
      orderedSubcomplex common := by
  ext Δ x
  constructor
  · intro hx
    change x ∈ (orderedSubcomplex left).obj Δ ∧
      x ∈ (orderedSubcomplex right).obj Δ at hx
    rcases hx with ⟨⟨leftFacet, hleftFacet, hxleft⟩,
      ⟨rightFacet, hrightFacet, hxright⟩⟩
    obtain ⟨commonFacet, hcommonFacet, hsubset⟩ :=
      hinter leftFacet hleftFacet rightFacet hrightFacet
    exact ⟨commonFacet, hcommonFacet, fun i ↦
      hsubset (Finset.mem_inter.mpr ⟨hxleft i, hxright i⟩)⟩
  · intro hx
    change x ∈ (orderedSubcomplex left).obj Δ ∧
      x ∈ (orderedSubcomplex right).obj Δ
    exact ⟨orderedSubcomplex_mono_of_facetFamilyLE hleft Δ hx,
      orderedSubcomplex_mono_of_facetFamilyLE hright Δ hx⟩

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
