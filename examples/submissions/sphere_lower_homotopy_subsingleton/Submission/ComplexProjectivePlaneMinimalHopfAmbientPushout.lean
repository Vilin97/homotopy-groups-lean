/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallCollapse
import Submission.Topology.PushoutMono

/-!
# The genuine ambient pushout of the finite Hopf map

The seventeen-vertex ambient complex, its boundary three-sphere, and the four-triangle Hopf
target map to the maintained nine-vertex projective-plane complex.  Although that square
commutes strictly, it is not itself a pushout: two explicit interior edges outside the boundary
have the same image under the quotient.

This file records that obstruction, constructs the actual simplicial pushout of the boundary
inclusion and finite Hopf map, and defines its canonical comparison with the nine-vertex model.
Geometric realization preserves the genuine pushout.  The comparison is not a simplicial
isomorphism, as forced by the obstruction.  The same two-edge collision is realized at explicit
interior midpoints, proving that the topological comparison remains noninjective; proving that it
is nevertheless a homotopy equivalence is the next comparison step.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## A collision outside the boundary -/

/-- A type-level pushout cannot identify two distinct points on the left if one of them lies
outside the range of the gluing map. -/
private theorem type_not_isPushout_of_collision_outside_range
    {A B C P : Type}
    (f : A ⟶ B) (g : A ⟶ C) (q : B ⟶ P) (j : C ⟶ P)
    (x y : B) (hx : x ∉ Set.range f) (hxy : x ≠ y) (hq : q x = q y) :
    ¬ IsPushout f g q j := by
  classical
  intro hP
  let mark : B ⟶ Bool := TypeCat.ofHom fun z ↦ decide (z = x)
  let zero : C ⟶ Bool := TypeCat.ofHom fun _ ↦ false
  have hagree : f ≫ mark = g ≫ zero := by
    apply ConcreteCategory.hom_ext
    intro a
    have hfax : f a ≠ x := fun h ↦ hx ⟨a, h⟩
    simp [mark, zero, hfax]
  let d : P ⟶ Bool := hP.desc mark zero hagree
  have hmark : q ≫ d = mark := hP.inl_desc mark zero hagree
  have hxmark := ConcreteCategory.congr_hom hmark x
  have hymark := ConcreteCategory.congr_hom hmark y
  have hmarks : mark x = mark y := by
    rw [← hxmark, ← hymark]
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun p ↦ d p) hq
  have hyx : y = x := by simpa [mark] using hmarks
  exact hxy hyx.symm

/-- The first interior edge witnessing an additional quotient identification. -/
def minimalHopfAmbientCollisionLeftEdge : Finset MinimalHopfBallVertex :=
  {2, 8}

/-- The second interior edge witnessing the same additional quotient identification. -/
def minimalHopfAmbientCollisionRightEdge : Finset MinimalHopfBallVertex :=
  {2, 10}

def minimalHopfAmbientCollisionLeftOrderHom :
    Fin 2 →o MinimalHopfBallVertex where
  toFun := ![2, 8]
  monotone' := by decide

def minimalHopfAmbientCollisionRightOrderHom :
    Fin 2 →o MinimalHopfBallVertex where
  toFun := ![2, 10]
  monotone' := by decide

/-- The twelve vertices used by every facet of the finite Hopf boundary. -/
def minimalHopfBoundaryVertexSupport : Finset MinimalHopfBallVertex :=
  {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}

theorem minimalHopfBallRotation_mem_boundaryVertexSupport
    (v : MinimalHopfBallVertex) (hv : v ∈ minimalHopfBoundaryVertexSupport) :
    minimalHopfBallRotation v ∈ minimalHopfBoundaryVertexSupport := by
  fin_cases v <;>
    simp [minimalHopfBoundaryVertexSupport, minimalHopfBallRotation] at hv ⊢

private theorem minimalHopfThreefoldOrbit_subset_boundaryVertexSupport
    (displayed : Finset (Finset MinimalHopfBallVertex))
    (hdisplayed : ∀ facet ∈ displayed,
      facet ⊆ minimalHopfBoundaryVertexSupport) :
    ∀ facet ∈ minimalHopfThreefoldOrbit displayed,
      facet ⊆ minimalHopfBoundaryVertexSupport := by
  intro facet hfacet
  rw [minimalHopfThreefoldOrbit] at hfacet
  rcases Finset.mem_union.mp hfacet with hfirst | htwice
  · rcases Finset.mem_union.mp hfirst with hdirect | honce
    · exact hdisplayed facet hdirect
    · rcases Finset.mem_image.mp honce with ⟨source, hsource, rfl⟩
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
      exact minimalHopfBallRotation_mem_boundaryVertexSupport u
        (hdisplayed source hsource hu)
  · rcases Finset.mem_image.mp htwice with ⟨once, honce, rfl⟩
    rcases Finset.mem_image.mp honce with ⟨source, hsource, rfl⟩
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    exact minimalHopfBallRotation_mem_boundaryVertexSupport _
      (minimalHopfBallRotation_mem_boundaryVertexSupport w
        (hdisplayed source hsource hw))

/-- Every displayed boundary facet is supported on the twelve boundary vertices. -/
theorem minimalHopfSphereFacet_subset_boundaryVertexSupport :
    ∀ facet ∈ minimalHopfSphereFacets,
      facet ⊆ minimalHopfBoundaryVertexSupport := by
  intro facet hfacet
  rw [minimalHopfSphereFacets] at hfacet
  rcases Finset.mem_union.mp hfacet with horbit | hexceptional
  · apply minimalHopfThreefoldOrbit_subset_boundaryVertexSupport
      minimalHopfSphereOrbitRepresentatives
    · intro representative hrepresentative
      simp [minimalHopfSphereOrbitRepresentatives] at hrepresentative
      rcases hrepresentative with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    · exact horbit
  · have hexceptionalSupport :
        ∀ exceptional ∈ minimalHopfSphereExceptionalFacets,
          exceptional ⊆ minimalHopfBoundaryVertexSupport := by
      intro exceptional hexceptional
      simp [minimalHopfSphereExceptionalFacets] at hexceptional
      rcases hexceptional with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    exact hexceptionalSupport facet hexceptional

/-- The certified boundary is exactly the subcomplex induced on the twelve outer vertices:
a finite ambient face belongs to the boundary precisely when all of its vertices are outer. -/
theorem minimalHopfSphere_isFace_iff
    (face : Finset MinimalHopfBallVertex) :
    IsFace minimalHopfSphereFacets face ↔
      IsFace minimalHopfBallFacets face ∧
        face ⊆ minimalHopfBoundaryVertexSupport := by
  constructor
  · rintro ⟨facet, hfacet, hface⟩
    obtain ⟨ballFacet, hballFacet, hfacetBall⟩ :=
      minimalHopfSphereFacets_le_ball facet hfacet
    exact ⟨⟨ballFacet, hballFacet, hface.trans hfacetBall⟩,
      fun v hv ↦ minimalHopfSphereFacet_subset_boundaryVertexSupport
        facet hfacet (hface hv)⟩
  · rintro ⟨hface, hsupport⟩
    obtain ⟨facet, hfacet, hfaceFacet⟩ := hface
    exact (by decide : ∀ facet : ↥minimalHopfBallFacets,
      ∀ face : ↥facet.1.powerset,
        face.1 ⊆ minimalHopfBoundaryVertexSupport →
          IsFace minimalHopfSphereFacets face.1)
      ⟨facet, hfacet⟩ ⟨face, Finset.mem_powerset.mpr hfaceFacet⟩ hsupport

/-- In affine coordinates, the boundary carrier consists exactly of ambient carrier points
whose nonzero coordinates are supported on the twelve outer vertices. -/
theorem minimalHopfSphere_mem_carrier_iff
    (x : stdSimplex ℝ MinimalHopfBallVertex) :
    x ∈ facetFamilyCarrier minimalHopfSphereFacets ↔
      x ∈ facetFamilyCarrier minimalHopfBallFacets ∧
        ∀ v, v ∉ minimalHopfBoundaryVertexSupport → x v = 0 := by
  constructor
  · intro hx
    obtain ⟨facet, hfacet, hsupport⟩ :=
      (mem_facetFamilyCarrier_iff minimalHopfSphereFacets x).mp hx
    obtain ⟨ballFacet, hballFacet, hfacetBall⟩ :=
      minimalHopfSphereFacets_le_ball facet hfacet
    constructor
    · exact (mem_facetFamilyCarrier_iff minimalHopfBallFacets x).mpr
        ⟨ballFacet, hballFacet, fun v hv ↦
          hsupport v (fun hvfacet ↦ hv (hfacetBall hvfacet))⟩
    · intro v hv
      exact hsupport v (fun hvfacet ↦ hv
        (minimalHopfSphereFacet_subset_boundaryVertexSupport
          facet hfacet hvfacet))
  · rintro ⟨hx, hzero⟩
    obtain ⟨ballFacet, hballFacet, hsupport⟩ :=
      (mem_facetFamilyCarrier_iff minimalHopfBallFacets x).mp hx
    let face := ballFacet ∩ minimalHopfBoundaryVertexSupport
    have hfaceBall : IsFace minimalHopfBallFacets face :=
      ⟨ballFacet, hballFacet, Finset.inter_subset_left⟩
    have hfaceSupport : face ⊆ minimalHopfBoundaryVertexSupport :=
      Finset.inter_subset_right
    obtain ⟨sphereFacet, hsphereFacet, hfaceSphere⟩ :=
      (minimalHopfSphere_isFace_iff face).mpr ⟨hfaceBall, hfaceSupport⟩
    exact (mem_facetFamilyCarrier_iff minimalHopfSphereFacets x).mpr
      ⟨sphereFacet, hsphereFacet, fun v hv ↦ by
        by_cases hvBall : v ∈ ballFacet
        · apply hzero v
          intro hvBoundary
          exact hv (hfaceSphere
            (Finset.mem_inter.mpr ⟨hvBall, hvBoundary⟩))
        · exact hsupport v hvBall⟩

/-- The ordered simplex on the first collision edge. -/
def minimalHopfAmbientCollisionLeftSimplex :
    (orderedSSet minimalHopfBallFacets).obj (Opposite.op ⦋1⦌) :=
  ⟨minimalHopfAmbientCollisionLeftOrderHom.monotone.functor,
    ⟨{0, 2, 3, 5, 8}, by
      rw [minimalHopfBallFacets, minimalHopfThreefoldOrbit]
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inl (by simp [minimalHopfBallDisplayedFacets])))), by
      intro i
      fin_cases i <;> decide⟩⟩

/-- The ordered simplex on the second collision edge. -/
def minimalHopfAmbientCollisionRightSimplex :
    (orderedSSet minimalHopfBallFacets).obj (Opposite.op ⦋1⦌) :=
  ⟨minimalHopfAmbientCollisionRightOrderHom.monotone.functor,
    ⟨{1, 2, 7, 10, 16}, by
      rw [minimalHopfBallFacets, minimalHopfThreefoldOrbit]
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inl (by simp [minimalHopfBallDisplayedFacets])))), by
      intro i
      fin_cases i <;> decide⟩⟩

/-- The two displayed interior edges are distinct ordered one-simplices. -/
theorem minimalHopfAmbientCollisionSimplices_ne :
    minimalHopfAmbientCollisionLeftSimplex ≠
      minimalHopfAmbientCollisionRightSimplex := by
  intro h
  have hvertex := congrArg (fun z ↦ z.1.obj (1 : Fin 2)) h
  change minimalHopfAmbientCollisionLeftOrderHom 1 =
    minimalHopfAmbientCollisionRightOrderHom 1 at hvertex
  simp [minimalHopfAmbientCollisionLeftOrderHom,
    minimalHopfAmbientCollisionRightOrderHom] at hvertex

/-- The vertex quotient identifies the two distinct ordered interior edges. -/
theorem minimalHopfAmbientCollisionSimplices_map_eq :
    minimalHopfBallQuotientSSetMap.app (Opposite.op ⦋1⦌)
        minimalHopfAmbientCollisionLeftSimplex =
      minimalHopfBallQuotientSSetMap.app (Opposite.op ⦋1⦌)
        minimalHopfAmbientCollisionRightSimplex := by
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  change minimalHopfQuotientVertex
      (minimalHopfAmbientCollisionLeftOrderHom i) =
    minimalHopfQuotientVertex
      (minimalHopfAmbientCollisionRightOrderHom i)
  fin_cases i <;> rfl

/-- The first collision edge is not supplied by a boundary simplex, because its first endpoint
is the interior vertex `3` (zero-based index `2`). -/
theorem minimalHopfAmbientCollisionLeft_not_mem_boundary_range :
    minimalHopfAmbientCollisionLeftSimplex ∉
      Set.range (minimalHopfSphereSSetIncl.app (Opposite.op ⦋1⦌)) := by
  rintro ⟨z, hz⟩
  rcases z.2 with ⟨facet, hfacet, hvertices⟩
  have hvertex := congrArg (fun w ↦ w.1.obj (0 : Fin 2)) hz
  have hvertex' : z.1.obj 0 = (2 : MinimalHopfBallVertex) := by
    change z.1.obj 0 = minimalHopfAmbientCollisionLeftOrderHom 0 at hvertex
    exact hvertex
  have htwo : (2 : MinimalHopfBallVertex) ∈ facet := by
    rw [← hvertex']
    exact hvertices 0
  exact (by decide : (2 : MinimalHopfBallVertex) ∉
    minimalHopfBoundaryVertexSupport)
      (minimalHopfSphereFacet_subset_boundaryVertexSupport facet hfacet htwo)

/-- **The finite ambient quotient square is not a strict simplicial pushout.**  Evaluation in
degree one preserves the alleged pushout and exposes the two identified interior edges. -/
theorem minimalHopfQuotient_not_isPushout :
    ¬ IsPushout minimalHopfSphereSSetIncl minimalHopfSSetMap
      minimalHopfBallQuotientSSetMap minimalHopfTargetSSetIncl := by
  intro hP
  let ev := (evaluation SimplexCategoryᵒᵖ (Type)).obj (Opposite.op ⦋1⦌)
  have hP1 := hP.map ev
  apply (type_not_isPushout_of_collision_outside_range
    (minimalHopfSphereSSetIncl.app (Opposite.op ⦋1⦌))
    (minimalHopfSSetMap.app (Opposite.op ⦋1⦌))
    (minimalHopfBallQuotientSSetMap.app (Opposite.op ⦋1⦌))
    (minimalHopfTargetSSetIncl.app (Opposite.op ⦋1⦌))
    minimalHopfAmbientCollisionLeftSimplex
    minimalHopfAmbientCollisionRightSimplex
    minimalHopfAmbientCollisionLeft_not_mem_boundary_range
    minimalHopfAmbientCollisionSimplices_ne
    minimalHopfAmbientCollisionSimplices_map_eq)
  exact hP1

/-! ## The actual simplicial pushout and its comparison -/

/-- The genuine simplicial pushout of the boundary inclusion and finite Hopf map. -/
noncomputable abbrev minimalHopfStrictPushoutSSet : SSet :=
  Limits.pushout minimalHopfSphereSSetIncl minimalHopfSSetMap

/-- Inclusion of the contractible ambient complex into the genuine pushout. -/
noncomputable def minimalHopfStrictPushoutBallIncl :
    orderedSSet minimalHopfBallFacets ⟶ minimalHopfStrictPushoutSSet :=
  Limits.pushout.inl minimalHopfSphereSSetIncl minimalHopfSSetMap

/-- Inclusion of the finite two-sphere target into the genuine pushout. -/
noncomputable def minimalHopfStrictPushoutTargetIncl :
    orderedSSet minimalHopfTargetFacets ⟶ minimalHopfStrictPushoutSSet :=
  Limits.pushout.inr minimalHopfSphereSSetIncl minimalHopfSSetMap

/-- The canonical square defining `minimalHopfStrictPushoutSSet` is a pushout. -/
theorem minimalHopfStrictPushout_isPushout :
    IsPushout minimalHopfSphereSSetIncl minimalHopfSSetMap
      minimalHopfStrictPushoutBallIncl minimalHopfStrictPushoutTargetIncl := by
  exact IsPushout.of_hasPushout _ _

/-- The commuting finite quotient square induces a canonical comparison from the genuine
pushout to the maintained nine-vertex projective-plane simplicial set. -/
noncomputable def minimalHopfStrictPushoutComparison :
    minimalHopfStrictPushoutSSet ⟶ projectivePlaneSSet :=
  Limits.pushout.desc minimalHopfBallQuotientSSetMap
    minimalHopfTargetSSetIncl minimalHopfQuotient_sSet_square

@[reassoc]
theorem minimalHopfStrictPushoutBallIncl_comparison :
    minimalHopfStrictPushoutBallIncl ≫ minimalHopfStrictPushoutComparison =
      minimalHopfBallQuotientSSetMap := by
  apply Limits.pushout.inl_desc

@[reassoc]
theorem minimalHopfStrictPushoutTargetIncl_comparison :
    minimalHopfStrictPushoutTargetIncl ≫ minimalHopfStrictPushoutComparison =
      minimalHopfTargetSSetIncl := by
  apply Limits.pushout.inr_desc

/-- Every simplex of the nine-vertex projective-plane model lifts through the finite ambient
quotient.  A target simplex lies in a top facet, and the facet computation supplies a source
top facet on which the vertex quotient is an order isomorphism. -/
theorem minimalHopfBallQuotientSSetMap_app_surjective
    (Δ : SimplexCategoryᵒᵖ) :
    Function.Surjective (minimalHopfBallQuotientSSetMap.app Δ) := by
  intro y
  rcases y.2 with ⟨targetFacet, htargetFacet, hy⟩
  have hfilter :
      targetFacet ∈
        (minimalHopfBallFacets.image
          (fun facet ↦ facet.image minimalHopfQuotientVertex)).filter
            (fun facet ↦ facet.card = 5) := by
    rw [minimalHopfBall_quotient_top_facets]
    exact htargetFacet
  rcases Finset.mem_filter.mp hfilter with ⟨himageMem, himageCard⟩
  rcases Finset.mem_image.mp himageMem with
    ⟨sourceFacet, hsourceFacet, himage⟩
  have hinjOn : Set.InjOn minimalHopfQuotientVertex sourceFacet := by
    rw [← Finset.card_image_iff]
    rw [himage, himageCard,
      minimalHopfBallFacets_pure sourceFacet hsourceFacet]
  let facetMap : ↑sourceFacet → ↑targetFacet := fun v ↦
    ⟨minimalHopfQuotientVertex v.1, by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  have hfacetMapMonotone : Monotone facetMap := by
    intro a b hab
    exact minimalHopfQuotientVertex.monotone hab
  have hfacetMapInjective : Function.Injective facetMap := by
    intro a b hab
    apply Subtype.ext
    exact hinjOn a.2 b.2 (congrArg Subtype.val hab)
  have hfacetMapSurjective : Function.Surjective facetMap := by
    intro w
    have hw : w.1 ∈ sourceFacet.image minimalHopfQuotientVertex := by
      rw [himage]
      exact w.2
    rcases Finset.mem_image.mp hw with ⟨v, hv, huv⟩
    exact ⟨⟨v, hv⟩, Subtype.ext huv⟩
  have hfacetMapStrictMono : StrictMono facetMap :=
    hfacetMapMonotone.strictMono_of_injective hfacetMapInjective
  let facetIso : ↑sourceFacet ≃o ↑targetFacet :=
    hfacetMapStrictMono.orderIsoOfSurjective facetMap hfacetMapSurjective
  let liftVertex : Fin (Δ.unop.len + 1) →o MinimalHopfBallVertex :=
    { toFun := fun i ↦ (facetIso.symm ⟨y.1.obj i, hy i⟩).1
      monotone' := by
        intro i j hij
        exact facetIso.symm.monotone (y.1.monotone hij) }
  let x : (orderedSSet minimalHopfBallFacets).obj Δ :=
    ⟨liftVertex.monotone.functor,
      ⟨sourceFacet, hsourceFacet, fun i ↦
        (facetIso.symm ⟨y.1.obj i, hy i⟩).2⟩⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  change minimalHopfQuotientVertex (liftVertex i) = y.1.obj i
  exact congrArg Subtype.val
    (facetIso.apply_symm_apply ⟨y.1.obj i, hy i⟩)

/-- The finite ambient quotient is an epimorphism of simplicial sets. -/
instance minimalHopfBallQuotientSSetMap_epi :
    Epi minimalHopfBallQuotientSSetMap := by
  rw [NatTrans.epi_iff_epi_app]
  intro Δ
  rw [epi_iff_surjective]
  exact minimalHopfBallQuotientSSetMap_app_surjective Δ

/-- The canonical comparison from the genuine finite Hopf pushout is an epimorphism. -/
instance minimalHopfStrictPushoutComparison_epi :
    Epi minimalHopfStrictPushoutComparison := by
  apply epi_of_epi_fac minimalHopfStrictPushoutBallIncl_comparison

/-- The canonical comparison cannot be a simplicial isomorphism: otherwise transporting the
genuine pushout square across it would make the finite quotient square a pushout. -/
theorem minimalHopfStrictPushoutComparison_not_isIso :
    ¬ IsIso minimalHopfStrictPushoutComparison := by
  intro h
  letI : IsIso minimalHopfStrictPushoutComparison := h
  apply minimalHopfQuotient_not_isPushout
  exact minimalHopfStrictPushout_isPushout.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso minimalHopfStrictPushoutComparison)
    (by simp) (by simp)
    (by simpa using minimalHopfStrictPushoutBallIncl_comparison)
    (by simpa using minimalHopfStrictPushoutTargetIncl_comparison)

/-! ## Geometric realization -/

/-- Realization of the genuine simplicial pushout. -/
noncomputable abbrev minimalHopfStrictPushoutRealization : TopCat :=
  SSet.toTop.obj minimalHopfStrictPushoutSSet

/-- Realization of the canonical comparison with the nine-vertex projective plane. -/
noncomputable def minimalHopfStrictPushoutComparisonRealization :
    minimalHopfStrictPushoutRealization ⟶ projectivePlaneRealization :=
  SSet.toTop.map minimalHopfStrictPushoutComparison

/-- Geometric realization preserves the genuine finite Hopf pushout. -/
theorem minimalHopfStrictPushoutRealization_isPushout :
    IsPushout
      (SSet.toTop.map minimalHopfSphereSSetIncl)
      minimalHopfRealizationMap
      (SSet.toTop.map minimalHopfStrictPushoutBallIncl)
      (SSet.toTop.map minimalHopfStrictPushoutTargetIncl) := by
  simpa [minimalHopfRealizationMap] using
    minimalHopfStrictPushout_isPushout.map SSet.toTop

/-- The realization of the genuine finite Hopf pushout is compact.  It is isomorphic to the
canonical topological pushout of the compact ambient and target finite polyhedra. -/
noncomputable instance minimalHopfStrictPushoutRealization_compactSpace :
    CompactSpace minimalHopfStrictPushoutRealization := by
  let f := SSet.toTop.map minimalHopfSphereSSetIncl
  let g := minimalHopfRealizationMap
  let B := SSet.toTop.obj (orderedSSet minimalHopfBallFacets)
  let C := SSet.toTop.obj (orderedSSet minimalHopfTargetFacets)
  letI : CompactSpace B :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallFacets).symm.compactSpace
  letI : CompactSpace C :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfTargetFacets).symm.compactSpace
  let P : TopCat := Limits.pushout f g
  letI : CompactSpace P :=
    Function.Surjective.compactSpace
      (pushoutSumDesc_isQuotientMap f g).continuous
      (pushoutSumDesc_isQuotientMap f g).surjective
  let canonical : IsPushout f g (Limits.pushout.inl f g)
      (Limits.pushout.inr f g) := IsPushout.of_hasPushout f g
  let e : P ≅ minimalHopfStrictPushoutRealization :=
    canonical.isoIsPushout B C minimalHopfStrictPushoutRealization_isPushout
  exact Function.Surjective.compactSpace
    (TopCat.homeoOfIso e).continuous
    (TopCat.homeoOfIso e).surjective

/-! ## The boundary as a barycentric zero set -/

/-- The five interior vertices of the finite ambient four-ball. -/
def minimalHopfInteriorVertexSupport : Finset MinimalHopfBallVertex :=
  {0, 1, 2, 3, 4}

/-- The total barycentric weight on the five interior vertices of the affine ambient carrier. -/
noncomputable def minimalHopfInteriorMass
    (x : facetFamilyCarrier minimalHopfBallFacets) : ℝ :=
  ∑ v ∈ minimalHopfInteriorVertexSupport, x.1 v

/-- Interior barycentric mass varies continuously on the affine ambient carrier. -/
theorem continuous_minimalHopfInteriorMass :
    Continuous minimalHopfInteriorMass := by
  apply continuous_finsetSum
  intro v _
  exact ((continuous_apply v).comp continuous_subtype_val).comp
    continuous_subtype_val

/-- An ambient carrier point belongs to the boundary carrier exactly when its total interior
barycentric mass vanishes. -/
theorem minimalHopfSphere_mem_carrier_iff_interiorMass_eq_zero
    (x : facetFamilyCarrier minimalHopfBallFacets) :
    x.1 ∈ facetFamilyCarrier minimalHopfSphereFacets ↔
      minimalHopfInteriorMass x = 0 := by
  rw [minimalHopfSphere_mem_carrier_iff]
  constructor
  · rintro ⟨_, hzero⟩
    rw [minimalHopfInteriorMass]
    apply Finset.sum_eq_zero
    intro v hv
    apply hzero v
    fin_cases v <;>
      simp [minimalHopfInteriorVertexSupport,
        minimalHopfBoundaryVertexSupport] at hv ⊢
  · intro hmass
    refine ⟨x.2, ?_⟩
    intro v hv
    have hcoordinate : ∀ w ∈ minimalHopfInteriorVertexSupport,
        x.1 w = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ ↦ x.1.2.1 w)).mp hmass
    apply hcoordinate v
    fin_cases v <;>
      simp [minimalHopfInteriorVertexSupport,
        minimalHopfBoundaryVertexSupport] at hv ⊢

/-- The affine boundary inclusion has range exactly the zero set of interior mass. -/
theorem minimalHopfBoundaryCarrier_range_iff_interiorMass_eq_zero
    (x : facetFamilyCarrier minimalHopfBallFacets) :
    x ∈ Set.range
        (facetFamilyCarrierMapOfFacetFamilyLE
          minimalHopfSphereFacets_le_ball) ↔
      minimalHopfInteriorMass x = 0 := by
  rw [← minimalHopfSphere_mem_carrier_iff_interiorMass_eq_zero]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩

/-- Interior barycentric mass transported across the canonical realization/carrier
homeomorphism. -/
noncomputable def minimalHopfRealizationInteriorMass
    (x : SSet.toTop.obj (orderedSSet minimalHopfBallFacets)) : ℝ :=
  minimalHopfInteriorMass
    (orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets x)

/-- Realized interior mass is continuous. -/
theorem continuous_minimalHopfRealizationInteriorMass :
    Continuous minimalHopfRealizationInteriorMass :=
  continuous_minimalHopfInteriorMass.comp
    (orderedRealizationToFacetFamilyCarrier
      minimalHopfBallFacets).hom.continuous

/-- A point of the realized ambient four-ball lies in the realized boundary inclusion exactly
when its interior barycentric mass vanishes. -/
theorem minimalHopfBoundaryRealization_range_iff_interiorMass_eq_zero
    (x : SSet.toTop.obj (orderedSSet minimalHopfBallFacets)) :
    x ∈ Set.range (SSet.toTop.map minimalHopfSphereSSetIncl) ↔
      minimalHopfRealizationInteriorMass x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    apply (minimalHopfBoundaryCarrier_range_iff_interiorMass_eq_zero
      (orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
        (SSet.toTop.map minimalHopfSphereSSetIncl y))).mp
    refine ⟨orderedRealizationToFacetFamilyCarrier
      minimalHopfSphereFacets y, ?_⟩
    simpa [minimalHopfSphereSSetIncl, ConcreteCategory.comp_apply,
      facetFamilyCarrierHomOfFacetFamilyLE] using
      (ConcreteCategory.congr_hom
        (orderedRealizationToFacetFamilyCarrier_naturality
          minimalHopfSphereFacets_le_ball) y).symm
  · intro hmass
    obtain ⟨z, hz⟩ :=
      (minimalHopfBoundaryCarrier_range_iff_interiorMass_eq_zero
        (orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets x)).mpr
          hmass
    refine ⟨(orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfSphereFacets).symm z, ?_⟩
    apply (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallFacets).injective
    calc
      orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
          (SSet.toTop.map minimalHopfSphereSSetIncl
            ((orderedRealizationHomeomorphFacetFamilyCarrier
              minimalHopfSphereFacets).symm z)) =
        facetFamilyCarrierMapOfFacetFamilyLE
          minimalHopfSphereFacets_le_ball
            (orderedRealizationToFacetFamilyCarrier
              minimalHopfSphereFacets
                ((orderedRealizationHomeomorphFacetFamilyCarrier
                  minimalHopfSphereFacets).symm z)) := by
          simpa [minimalHopfSphereSSetIncl, ConcreteCategory.comp_apply,
            facetFamilyCarrierHomOfFacetFamilyLE] using
            ConcreteCategory.congr_hom
              (orderedRealizationToFacetFamilyCarrier_naturality
                minimalHopfSphereFacets_le_ball)
              ((orderedRealizationHomeomorphFacetFamilyCarrier
                minimalHopfSphereFacets).symm z)
      _ = facetFamilyCarrierMapOfFacetFamilyLE
          minimalHopfSphereFacets_le_ball z := by
        rw [show orderedRealizationToFacetFamilyCarrier
            minimalHopfSphereFacets
              ((orderedRealizationHomeomorphFacetFamilyCarrier
                minimalHopfSphereFacets).symm z) = z by
          exact (orderedRealizationHomeomorphFacetFamilyCarrier
            minimalHopfSphereFacets).apply_symm_apply z]
      _ = orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets x := hz

@[reassoc]
theorem minimalHopfStrictPushoutBallIncl_comparison_realization :
    SSet.toTop.map minimalHopfStrictPushoutBallIncl ≫
        minimalHopfStrictPushoutComparisonRealization =
      minimalHopfBallQuotientRealizationMap := by
  rw [minimalHopfStrictPushoutComparisonRealization,
    minimalHopfBallQuotientRealizationMap, ← SSet.toTop.map_comp,
    minimalHopfStrictPushoutBallIncl_comparison]

@[reassoc]
theorem minimalHopfStrictPushoutTargetIncl_comparison_realization :
    SSet.toTop.map minimalHopfStrictPushoutTargetIncl ≫
        minimalHopfStrictPushoutComparisonRealization =
      SSet.toTop.map minimalHopfTargetSSetIncl := by
  rw [minimalHopfStrictPushoutComparisonRealization, ← SSet.toTop.map_comp,
    minimalHopfStrictPushoutTargetIncl_comparison]

/-- The source vertices lying over each of the nine quotient vertices.  The first five fibers
are singletons and the remaining four are the collapsed triples. -/
def minimalHopfQuotientVertexFiber :
    Vertex → Finset MinimalHopfBallVertex :=
  ![{0}, {1}, {2}, {3}, {4}, {5, 6, 7}, {8, 9, 10},
    {11, 12, 13}, {14, 15, 16}]

/-- The displayed finite fibers are exactly the inverse images of the vertex quotient. -/
theorem minimalHopfQuotientVertexFiber_eq_filter (w : Vertex) :
    minimalHopfQuotientVertexFiber w =
      Finset.univ.filter (fun v ↦ minimalHopfQuotientVertex v = w) := by
  fin_cases w <;> decide

/-- Under the canonical affine-carrier coordinates, the realized ambient quotient is exactly
the barycentric pushforward along the seventeen-to-nine vertex quotient. -/
theorem minimalHopfBallQuotientRealization_carrier_naturality :
    minimalHopfBallQuotientRealizationMap ≫
        orderedRealizationToFacetFamilyCarrier facets =
      orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets ≫
        facetFamilyCarrierHomOfMonotone minimalHopfQuotientVertex
          minimalHopfBallFacetFamilyMapsTo :=
  orderedRealizationToFacetFamilyCarrier_naturality_monotone
    minimalHopfQuotientVertex minimalHopfBallFacetFamilyMapsTo

/-- Coordinate formula for the affine ambient quotient: the weight at a target vertex is the
sum of the source weights in its displayed finite fiber. -/
theorem minimalHopfBallCarrierQuotient_coordinate
    (x : facetFamilyCarrier minimalHopfBallFacets) (w : Vertex) :
    (facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
      minimalHopfBallFacetFamilyMapsTo x).1 w =
        (minimalHopfQuotientVertexFiber w).sum (fun v ↦ x.1 v) := by
  change (FunOnFinite.linearMap ℝ ℝ minimalHopfQuotientVertex x.1) w = _
  rw [FunOnFinite.linearMap_apply_apply,
    minimalHopfQuotientVertexFiber_eq_filter]

/-! ## A surviving topological collision -/

/-- The midpoint used to realize both collision edges. -/
def minimalHopfAmbientCollisionMidpoint : stdSimplex ℝ (Fin 2) :=
  ⟨![1 / 2, 1 / 2], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_two]⟩

/-- The affine midpoint of the first collision edge in the ambient carrier. -/
noncomputable def minimalHopfAmbientCollisionLeftCarrierPoint :
    facetFamilyCarrier minimalHopfBallFacets :=
  facetFamilyTopologicalSimplexPoint minimalHopfBallFacets
    minimalHopfAmbientCollisionLeftSimplex
    minimalHopfAmbientCollisionMidpoint

/-- The affine midpoint of the second collision edge in the ambient carrier. -/
noncomputable def minimalHopfAmbientCollisionRightCarrierPoint :
    facetFamilyCarrier minimalHopfBallFacets :=
  facetFamilyTopologicalSimplexPoint minimalHopfBallFacets
    minimalHopfAmbientCollisionRightSimplex
    minimalHopfAmbientCollisionMidpoint

private theorem minimalHopfAmbientCollisionLeftCarrierPoint_coord_eight :
    minimalHopfAmbientCollisionLeftCarrierPoint.1
        (8 : MinimalHopfBallVertex) = 1 / 2 := by
  change (FunOnFinite.linearMap ℝ ℝ
    (fun i : Fin 2 => ![2, 8] i)
      minimalHopfAmbientCollisionMidpoint.1) 8 = 1 / 2
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.sum_univ_two,
    minimalHopfAmbientCollisionMidpoint]

private theorem minimalHopfAmbientCollisionLeftCarrierPoint_coord_two :
    minimalHopfAmbientCollisionLeftCarrierPoint.1
        (2 : MinimalHopfBallVertex) = 1 / 2 := by
  change (FunOnFinite.linearMap ℝ ℝ
    (fun i : Fin 2 => ![2, 8] i)
      minimalHopfAmbientCollisionMidpoint.1) 2 = 1 / 2
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.sum_univ_two,
    minimalHopfAmbientCollisionMidpoint]

private theorem minimalHopfAmbientCollisionRightCarrierPoint_coord_eight :
    minimalHopfAmbientCollisionRightCarrierPoint.1
        (8 : MinimalHopfBallVertex) = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ
    (fun i : Fin 2 => ![2, 10] i)
      minimalHopfAmbientCollisionMidpoint.1) 8 = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter, Fin.sum_univ_two,
    minimalHopfAmbientCollisionMidpoint]

/-- The two affine collision midpoints are distinct in the ambient finite polyhedron. -/
theorem minimalHopfAmbientCollisionCarrierPoints_ne :
    minimalHopfAmbientCollisionLeftCarrierPoint ≠
      minimalHopfAmbientCollisionRightCarrierPoint := by
  intro h
  have hcoord := congrArg
    (fun x : facetFamilyCarrier minimalHopfBallFacets =>
      x.1 (8 : MinimalHopfBallVertex)) h
  rw [minimalHopfAmbientCollisionLeftCarrierPoint_coord_eight,
    minimalHopfAmbientCollisionRightCarrierPoint_coord_eight] at hcoord
  norm_num at hcoord

/-- Affine pushforward along the vertex quotient identifies the two collision midpoints. -/
theorem minimalHopfAmbientCollisionCarrierQuotient_eq :
    facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
        minimalHopfAmbientCollisionLeftCarrierPoint =
      facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
        minimalHopfAmbientCollisionRightCarrierPoint := by
  apply Subtype.ext
  apply stdSimplex.ext
  funext w
  rw [minimalHopfBallCarrierQuotient_coordinate,
    minimalHopfBallCarrierQuotient_coordinate]
  fin_cases w <;>
    simp [minimalHopfQuotientVertexFiber,
      minimalHopfAmbientCollisionLeftCarrierPoint,
      minimalHopfAmbientCollisionRightCarrierPoint,
      facetFamilyTopologicalSimplexPoint,
      minimalHopfAmbientCollisionMidpoint,
      minimalHopfAmbientCollisionLeftSimplex,
      minimalHopfAmbientCollisionRightSimplex,
      minimalHopfAmbientCollisionLeftOrderHom,
      minimalHopfAmbientCollisionRightOrderHom,
      FunOnFinite.linearMap_apply_apply, Finset.sum_filter,
      Fin.sum_univ_two]

/-- The first collision midpoint in the realization of the ambient complex. -/
noncomputable def minimalHopfAmbientCollisionLeftBallPoint :
    SSet.toTop.obj (orderedSSet minimalHopfBallFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfBallFacets).symm
      minimalHopfAmbientCollisionLeftCarrierPoint

/-- The second collision midpoint in the realization of the ambient complex. -/
noncomputable def minimalHopfAmbientCollisionRightBallPoint :
    SSet.toTop.obj (orderedSSet minimalHopfBallFacets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
    minimalHopfBallFacets).symm
      minimalHopfAmbientCollisionRightCarrierPoint

/-- The two collision midpoints remain distinct in the ambient realization. -/
theorem minimalHopfAmbientCollisionBallPoints_ne :
    minimalHopfAmbientCollisionLeftBallPoint ≠
      minimalHopfAmbientCollisionRightBallPoint := by
  intro h
  apply minimalHopfAmbientCollisionCarrierPoints_ne
  have h' := congrArg
    (orderedRealizationHomeomorphFacetFamilyCarrier minimalHopfBallFacets) h
  simpa [minimalHopfAmbientCollisionLeftBallPoint,
    minimalHopfAmbientCollisionRightBallPoint] using h'

/-- The realized ambient quotient identifies the two collision midpoints. -/
theorem minimalHopfAmbientCollisionBallQuotient_eq :
    minimalHopfBallQuotientRealizationMap
        minimalHopfAmbientCollisionLeftBallPoint =
      minimalHopfBallQuotientRealizationMap
        minimalHopfAmbientCollisionRightBallPoint := by
  apply (orderedRealizationHomeomorphFacetFamilyCarrier facets).injective
  calc
    orderedRealizationToFacetFamilyCarrier facets
        (minimalHopfBallQuotientRealizationMap
          minimalHopfAmbientCollisionLeftBallPoint) =
      facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
          (orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
            minimalHopfAmbientCollisionLeftBallPoint) := by
      simpa [ConcreteCategory.comp_apply,
        facetFamilyCarrierHomOfMonotone] using
        ConcreteCategory.congr_hom
          minimalHopfBallQuotientRealization_carrier_naturality
          minimalHopfAmbientCollisionLeftBallPoint
    _ = facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
          minimalHopfAmbientCollisionLeftCarrierPoint := by
      rw [show orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
          minimalHopfAmbientCollisionLeftBallPoint =
            minimalHopfAmbientCollisionLeftCarrierPoint by
        exact (orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfBallFacets).apply_symm_apply _]
    _ = facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
          minimalHopfAmbientCollisionRightCarrierPoint :=
      minimalHopfAmbientCollisionCarrierQuotient_eq
    _ = facetFamilyCarrierMapOfMonotone minimalHopfQuotientVertex
        minimalHopfBallFacetFamilyMapsTo
          (orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
            minimalHopfAmbientCollisionRightBallPoint) := by
      rw [show orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
          minimalHopfAmbientCollisionRightBallPoint =
            minimalHopfAmbientCollisionRightCarrierPoint by
        exact (orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfBallFacets).apply_symm_apply _]
    _ = orderedRealizationToFacetFamilyCarrier facets
        (minimalHopfBallQuotientRealizationMap
          minimalHopfAmbientCollisionRightBallPoint) := by
      simpa [ConcreteCategory.comp_apply,
        facetFamilyCarrierHomOfMonotone] using
        (ConcreteCategory.congr_hom
          minimalHopfBallQuotientRealization_carrier_naturality
          minimalHopfAmbientCollisionRightBallPoint).symm

private theorem minimalHopfBoundaryCarrier_coord_two_eq_zero
    (x : facetFamilyCarrier minimalHopfSphereFacets) :
    x.1 (2 : MinimalHopfBallVertex) = 0 := by
  obtain ⟨facet, hfacet, hx⟩ :=
    (mem_facetFamilyCarrier_iff minimalHopfSphereFacets x.1).mp x.2
  apply hx
  intro htwo
  exact (by decide : (2 : MinimalHopfBallVertex) ∉
    minimalHopfBoundaryVertexSupport)
      (minimalHopfSphereFacet_subset_boundaryVertexSupport facet hfacet htwo)

/-- The first collision midpoint is an interior point: it is not in the image of the realized
boundary inclusion. -/
theorem minimalHopfAmbientCollisionLeftBallPoint_not_mem_boundary_range :
    minimalHopfAmbientCollisionLeftBallPoint ∉
      Set.range (SSet.toTop.map minimalHopfSphereSSetIncl) := by
  rintro ⟨x, hx⟩
  have hcarrier : minimalHopfAmbientCollisionLeftCarrierPoint =
      facetFamilyCarrierMapOfFacetFamilyLE minimalHopfSphereFacets_le_ball
        (orderedRealizationToFacetFamilyCarrier minimalHopfSphereFacets x) := by
    calc
      minimalHopfAmbientCollisionLeftCarrierPoint =
          orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
            minimalHopfAmbientCollisionLeftBallPoint :=
        (orderedRealizationHomeomorphFacetFamilyCarrier
          minimalHopfBallFacets).apply_symm_apply _ |>.symm
      _ = orderedRealizationToFacetFamilyCarrier minimalHopfBallFacets
          (SSet.toTop.map minimalHopfSphereSSetIncl x) := congrArg _ hx.symm
      _ = facetFamilyCarrierMapOfFacetFamilyLE minimalHopfSphereFacets_le_ball
          (orderedRealizationToFacetFamilyCarrier minimalHopfSphereFacets x) := by
        simpa [ConcreteCategory.comp_apply, minimalHopfSphereSSetIncl,
          facetFamilyCarrierHomOfFacetFamilyLE] using
          ConcreteCategory.congr_hom
            (orderedRealizationToFacetFamilyCarrier_naturality
              minimalHopfSphereFacets_le_ball) x
  have hcoord := congrArg
    (fun y : facetFamilyCarrier minimalHopfBallFacets =>
      y.1 (2 : MinimalHopfBallVertex)) hcarrier
  change minimalHopfAmbientCollisionLeftCarrierPoint.1
      (2 : MinimalHopfBallVertex) =
    (orderedRealizationToFacetFamilyCarrier
      minimalHopfSphereFacets x).1 2 at hcoord
  rw [minimalHopfAmbientCollisionLeftCarrierPoint_coord_two,
    minimalHopfBoundaryCarrier_coord_two_eq_zero] at hcoord
  norm_num at hcoord

/-- The two ambient collision midpoints remain distinct after inclusion into the genuine
topological pushout. The only new equalities between ambient points in a pushout must come from
the boundary, while the first midpoint has positive weight at an interior vertex. -/
theorem minimalHopfAmbientCollisionStrictPushoutPoints_ne :
    SSet.toTop.map minimalHopfStrictPushoutBallIncl
        minimalHopfAmbientCollisionLeftBallPoint ≠
      SSet.toTop.map minimalHopfStrictPushoutBallIncl
        minimalHopfAmbientCollisionRightBallPoint := by
  intro h
  let hpo := minimalHopfStrictPushoutRealization_isPushout.map (forget TopCat)
  have hincl : Function.Injective
      ((forget TopCat).map (SSet.toTop.map minimalHopfSphereSSetIncl)) := by
    simpa [minimalHopfSphereSSetIncl] using
      orderedRealizationMapOfFacetFamilyLE_injective
        minimalHopfSphereFacets_le_ball
  change hpo.cocone.inl minimalHopfAmbientCollisionLeftBallPoint =
    hpo.cocone.inl minimalHopfAmbientCollisionRightBallPoint at h
  rcases (pushoutCocone_inl_eq_inl_iff_of_isColimit
      hpo.isColimit hincl minimalHopfAmbientCollisionLeftBallPoint
        minimalHopfAmbientCollisionRightBallPoint).mp h with
    hpoints | hboundary
  · exact minimalHopfAmbientCollisionBallPoints_ne hpoints
  · rcases hboundary with ⟨s, t, hst, hleft, hright⟩
    exact minimalHopfAmbientCollisionLeftBallPoint_not_mem_boundary_range
      ⟨s, hleft.symm⟩

/-- The realized strict-pushout comparison identifies the two displayed, distinct pushout
points. -/
theorem minimalHopfAmbientCollisionStrictPushoutComparison_eq :
    minimalHopfStrictPushoutComparisonRealization
        (SSet.toTop.map minimalHopfStrictPushoutBallIncl
          minimalHopfAmbientCollisionLeftBallPoint) =
      minimalHopfStrictPushoutComparisonRealization
        (SSet.toTop.map minimalHopfStrictPushoutBallIncl
          minimalHopfAmbientCollisionRightBallPoint) := by
  calc
    _ = minimalHopfBallQuotientRealizationMap
        minimalHopfAmbientCollisionLeftBallPoint := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom
          minimalHopfStrictPushoutBallIncl_comparison_realization
          minimalHopfAmbientCollisionLeftBallPoint
    _ = minimalHopfBallQuotientRealizationMap
        minimalHopfAmbientCollisionRightBallPoint :=
      minimalHopfAmbientCollisionBallQuotient_eq
    _ = _ := by
      simpa only [ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom
          minimalHopfStrictPushoutBallIncl_comparison_realization
          minimalHopfAmbientCollisionRightBallPoint).symm

/-- **The genuine realized pushout comparison is not injective.**  The extra finite-quotient
identification survives geometric realization on the two explicit interior-edge midpoints. -/
theorem minimalHopfStrictPushoutComparisonRealization_not_injective :
    ¬ Function.Injective minimalHopfStrictPushoutComparisonRealization := by
  intro hinjective
  exact minimalHopfAmbientCollisionStrictPushoutPoints_ne
    (hinjective minimalHopfAmbientCollisionStrictPushoutComparison_eq)

/-- The finite ambient quotient remains surjective after geometric realization. -/
theorem minimalHopfBallQuotientRealizationMap_surjective :
    Function.Surjective minimalHopfBallQuotientRealizationMap := by
  rw [← TopCat.epi_iff_surjective]
  unfold minimalHopfBallQuotientRealizationMap
  infer_instance

/-- The realized finite ambient map presents the projective-plane realization with its quotient
topology.  This uses compactness of the finite source polyhedron and Hausdorffness of the finite
target polyhedron. -/
theorem minimalHopfBallQuotientRealizationMap_isQuotientMap :
    Topology.IsQuotientMap minimalHopfBallQuotientRealizationMap := by
  letI : CompactSpace
      (SSet.toTop.obj (orderedSSet minimalHopfBallFacets)) :=
    (orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfBallFacets).symm.compactSpace
  letI : T2Space projectivePlaneRealization :=
    (orderedRealizationHomeomorphFacetFamilyCarrier facets).symm.t2Space
  exact Topology.IsQuotientMap.of_surjective_continuous
    minimalHopfBallQuotientRealizationMap_surjective
    minimalHopfBallQuotientRealizationMap.hom.continuous

/-- The realized comparison is surjective.  Geometric realization preserves the simplicial
epimorphism, and epimorphisms of topological spaces are precisely the surjective maps. -/
theorem minimalHopfStrictPushoutComparisonRealization_surjective :
    Function.Surjective minimalHopfStrictPushoutComparisonRealization := by
  rw [← TopCat.epi_iff_surjective]
  unfold minimalHopfStrictPushoutComparisonRealization
  infer_instance

/-- The realized comparison equips the finite projective-plane realization with the quotient
topology induced by the genuine Hopf pushout. -/
theorem minimalHopfStrictPushoutComparisonRealization_isQuotientMap :
    Topology.IsQuotientMap minimalHopfStrictPushoutComparisonRealization := by
  letI : T2Space projectivePlaneRealization :=
    (orderedRealizationHomeomorphFacetFamilyCarrier facets).symm.t2Space
  exact Topology.IsQuotientMap.of_surjective_continuous
    minimalHopfStrictPushoutComparisonRealization_surjective
    minimalHopfStrictPushoutComparisonRealization.hom.continuous

end Submission.ComplexProjectivePlaneTriangulation
