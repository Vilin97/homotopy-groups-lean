/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallCollapse

/-!
# The genuine ambient pushout of the finite Hopf map

The seventeen-vertex ambient complex, its boundary three-sphere, and the four-triangle Hopf
target map to the maintained nine-vertex projective-plane complex.  Although that square
commutes strictly, it is not itself a pushout: two explicit interior edges outside the boundary
have the same image under the quotient.

This file records that obstruction, constructs the actual simplicial pushout of the boundary
inclusion and finite Hopf map, and defines its canonical comparison with the nine-vertex model.
Geometric realization preserves the genuine pushout.  The comparison is not a simplicial
isomorphism, as forced by the obstruction; proving that its realization is nevertheless a
homotopy equivalence is the next topological comparison step.
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

end Submission.ComplexProjectivePlaneTriangulation
