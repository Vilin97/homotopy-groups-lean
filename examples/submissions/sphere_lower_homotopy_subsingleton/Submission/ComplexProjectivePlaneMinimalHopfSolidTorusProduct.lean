/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfSolidTorusDecomposition
import Submission.FiniteOrderedSimplexRealization

/-!
# The nine-tetrahedron Hopf piece is a solid torus

The preimage of the target triangle `ABC` in the minimal finite Hopf map has one vertex
`Xᵢ` for each target vertex `X = A,B,C` and each fiber vertex `i = 0,1,2`.  Its nine
tetrahedra triangulate the product of the full target triangle with the triangular fiber circle.

This file proves that assertion directly.  On affine carriers the forward map takes target-letter
and fiber-index marginals.  For each of the three fiber edges, an explicit three-region coupling
is the inverse.  The regions are exactly the three tetrahedra over that edge.  Thus the marginal
map is a continuous bijection from a compact space to a Hausdorff space, hence a homeomorphism.
Combining this with finite realization/carrier comparison identifies the actual nine-tetrahedron
piece with the exact metric product `D² × S¹`.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped BigOperators

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The nine-vertex product complex -/

/-- The `ABC` piece after translating its consecutive vertices `5,…,13` to `Fin 9`. -/
def minimalHopfABCPreimageFinNineFacets : Finset (Finset (Fin 9)) :=
  { {0, 1, 4, 7}, {0, 2, 3, 8}, {0, 3, 4, 7},
    {0, 3, 6, 7}, {0, 3, 6, 8}, {1, 2, 4, 7},
    {2, 3, 5, 8}, {2, 4, 5, 8}, {2, 4, 7, 8} }

theorem map_minimalHopfABCPreimageFinNineFacets :
    mapFacets minimalHopfABCOrderEmbedding.toEmbedding
        minimalHopfABCPreimageFinNineFacets =
      minimalHopfABCPreimageFacets := by
  decide

/-- Ordered reindexing identifies the actual `ABC` piece with its nine-vertex copy. -/
noncomputable def minimalHopfABCPreimageSSetIsoFinNine :
    orderedSSet minimalHopfABCPreimageFacets ≅
      orderedSSet minimalHopfABCPreimageFinNineFacets :=
  (orderedSSetMapFacetsIso minimalHopfABCOrderEmbedding
      minimalHopfABCPreimageFinNineFacets ≪≫
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        map_minimalHopfABCPreimageFinNineFacets)).symm

/-- The full two-simplex on three target-letter vertices. -/
def triangleThreeFacets : Finset (Finset (Fin 3)) :=
  {Finset.univ}

abbrev TriangleThreeCarrier :=
  facetFamilyCarrier triangleThreeFacets

abbrev MinimalHopfABCSolidTorusCarrier :=
  facetFamilyCarrier minimalHopfABCPreimageFinNineFacets

/-! ## Target-letter and fiber-index marginals -/

/-- Target-letter marginal of a barycentric point. -/
def minimalHopfABCSolidTorusRowCoord
    (x : MinimalHopfABCSolidTorusCarrier) (i : Fin 3) : ℝ :=
  ![x.1.1 0 + x.1.1 1 + x.1.1 2,
    x.1.1 3 + x.1.1 4 + x.1.1 5,
    x.1.1 6 + x.1.1 7 + x.1.1 8] i

/-- Fiber-index marginal of a barycentric point. -/
def minimalHopfABCSolidTorusColumnCoord
    (x : MinimalHopfABCSolidTorusCarrier) (i : Fin 3) : ℝ :=
  ![x.1.1 0 + x.1.1 3 + x.1.1 6,
    x.1.1 1 + x.1.1 4 + x.1.1 7,
    x.1.1 2 + x.1.1 5 + x.1.1 8] i

theorem minimalHopfABCSolidTorusRowCoord_nonneg
    (x : MinimalHopfABCSolidTorusCarrier) (i : Fin 3) :
    0 ≤ minimalHopfABCSolidTorusRowCoord x i := by
  fin_cases i <;> simp only [minimalHopfABCSolidTorusRowCoord]
  all_goals
    exact add_nonneg (add_nonneg (x.1.2.1 _) (x.1.2.1 _)) (x.1.2.1 _)

theorem minimalHopfABCSolidTorusColumnCoord_nonneg
    (x : MinimalHopfABCSolidTorusCarrier) (i : Fin 3) :
    0 ≤ minimalHopfABCSolidTorusColumnCoord x i := by
  fin_cases i <;> simp only [minimalHopfABCSolidTorusColumnCoord]
  all_goals
    exact add_nonneg (add_nonneg (x.1.2.1 _) (x.1.2.1 _)) (x.1.2.1 _)

theorem minimalHopfABCSolidTorusRowCoord_sum
    (x : MinimalHopfABCSolidTorusCarrier) :
    ∑ i, minimalHopfABCSolidTorusRowCoord x i = 1 := by
  have hx := x.1.2.2
  simp [minimalHopfABCSolidTorusRowCoord, Fin.sum_univ_succ] at ⊢ hx
  linarith

theorem minimalHopfABCSolidTorusColumnCoord_sum
    (x : MinimalHopfABCSolidTorusCarrier) :
    ∑ i, minimalHopfABCSolidTorusColumnCoord x i = 1 := by
  have hx := x.1.2.2
  simp [minimalHopfABCSolidTorusColumnCoord, Fin.sum_univ_succ] at ⊢ hx
  linarith

def minimalHopfABCSolidTorusRowSimplex
    (x : MinimalHopfABCSolidTorusCarrier) : stdSimplex ℝ (Fin 3) :=
  ⟨minimalHopfABCSolidTorusRowCoord x,
    minimalHopfABCSolidTorusRowCoord_nonneg x,
    minimalHopfABCSolidTorusRowCoord_sum x⟩

def minimalHopfABCSolidTorusColumnSimplex
    (x : MinimalHopfABCSolidTorusCarrier) : stdSimplex ℝ (Fin 3) :=
  ⟨minimalHopfABCSolidTorusColumnCoord x,
    minimalHopfABCSolidTorusColumnCoord_nonneg x,
    minimalHopfABCSolidTorusColumnCoord_sum x⟩

theorem minimalHopfABCPreimageFinNineFacets_column_image
    (facet : Finset (Fin 9))
    (hfacet : facet ∈ minimalHopfABCPreimageFinNineFacets) :
    facet.image productTorusColumnVertex ∈ triangleBoundaryThreeFacets := by
  exact (by decide : ∀ facet : Finset (Fin 9),
    facet ∈ minimalHopfABCPreimageFinNineFacets →
      facet.image productTorusColumnVertex ∈ triangleBoundaryThreeFacets) facet hfacet

theorem minimalHopfABCSolidTorusRowSimplex_mem
    (x : MinimalHopfABCSolidTorusCarrier) :
    minimalHopfABCSolidTorusRowSimplex x ∈
      facetFamilyCarrier triangleThreeFacets := by
  rw [mem_facetFamilyCarrier_iff]
  refine ⟨Finset.univ, by simp [triangleThreeFacets], ?_⟩
  intro i hi
  exact False.elim (hi (Finset.mem_univ i))

theorem minimalHopfABCSolidTorusColumnSimplex_mem
    (x : MinimalHopfABCSolidTorusCarrier) :
    minimalHopfABCSolidTorusColumnSimplex x ∈
      facetFamilyCarrier triangleBoundaryThreeFacets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff minimalHopfABCPreimageFinNineFacets x.1).mp x.2
  refine (mem_facetFamilyCarrier_iff triangleBoundaryThreeFacets _).mpr
    ⟨facet.image productTorusColumnVertex,
      minimalHopfABCPreimageFinNineFacets_column_image facet hfacet, ?_⟩
  intro i hi
  change minimalHopfABCSolidTorusColumnCoord x i = 0
  have hzero (v : Fin 9) (hv : productTorusColumnVertex v = i) : x.1.1 v = 0 := by
    apply hsupport v
    intro hvfacet
    apply hi
    exact Finset.mem_image.mpr ⟨v, hvfacet, hv⟩
  fin_cases i
  · change x.1.1 0 + x.1.1 3 + x.1.1 6 = 0
    rw [hzero 0 (by decide), hzero 3 (by decide), hzero 6 (by decide)]
    norm_num
  · change x.1.1 1 + x.1.1 4 + x.1.1 7 = 0
    rw [hzero 1 (by decide), hzero 4 (by decide), hzero 7 (by decide)]
    norm_num
  · change x.1.1 2 + x.1.1 5 + x.1.1 8 = 0
    rw [hzero 2 (by decide), hzero 5 (by decide), hzero 8 (by decide)]
    norm_num

/-- The affine product map, given by target and fiber marginals. -/
def minimalHopfABCSolidTorusCarrierToProduct
    (x : MinimalHopfABCSolidTorusCarrier) :
    TriangleThreeCarrier × TriangleBoundaryThreeCarrier :=
  (⟨minimalHopfABCSolidTorusRowSimplex x,
      minimalHopfABCSolidTorusRowSimplex_mem x⟩,
    ⟨minimalHopfABCSolidTorusColumnSimplex x,
      minimalHopfABCSolidTorusColumnSimplex_mem x⟩)

theorem continuous_minimalHopfABCSolidTorusRowCoord (i : Fin 3) :
    Continuous (fun x : MinimalHopfABCSolidTorusCarrier ↦
      minimalHopfABCSolidTorusRowCoord x i) := by
  have hcoord (v : Fin 9) :
      Continuous (fun x : MinimalHopfABCSolidTorusCarrier ↦ x.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  fin_cases i
  · exact ((hcoord 0).add (hcoord 1)).add (hcoord 2)
  · exact ((hcoord 3).add (hcoord 4)).add (hcoord 5)
  · exact ((hcoord 6).add (hcoord 7)).add (hcoord 8)

theorem continuous_minimalHopfABCSolidTorusColumnCoord (i : Fin 3) :
    Continuous (fun x : MinimalHopfABCSolidTorusCarrier ↦
      minimalHopfABCSolidTorusColumnCoord x i) := by
  have hcoord (v : Fin 9) :
      Continuous (fun x : MinimalHopfABCSolidTorusCarrier ↦ x.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  fin_cases i
  · exact ((hcoord 0).add (hcoord 3)).add (hcoord 6)
  · exact ((hcoord 1).add (hcoord 4)).add (hcoord 7)
  · exact ((hcoord 2).add (hcoord 5)).add (hcoord 8)

theorem continuous_minimalHopfABCSolidTorusCarrierToProduct :
    Continuous minimalHopfABCSolidTorusCarrierToProduct := by
  apply Continuous.prodMk <;>
    apply Continuous.subtype_mk <;>
      apply Continuous.subtype_mk <;>
        apply continuous_pi
  · exact continuous_minimalHopfABCSolidTorusRowCoord
  · exact continuous_minimalHopfABCSolidTorusColumnCoord

/-! ## Explicit inverse coupling -/

/-- Barycentric coordinate of the inverse coupling over a selected fiber edge.

For edge `01` the target rows enter the upper endpoint in order `2,1,0`; for edge `02` the
order is `2,0,1`; and for edge `12` it is `0,2,1`.  These are precisely the three staircase
orders displayed by the nine source tetrahedra. -/
def minimalHopfABCSolidTorusCouplingCoord
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier)
    (c : Fin 3) (z : Fin 9) : ℝ :=
  if c = 0 then
    let t := q.1.1 1
    if t ≤ p.1.1 2 then
      if z = 0 then p.1.1 0
      else if z = 3 then p.1.1 1
      else if z = 6 then p.1.1 2 - t
      else if z = 7 then t
      else 0
    else if t ≤ p.1.1 1 + p.1.1 2 then
      if z = 0 then p.1.1 0
      else if z = 3 then p.1.1 1 + p.1.1 2 - t
      else if z = 4 then t - p.1.1 2
      else if z = 7 then p.1.1 2
      else 0
    else
      if z = 0 then 1 - t
      else if z = 1 then t - p.1.1 1 - p.1.1 2
      else if z = 4 then p.1.1 1
      else if z = 7 then p.1.1 2
      else 0
  else if c = 1 then
    let t := q.1.1 2
    if t ≤ p.1.1 2 then
      if z = 0 then p.1.1 0
      else if z = 3 then p.1.1 1
      else if z = 6 then p.1.1 2 - t
      else if z = 8 then t
      else 0
    else if t ≤ p.1.1 0 + p.1.1 2 then
      if z = 0 then p.1.1 0 + p.1.1 2 - t
      else if z = 2 then t - p.1.1 2
      else if z = 3 then p.1.1 1
      else if z = 8 then p.1.1 2
      else 0
    else
      if z = 2 then p.1.1 0
      else if z = 3 then 1 - t
      else if z = 5 then t - p.1.1 0 - p.1.1 2
      else if z = 8 then p.1.1 2
      else 0
  else
    let t := q.1.1 2
    if t ≤ p.1.1 0 then
      if z = 1 then p.1.1 0 - t
      else if z = 2 then t
      else if z = 4 then p.1.1 1
      else if z = 7 then p.1.1 2
      else 0
    else if t ≤ p.1.1 0 + p.1.1 2 then
      if z = 2 then p.1.1 0
      else if z = 4 then p.1.1 1
      else if z = 7 then p.1.1 0 + p.1.1 2 - t
      else if z = 8 then t - p.1.1 0
      else 0
    else
      if z = 2 then p.1.1 0
      else if z = 4 then 1 - t
      else if z = 5 then t - p.1.1 0 - p.1.1 2
      else if z = 8 then p.1.1 2
      else 0

theorem minimalHopfABCSolidTorusCouplingCoord_nonneg
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier)
    (c : Fin 3) (z : Fin 9) :
    0 ≤ minimalHopfABCSolidTorusCouplingCoord p q c z := by
  have hp := p.1.2.1
  have hpsum := p.1.2.2
  have hq := q.1.2.1
  have hq1 := stdSimplex.le_one q.1 (1 : Fin 3)
  have hq2 := stdSimplex.le_one q.1 (2 : Fin 3)
  change q.1.1 1 ≤ 1 at hq1
  change q.1.1 2 ≤ 1 at hq2
  simp [Fin.sum_univ_succ] at hpsum
  fin_cases c <;> simp [minimalHopfABCSolidTorusCouplingCoord] <;>
    split_ifs <;> linarith [hp 0, hp 1, hp 2, hq 1, hq 2]

theorem minimalHopfABCSolidTorusCouplingCoord_sum
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier) (c : Fin 3) :
    ∑ z, minimalHopfABCSolidTorusCouplingCoord p q c z = 1 := by
  have hpsum := p.1.2.2
  simp [Fin.sum_univ_succ] at hpsum
  fin_cases c <;>
    simp [minimalHopfABCSolidTorusCouplingCoord, Fin.sum_univ_succ] <;>
    split_ifs <;> linarith

def minimalHopfABCSolidTorusCouplingSimplex
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier) (c : Fin 3) :
    stdSimplex ℝ (Fin 9) :=
  ⟨minimalHopfABCSolidTorusCouplingCoord p q c,
    minimalHopfABCSolidTorusCouplingCoord_nonneg p q c,
    minimalHopfABCSolidTorusCouplingCoord_sum p q c⟩

theorem minimalHopfABCSolidTorusCouplingSimplex_mem
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier) (c : Fin 3) :
    minimalHopfABCSolidTorusCouplingSimplex p q c ∈
      facetFamilyCarrier minimalHopfABCPreimageFinNineFacets := by
  rw [mem_facetFamilyCarrier_iff]
  fin_cases c
  · by_cases hfirst : q.1.1 1 ≤ p.1.1 2
    · refine ⟨{0, 3, 6, 7}, by decide, ?_⟩
      intro z hz
      change minimalHopfABCSolidTorusCouplingCoord p q 0 z = 0
      fin_cases z <;> simp at hz <;>
        simp [minimalHopfABCSolidTorusCouplingCoord, hfirst]
    · by_cases hsecond : q.1.1 1 ≤ p.1.1 1 + p.1.1 2
      · refine ⟨{0, 3, 4, 7}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 0 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]
      · refine ⟨{0, 1, 4, 7}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 0 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]
  · by_cases hfirst : q.1.1 2 ≤ p.1.1 2
    · refine ⟨{0, 3, 6, 8}, by decide, ?_⟩
      intro z hz
      change minimalHopfABCSolidTorusCouplingCoord p q 1 z = 0
      fin_cases z <;> simp at hz <;>
        simp [minimalHopfABCSolidTorusCouplingCoord, hfirst]
    · by_cases hsecond : q.1.1 2 ≤ p.1.1 0 + p.1.1 2
      · refine ⟨{0, 2, 3, 8}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 1 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]
      · refine ⟨{2, 3, 5, 8}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 1 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]
  · by_cases hfirst : q.1.1 2 ≤ p.1.1 0
    · refine ⟨{1, 2, 4, 7}, by decide, ?_⟩
      intro z hz
      change minimalHopfABCSolidTorusCouplingCoord p q 2 z = 0
      fin_cases z <;> simp at hz <;>
        simp [minimalHopfABCSolidTorusCouplingCoord, hfirst]
    · by_cases hsecond : q.1.1 2 ≤ p.1.1 0 + p.1.1 2
      · refine ⟨{2, 4, 7, 8}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 2 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]
      · refine ⟨{2, 4, 5, 8}, by decide, ?_⟩
        intro z hz
        change minimalHopfABCSolidTorusCouplingCoord p q 2 z = 0
        fin_cases z <;> simp at hz <;>
          simp [minimalHopfABCSolidTorusCouplingCoord, hfirst, hsecond]

def minimalHopfABCSolidTorusCoupling
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier) (c : Fin 3) :
    MinimalHopfABCSolidTorusCarrier :=
  ⟨minimalHopfABCSolidTorusCouplingSimplex p q c,
    minimalHopfABCSolidTorusCouplingSimplex_mem p q c⟩

theorem minimalHopfABCSolidTorusCoupling_marginals
    (p : TriangleThreeCarrier) (q : TriangleBoundaryThreeCarrier) (c : Fin 3)
    (hq : ∀ i, i ∉ triangleBoundaryEdge c → q.1.1 i = 0) :
    minimalHopfABCSolidTorusCarrierToProduct
        (minimalHopfABCSolidTorusCoupling p q c) = (p, q) := by
  have hqzero := hq (triangleBoundaryEdgeMissing c)
    (triangleBoundaryEdgeMissing_not_mem c)
  have hpsum := p.1.2.2
  have hqsum := q.1.2.2
  simp [Fin.sum_univ_succ] at hpsum hqsum
  apply Prod.ext
  · apply Subtype.ext
    apply stdSimplex.ext
    funext i
    change minimalHopfABCSolidTorusRowCoord
        (minimalHopfABCSolidTorusCoupling p q c) i = p.1.1 i
    fin_cases c <;> fin_cases i <;>
      simp [minimalHopfABCSolidTorusRowCoord,
        minimalHopfABCSolidTorusCoupling,
        minimalHopfABCSolidTorusCouplingSimplex,
        minimalHopfABCSolidTorusCouplingCoord,
        triangleBoundaryEdgeMissing] at hqzero ⊢ <;>
      (try split_ifs) <;> linarith
  · apply Subtype.ext
    apply stdSimplex.ext
    funext i
    change minimalHopfABCSolidTorusColumnCoord
        (minimalHopfABCSolidTorusCoupling p q c) i = q.1.1 i
    fin_cases c <;> fin_cases i <;>
      simp [minimalHopfABCSolidTorusColumnCoord,
        minimalHopfABCSolidTorusCoupling,
        minimalHopfABCSolidTorusCouplingSimplex,
        minimalHopfABCSolidTorusCouplingCoord,
        triangleBoundaryEdgeMissing] at hqzero ⊢ <;>
      (try split_ifs) <;> linarith

/-- The selected coupling reconstructs every source point from its two marginals. -/
theorem minimalHopfABCSolidTorusCoupling_marginals_eq_self
    (x : MinimalHopfABCSolidTorusCarrier) (c : Fin 3)
    (hc : ∀ i, i ∉ triangleBoundaryEdge c →
      minimalHopfABCSolidTorusColumnCoord x i = 0) :
    minimalHopfABCSolidTorusCoupling
        (minimalHopfABCSolidTorusCarrierToProduct x).1
        (minimalHopfABCSolidTorusCarrierToProduct x).2 c = x := by
  have hcolzero := hc (triangleBoundaryEdgeMissing c)
    (triangleBoundaryEdgeMissing_not_mem c)
  have hxsum := x.1.2.2
  simp [Fin.sum_univ_succ] at hxsum
  have hx0 := x.1.2.1 (0 : Fin 9)
  have hx1 := x.1.2.1 (1 : Fin 9)
  have hx2 := x.1.2.1 (2 : Fin 9)
  have hx3 := x.1.2.1 (3 : Fin 9)
  have hx4 := x.1.2.1 (4 : Fin 9)
  have hx5 := x.1.2.1 (5 : Fin 9)
  have hx6 := x.1.2.1 (6 : Fin 9)
  have hx7 := x.1.2.1 (7 : Fin 9)
  have hx8 := x.1.2.1 (8 : Fin 9)
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff minimalHopfABCPreimageFinNineFacets x.1).mp x.2
  simp [minimalHopfABCPreimageFinNineFacets] at hfacet
  rcases hfacet with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try have hx0zero : x.1.1 0 = 0 := hsupport 0 (by decide)
    try have hx1zero : x.1.1 1 = 0 := hsupport 1 (by decide)
    try have hx2zero : x.1.1 2 = 0 := hsupport 2 (by decide)
    try have hx3zero : x.1.1 3 = 0 := hsupport 3 (by decide)
    try have hx4zero : x.1.1 4 = 0 := hsupport 4 (by decide)
    try have hx5zero : x.1.1 5 = 0 := hsupport 5 (by decide)
    try have hx6zero : x.1.1 6 = 0 := hsupport 6 (by decide)
    try have hx7zero : x.1.1 7 = 0 := hsupport 7 (by decide)
    try have hx8zero : x.1.1 8 = 0 := hsupport 8 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext z
    change minimalHopfABCSolidTorusCouplingCoord
        (minimalHopfABCSolidTorusCarrierToProduct x).1
        (minimalHopfABCSolidTorusCarrierToProduct x).2 c z = x.1.1 z
    fin_cases c <;> fin_cases z <;>
      simp [minimalHopfABCSolidTorusCouplingCoord,
        minimalHopfABCSolidTorusCarrierToProduct,
        minimalHopfABCSolidTorusRowSimplex,
        minimalHopfABCSolidTorusColumnSimplex,
        minimalHopfABCSolidTorusRowCoord,
        minimalHopfABCSolidTorusColumnCoord,
        triangleBoundaryEdgeMissing] at hcolzero ⊢ <;>
      (try split_ifs) <;> linarith

/-- A deterministic inverse, using a supporting edge of the fiber marginal. -/
def minimalHopfABCSolidTorusProductToCarrier
    (pq : TriangleThreeCarrier × TriangleBoundaryThreeCarrier) :
    MinimalHopfABCSolidTorusCarrier :=
  minimalHopfABCSolidTorusCoupling pq.1 pq.2
    (triangleBoundarySupportEdge pq.2)

theorem minimalHopfABCSolidTorusCarrierToProduct_productToCarrier
    (pq : TriangleThreeCarrier × TriangleBoundaryThreeCarrier) :
    minimalHopfABCSolidTorusCarrierToProduct
        (minimalHopfABCSolidTorusProductToCarrier pq) = pq := by
  rcases pq with ⟨p, q⟩
  exact minimalHopfABCSolidTorusCoupling_marginals p q
    (triangleBoundarySupportEdge q) (triangleBoundarySupportEdge_spec q)

theorem minimalHopfABCSolidTorusProductToCarrier_carrierToProduct
    (x : MinimalHopfABCSolidTorusCarrier) :
    minimalHopfABCSolidTorusProductToCarrier
        (minimalHopfABCSolidTorusCarrierToProduct x) = x := by
  apply minimalHopfABCSolidTorusCoupling_marginals_eq_self
  simpa [minimalHopfABCSolidTorusCarrierToProduct,
    minimalHopfABCSolidTorusColumnSimplex] using
    triangleBoundarySupportEdge_spec
      (minimalHopfABCSolidTorusCarrierToProduct x).2

theorem minimalHopfABCSolidTorusCarrierToProduct_injective :
    Function.Injective minimalHopfABCSolidTorusCarrierToProduct :=
  (show Function.LeftInverse minimalHopfABCSolidTorusProductToCarrier
      minimalHopfABCSolidTorusCarrierToProduct from
    minimalHopfABCSolidTorusProductToCarrier_carrierToProduct).injective

theorem minimalHopfABCSolidTorusCarrierToProduct_surjective :
    Function.Surjective minimalHopfABCSolidTorusCarrierToProduct :=
  (show Function.RightInverse minimalHopfABCSolidTorusProductToCarrier
      minimalHopfABCSolidTorusCarrierToProduct from
    minimalHopfABCSolidTorusCarrierToProduct_productToCarrier).surjective

/-- The nine-tetrahedron affine carrier is the product of the target triangle and fiber circle. -/
noncomputable def minimalHopfABCSolidTorusCarrierHomeomorphProduct :
    MinimalHopfABCSolidTorusCarrier ≃ₜ
      TriangleThreeCarrier × TriangleBoundaryThreeCarrier := by
  letI : T2Space (TriangleThreeCarrier × TriangleBoundaryThreeCarrier) := by
    infer_instance
  exact IsHomeomorph.homeomorph minimalHopfABCSolidTorusCarrierToProduct <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_minimalHopfABCSolidTorusCarrierToProduct,
        minimalHopfABCSolidTorusCarrierToProduct_injective,
        minimalHopfABCSolidTorusCarrierToProduct_surjective⟩

/-! ## Exact solid-torus realization -/

noncomputable def triangleThreeRealizationHomeomorphDiskTwo :
    SSet.toTop.obj (orderedSSet triangleThreeFacets) ≃ₜ TopCat.disk.{0} 2 := by
  let q : orderedSSet triangleThreeFacets ≅
      orderedSSet ({Finset.univ} : Finset (Finset (Fin 3))) :=
    SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex (by rfl))
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso q)).trans
    (simplexRealizationHomeomorphDisk 2
      (Finset.univ : Finset (Fin 3)) (by decide))

noncomputable def triangleThreeCarrierHomeomorphDiskTwo :
    TriangleThreeCarrier ≃ₜ TopCat.disk.{0} 2 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier triangleThreeFacets).symm.trans
    triangleThreeRealizationHomeomorphDiskTwo

/-- The actual nine-tetrahedron `ABC` preimage is exactly the metric solid torus `D² × S¹`. -/
noncomputable def minimalHopfABCPreimageRealizationHomeomorphDiskTwoProdSphereOne :
    SSet.toTop.obj (orderedSSet minimalHopfABCPreimageFacets) ≃ₜ
      TopCat.disk.{0} 2 × SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso minimalHopfABCPreimageSSetIsoFinNine)).trans
    ((orderedRealizationHomeomorphFacetFamilyCarrier
      minimalHopfABCPreimageFinNineFacets).trans
      (minimalHopfABCSolidTorusCarrierHomeomorphProduct.trans
        (Homeomorph.prodCongr triangleThreeCarrierHomeomorphDiskTwo
          triangleBoundaryThreeCarrierHomeomorphSphereOne)))

end Submission.ComplexProjectivePlaneTriangulation
