/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionCentralTorusProduct
import Submission.ComplexProjectivePlaneTrisectionInterfaceHomotopy

/-!
# The product triangulation as a product of circles

The nine-vertex staircase triangulation from the central-torus bistellar certificate realizes as
the product of two triangular-boundary carriers.  The forward map takes row and column marginals
of a barycentric point.  Its inverse is the unique monotone coupling of the two boundary points.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped BigOperators

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The three edges forming the boundary of the standard triangle. -/
def triangleBoundaryThreeFacets : Finset (Finset (Fin 3)) :=
  {{0, 1}, {0, 2}, {1, 2}}

abbrev TriangleBoundaryThreeCarrier :=
  facetFamilyCarrier triangleBoundaryThreeFacets

abbrev TriangleBoundaryProductCarrier :=
  facetFamilyCarrier triangleBoundaryProductFacets

/-- Row coordinate of a product-grid vertex. -/
def productTorusRowVertex : Fin 9 → Fin 3 :=
  ![0, 0, 0, 1, 1, 1, 2, 2, 2]

/-- Column coordinate of a product-grid vertex. -/
def productTorusColumnVertex : Fin 9 → Fin 3 :=
  ![0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- The row marginal of a barycentric point in the product grid. -/
def productTorusRowCoord (x : TriangleBoundaryProductCarrier) (i : Fin 3) : ℝ :=
  ![x.1.1 0 + x.1.1 1 + x.1.1 2,
    x.1.1 3 + x.1.1 4 + x.1.1 5,
    x.1.1 6 + x.1.1 7 + x.1.1 8] i

/-- The column marginal of a barycentric point in the product grid. -/
def productTorusColumnCoord (x : TriangleBoundaryProductCarrier) (i : Fin 3) : ℝ :=
  ![x.1.1 0 + x.1.1 3 + x.1.1 6,
    x.1.1 1 + x.1.1 4 + x.1.1 7,
    x.1.1 2 + x.1.1 5 + x.1.1 8] i

theorem productTorusRowCoord_nonneg (x : TriangleBoundaryProductCarrier) (i : Fin 3) :
    0 ≤ productTorusRowCoord x i := by
  fin_cases i <;> simp only [productTorusRowCoord]
  all_goals
    exact add_nonneg (add_nonneg (x.1.2.1 _) (x.1.2.1 _)) (x.1.2.1 _)

theorem productTorusColumnCoord_nonneg (x : TriangleBoundaryProductCarrier) (i : Fin 3) :
    0 ≤ productTorusColumnCoord x i := by
  fin_cases i <;> simp only [productTorusColumnCoord]
  all_goals
    exact add_nonneg (add_nonneg (x.1.2.1 _) (x.1.2.1 _)) (x.1.2.1 _)

theorem productTorusRowCoord_sum (x : TriangleBoundaryProductCarrier) :
    ∑ i, productTorusRowCoord x i = 1 := by
  have hx := x.1.2.2
  simp [productTorusRowCoord, Fin.sum_univ_succ] at ⊢ hx
  linarith

theorem productTorusColumnCoord_sum (x : TriangleBoundaryProductCarrier) :
    ∑ i, productTorusColumnCoord x i = 1 := by
  have hx := x.1.2.2
  simp [productTorusColumnCoord, Fin.sum_univ_succ] at ⊢ hx
  linarith

def productTorusRowSimplex (x : TriangleBoundaryProductCarrier) :
    stdSimplex ℝ (Fin 3) :=
  ⟨productTorusRowCoord x, productTorusRowCoord_nonneg x,
    productTorusRowCoord_sum x⟩

def productTorusColumnSimplex (x : TriangleBoundaryProductCarrier) :
    stdSimplex ℝ (Fin 3) :=
  ⟨productTorusColumnCoord x, productTorusColumnCoord_nonneg x,
    productTorusColumnCoord_sum x⟩

theorem triangleBoundaryProductFacets_row_image
    (facet : Finset (Fin 9)) (hfacet : facet ∈ triangleBoundaryProductFacets) :
    facet.image productTorusRowVertex ∈ triangleBoundaryThreeFacets := by
  exact (by decide : ∀ facet : Finset (Fin 9),
    facet ∈ triangleBoundaryProductFacets →
      facet.image productTorusRowVertex ∈ triangleBoundaryThreeFacets) facet hfacet

theorem triangleBoundaryProductFacets_column_image
    (facet : Finset (Fin 9)) (hfacet : facet ∈ triangleBoundaryProductFacets) :
    facet.image productTorusColumnVertex ∈ triangleBoundaryThreeFacets := by
  exact (by decide : ∀ facet : Finset (Fin 9),
    facet ∈ triangleBoundaryProductFacets →
      facet.image productTorusColumnVertex ∈ triangleBoundaryThreeFacets) facet hfacet

theorem productTorusRowSimplex_mem (x : TriangleBoundaryProductCarrier) :
    productTorusRowSimplex x ∈ facetFamilyCarrier triangleBoundaryThreeFacets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff triangleBoundaryProductFacets x.1).mp x.2
  refine (mem_facetFamilyCarrier_iff triangleBoundaryThreeFacets _).mpr
    ⟨facet.image productTorusRowVertex,
      triangleBoundaryProductFacets_row_image facet hfacet, ?_⟩
  intro i hi
  change productTorusRowCoord x i = 0
  have hzero (v : Fin 9) (hv : productTorusRowVertex v = i) : x.1.1 v = 0 := by
    apply hsupport v
    intro hvfacet
    apply hi
    exact Finset.mem_image.mpr ⟨v, hvfacet, hv⟩
  fin_cases i
  · change x.1.1 0 + x.1.1 1 + x.1.1 2 = 0
    rw [hzero 0 (by decide), hzero 1 (by decide), hzero 2 (by decide)]
    norm_num
  · change x.1.1 3 + x.1.1 4 + x.1.1 5 = 0
    rw [hzero 3 (by decide), hzero 4 (by decide), hzero 5 (by decide)]
    norm_num
  · change x.1.1 6 + x.1.1 7 + x.1.1 8 = 0
    rw [hzero 6 (by decide), hzero 7 (by decide), hzero 8 (by decide)]
    norm_num

theorem productTorusColumnSimplex_mem (x : TriangleBoundaryProductCarrier) :
    productTorusColumnSimplex x ∈ facetFamilyCarrier triangleBoundaryThreeFacets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff triangleBoundaryProductFacets x.1).mp x.2
  refine (mem_facetFamilyCarrier_iff triangleBoundaryThreeFacets _).mpr
    ⟨facet.image productTorusColumnVertex,
      triangleBoundaryProductFacets_column_image facet hfacet, ?_⟩
  intro i hi
  change productTorusColumnCoord x i = 0
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

def productTorusCarrierToBoundaryProduct (x : TriangleBoundaryProductCarrier) :
    TriangleBoundaryThreeCarrier × TriangleBoundaryThreeCarrier :=
  (⟨productTorusRowSimplex x, productTorusRowSimplex_mem x⟩,
    ⟨productTorusColumnSimplex x, productTorusColumnSimplex_mem x⟩)

theorem continuous_productTorusRowCoord (i : Fin 3) :
    Continuous (fun x : TriangleBoundaryProductCarrier ↦ productTorusRowCoord x i) := by
  have hcoord (v : Fin 9) :
      Continuous (fun x : TriangleBoundaryProductCarrier ↦ x.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  fin_cases i
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 0 + x.1.1 1) + x.1.1 2)
    exact ((hcoord 0).add (hcoord 1)).add (hcoord 2)
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 3 + x.1.1 4) + x.1.1 5)
    exact ((hcoord 3).add (hcoord 4)).add (hcoord 5)
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 6 + x.1.1 7) + x.1.1 8)
    exact ((hcoord 6).add (hcoord 7)).add (hcoord 8)

theorem continuous_productTorusColumnCoord (i : Fin 3) :
    Continuous (fun x : TriangleBoundaryProductCarrier ↦ productTorusColumnCoord x i) := by
  have hcoord (v : Fin 9) :
      Continuous (fun x : TriangleBoundaryProductCarrier ↦ x.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  fin_cases i
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 0 + x.1.1 3) + x.1.1 6)
    exact ((hcoord 0).add (hcoord 3)).add (hcoord 6)
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 1 + x.1.1 4) + x.1.1 7)
    exact ((hcoord 1).add (hcoord 4)).add (hcoord 7)
  · change Continuous (fun x : TriangleBoundaryProductCarrier ↦
      (x.1.1 2 + x.1.1 5) + x.1.1 8)
    exact ((hcoord 2).add (hcoord 5)).add (hcoord 8)

theorem continuous_productTorusCarrierToBoundaryProduct :
    Continuous productTorusCarrierToBoundaryProduct := by
  apply Continuous.prodMk <;>
    apply Continuous.subtype_mk <;>
      apply Continuous.subtype_mk <;>
        apply continuous_pi
  · exact continuous_productTorusRowCoord
  · exact continuous_productTorusColumnCoord

/-! ## The monotone-coupling inverse -/

/-- Enumeration of the three boundary edges. -/
def triangleBoundaryEdge (k : Fin 3) : Finset (Fin 3) :=
  ![{0, 1}, {0, 2}, {1, 2}] k

/-- Lower endpoint of an enumerated boundary edge. -/
def triangleBoundaryEdgeLow : Fin 3 → Fin 3 := ![0, 0, 1]

/-- Upper endpoint of an enumerated boundary edge. -/
def triangleBoundaryEdgeHigh : Fin 3 → Fin 3 := ![1, 2, 2]

/-- The vertex omitted by an enumerated boundary edge. -/
def triangleBoundaryEdgeMissing : Fin 3 → Fin 3 := ![2, 1, 0]

theorem triangleBoundaryEdge_eq (k : Fin 3) :
    triangleBoundaryEdge k =
      {triangleBoundaryEdgeLow k, triangleBoundaryEdgeHigh k} := by
  fin_cases k <;> decide

theorem triangleBoundaryEdgeLow_lt_high (k : Fin 3) :
    triangleBoundaryEdgeLow k < triangleBoundaryEdgeHigh k := by
  fin_cases k <;> decide

theorem triangleBoundaryEdgeMissing_not_mem (k : Fin 3) :
    triangleBoundaryEdgeMissing k ∉ triangleBoundaryEdge k := by
  fin_cases k <;> decide

theorem exists_triangleBoundarySupportEdge (p : TriangleBoundaryThreeCarrier) :
    ∃ k : Fin 3, ∀ i, i ∉ triangleBoundaryEdge k → p.1.1 i = 0 := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff triangleBoundaryThreeFacets p.1).mp p.2
  obtain ⟨k, hk⟩ := (by
    exact (by decide : ∀ facet : Finset (Fin 3),
      facet ∈ triangleBoundaryThreeFacets →
        ∃ k : Fin 3, triangleBoundaryEdge k = facet) facet hfacet)
  subst facet
  exact ⟨k, hsupport⟩

/-- A deterministic supporting boundary edge for a triangular-boundary carrier point. -/
noncomputable def triangleBoundarySupportEdge (p : TriangleBoundaryThreeCarrier) : Fin 3 :=
  (exists_triangleBoundarySupportEdge p).choose

theorem triangleBoundarySupportEdge_spec (p : TriangleBoundaryThreeCarrier) :
    ∀ i, i ∉ triangleBoundaryEdge (triangleBoundarySupportEdge p) → p.1.1 i = 0 :=
  (exists_triangleBoundarySupportEdge p).choose_spec

/-- Row-major index of a product-grid vertex. -/
def productGridVertex (i j : Fin 3) : Fin 9 :=
  ![![0, 1, 2], ![3, 4, 5], ![6, 7, 8]] i j

/-- Barycentric coordinates of the monotone coupling on a selected pair of boundary edges. -/
def staircaseCouplingCoord
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) (z : Fin 9) : ℝ :=
  let a := triangleBoundaryEdgeLow r
  let b := triangleBoundaryEdgeHigh r
  let d := triangleBoundaryEdgeHigh c
  if p.1.1 b ≤ q.1.1 d then
    if z = productGridVertex a (triangleBoundaryEdgeLow c) then 1 - q.1.1 d
    else if z = productGridVertex a d then q.1.1 d - p.1.1 b
    else if z = productGridVertex b d then p.1.1 b
    else 0
  else
    if z = productGridVertex a (triangleBoundaryEdgeLow c) then 1 - p.1.1 b
    else if z = productGridVertex b (triangleBoundaryEdgeLow c) then
      p.1.1 b - q.1.1 d
    else if z = productGridVertex b d then q.1.1 d
    else 0

theorem staircaseCouplingCoord_nonneg
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) (z : Fin 9) :
    0 ≤ staircaseCouplingCoord p q r c z := by
  have hp0 := p.1.2.1 (triangleBoundaryEdgeHigh r)
  have hq0 := q.1.2.1 (triangleBoundaryEdgeHigh c)
  have hp1 : p.1.1 (triangleBoundaryEdgeHigh r) ≤ 1 :=
    stdSimplex.le_one p.1 (triangleBoundaryEdgeHigh r)
  have hq1 : q.1.1 (triangleBoundaryEdgeHigh c) ≤ 1 :=
    stdSimplex.le_one q.1 (triangleBoundaryEdgeHigh c)
  simp only [staircaseCouplingCoord]
  split_ifs <;> linarith

theorem staircaseCouplingCoord_sum
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) :
    ∑ z, staircaseCouplingCoord p q r c z = 1 := by
  fin_cases r <;> fin_cases c <;>
    simp [staircaseCouplingCoord, triangleBoundaryEdgeLow,
      triangleBoundaryEdgeHigh, productGridVertex, Fin.sum_univ_succ]

def staircaseCouplingSimplex
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) :
    stdSimplex ℝ (Fin 9) :=
  ⟨staircaseCouplingCoord p q r c,
    staircaseCouplingCoord_nonneg p q r c,
    staircaseCouplingCoord_sum p q r c⟩

theorem staircaseCouplingSimplex_mem
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) :
    staircaseCouplingSimplex p q r c ∈
      facetFamilyCarrier triangleBoundaryProductFacets := by
  rw [mem_facetFamilyCarrier_iff]
  by_cases h : p.1.1 (triangleBoundaryEdgeHigh r) ≤
      q.1.1 (triangleBoundaryEdgeHigh c)
  · let facet : Finset (Fin 9) :=
      {productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeLow c),
        productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeHigh c),
        productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeHigh c)}
    refine ⟨facet, ?_, ?_⟩
    · fin_cases r <;> fin_cases c <;> decide
    · intro z hz
      have hz₀ : z ≠
          productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeLow c) := by
        intro heq
        apply hz
        simp [facet, heq]
      have hz₁ : z ≠
          productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeHigh c) := by
        intro heq
        apply hz
        simp [facet, heq]
      have hz₂ : z ≠
          productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeHigh c) := by
        intro heq
        apply hz
        simp [facet, heq]
      change staircaseCouplingCoord p q r c z = 0
      simp [staircaseCouplingCoord, h, hz₀, hz₁, hz₂]
  · let facet : Finset (Fin 9) :=
      {productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeLow c),
        productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeLow c),
        productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeHigh c)}
    refine ⟨facet, ?_, ?_⟩
    · fin_cases r <;> fin_cases c <;> decide
    · intro z hz
      have hz₀ : z ≠
          productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeLow c) := by
        intro heq
        apply hz
        simp [facet, heq]
      have hz₁ : z ≠
          productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeLow c) := by
        intro heq
        apply hz
        simp [facet, heq]
      have hz₂ : z ≠
          productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeHigh c) := by
        intro heq
        apply hz
        simp [facet, heq]
      change staircaseCouplingCoord p q r c z = 0
      simp [staircaseCouplingCoord, h, hz₀, hz₁, hz₂]

def staircaseCoupling
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3) :
    TriangleBoundaryProductCarrier :=
  ⟨staircaseCouplingSimplex p q r c, staircaseCouplingSimplex_mem p q r c⟩

/-- No product-triangulation facet contains both vertices that cross in a selected grid square. -/
theorem triangleBoundaryProductFacet_no_crossing
    (facet : Finset (Fin 9)) (hfacet : facet ∈ triangleBoundaryProductFacets)
    (r c : Fin 3) :
    productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeHigh c) ∉ facet ∨
      productGridVertex (triangleBoundaryEdgeHigh r) (triangleBoundaryEdgeLow c) ∉ facet := by
  exact (by decide : ∀ facet : Finset (Fin 9),
    facet ∈ triangleBoundaryProductFacets → ∀ r c : Fin 3,
      productGridVertex (triangleBoundaryEdgeLow r) (triangleBoundaryEdgeHigh c) ∉ facet ∨
        productGridVertex (triangleBoundaryEdgeHigh r)
          (triangleBoundaryEdgeLow c) ∉ facet) facet hfacet r c

/-- Every carrier point has a zero on at least one of the two crossing vertices of each selected
grid square. -/
theorem productTorusCarrier_crossing_zero
    (x : TriangleBoundaryProductCarrier) (r c : Fin 3) :
    x.1.1 (productGridVertex (triangleBoundaryEdgeLow r)
        (triangleBoundaryEdgeHigh c)) = 0 ∨
      x.1.1 (productGridVertex (triangleBoundaryEdgeHigh r)
        (triangleBoundaryEdgeLow c)) = 0 := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff triangleBoundaryProductFacets x.1).mp x.2
  rcases triangleBoundaryProductFacet_no_crossing facet hfacet r c with h | h
  · exact Or.inl (hsupport _ h)
  · exact Or.inr (hsupport _ h)

theorem productTorusCoord_eq_zero_of_rowCoord_eq_zero
    (x : TriangleBoundaryProductCarrier) (i j : Fin 3)
    (h : productTorusRowCoord x i = 0) :
    x.1.1 (productGridVertex i j) = 0 := by
  have hx0 := x.1.2.1 (0 : Fin 9)
  have hx1 := x.1.2.1 (1 : Fin 9)
  have hx2 := x.1.2.1 (2 : Fin 9)
  have hx3 := x.1.2.1 (3 : Fin 9)
  have hx4 := x.1.2.1 (4 : Fin 9)
  have hx5 := x.1.2.1 (5 : Fin 9)
  have hx6 := x.1.2.1 (6 : Fin 9)
  have hx7 := x.1.2.1 (7 : Fin 9)
  have hx8 := x.1.2.1 (8 : Fin 9)
  fin_cases i <;> fin_cases j <;>
    simp [productTorusRowCoord, productGridVertex] at h ⊢ <;> linarith

theorem productTorusCoord_eq_zero_of_columnCoord_eq_zero
    (x : TriangleBoundaryProductCarrier) (i j : Fin 3)
    (h : productTorusColumnCoord x j = 0) :
    x.1.1 (productGridVertex i j) = 0 := by
  have hx0 := x.1.2.1 (0 : Fin 9)
  have hx1 := x.1.2.1 (1 : Fin 9)
  have hx2 := x.1.2.1 (2 : Fin 9)
  have hx3 := x.1.2.1 (3 : Fin 9)
  have hx4 := x.1.2.1 (4 : Fin 9)
  have hx5 := x.1.2.1 (5 : Fin 9)
  have hx6 := x.1.2.1 (6 : Fin 9)
  have hx7 := x.1.2.1 (7 : Fin 9)
  have hx8 := x.1.2.1 (8 : Fin 9)
  fin_cases i <;> fin_cases j <;>
    simp [productTorusColumnCoord, productGridVertex] at h ⊢ <;> linarith

/-- The monotone coupling reconstructs a product-triangulation point from its marginals whenever
the selected boundary edges support those marginals. -/
theorem staircaseCoupling_marginals_eq_self
    (x : TriangleBoundaryProductCarrier) (r c : Fin 3)
    (hr : productTorusRowCoord x (triangleBoundaryEdgeMissing r) = 0)
    (hc : productTorusColumnCoord x (triangleBoundaryEdgeMissing c) = 0) :
    staircaseCoupling (productTorusCarrierToBoundaryProduct x).1
        (productTorusCarrierToBoundaryProduct x).2 r c = x := by
  apply Subtype.ext
  apply stdSimplex.ext
  funext z
  change staircaseCouplingCoord (productTorusCarrierToBoundaryProduct x).1
      (productTorusCarrierToBoundaryProduct x).2 r c z = x.1.1 z
  have hxrow0 (j : Fin 3) :=
    productTorusCoord_eq_zero_of_rowCoord_eq_zero x
      (triangleBoundaryEdgeMissing r) j hr
  have hxcol0 (i : Fin 3) :=
    productTorusCoord_eq_zero_of_columnCoord_eq_zero x i
      (triangleBoundaryEdgeMissing c) hc
  have hxrow0₀ := hxrow0 (0 : Fin 3)
  have hxrow0₁ := hxrow0 (1 : Fin 3)
  have hxrow0₂ := hxrow0 (2 : Fin 3)
  have hxcol0₀ := hxcol0 (0 : Fin 3)
  have hxcol0₁ := hxcol0 (1 : Fin 3)
  have hxcol0₂ := hxcol0 (2 : Fin 3)
  have hxsum := x.1.2.2
  have hx0 := x.1.2.1 (0 : Fin 9)
  have hx1 := x.1.2.1 (1 : Fin 9)
  have hx2 := x.1.2.1 (2 : Fin 9)
  have hx3 := x.1.2.1 (3 : Fin 9)
  have hx4 := x.1.2.1 (4 : Fin 9)
  have hx5 := x.1.2.1 (5 : Fin 9)
  have hx6 := x.1.2.1 (6 : Fin 9)
  have hx7 := x.1.2.1 (7 : Fin 9)
  have hx8 := x.1.2.1 (8 : Fin 9)
  rcases productTorusCarrier_crossing_zero x r c with hcross | hcross <;>
    fin_cases r <;> fin_cases c <;> fin_cases z <;>
    simp [staircaseCouplingCoord, productTorusCarrierToBoundaryProduct,
      productTorusRowSimplex, productTorusColumnSimplex,
      productTorusRowCoord, productTorusColumnCoord,
      triangleBoundaryEdgeLow, triangleBoundaryEdgeHigh,
      triangleBoundaryEdgeMissing, productGridVertex, Fin.sum_univ_succ]
      at hcross hxrow0₀ hxrow0₁ hxrow0₂ hxcol0₀ hxcol0₁ hxcol0₂ hxsum ⊢ <;>
    (try split_ifs) <;> linarith

theorem staircaseCoupling_marginals
    (p q : TriangleBoundaryThreeCarrier) (r c : Fin 3)
    (hp : ∀ i, i ∉ triangleBoundaryEdge r → p.1.1 i = 0)
    (hq : ∀ i, i ∉ triangleBoundaryEdge c → q.1.1 i = 0) :
    productTorusCarrierToBoundaryProduct (staircaseCoupling p q r c) = (p, q) := by
  have hpzero := hp (triangleBoundaryEdgeMissing r)
    (triangleBoundaryEdgeMissing_not_mem r)
  have hqzero := hq (triangleBoundaryEdgeMissing c)
    (triangleBoundaryEdgeMissing_not_mem c)
  have hpsum := p.1.2.2
  have hqsum := q.1.2.2
  apply Prod.ext
  · apply Subtype.ext
    apply stdSimplex.ext
    funext i
    change productTorusRowCoord (staircaseCoupling p q r c) i = p.1.1 i
    fin_cases r <;> fin_cases c <;> fin_cases i <;>
      simp [productTorusRowCoord, staircaseCoupling, staircaseCouplingSimplex,
        staircaseCouplingCoord, triangleBoundaryEdgeLow,
        triangleBoundaryEdgeHigh, triangleBoundaryEdgeMissing,
        productGridVertex, Fin.sum_univ_succ] at hpzero hqzero hpsum hqsum ⊢ <;>
      (try split_ifs) <;> linarith
  · apply Subtype.ext
    apply stdSimplex.ext
    funext i
    change productTorusColumnCoord (staircaseCoupling p q r c) i = q.1.1 i
    fin_cases r <;> fin_cases c <;> fin_cases i <;>
      simp [productTorusColumnCoord, staircaseCoupling, staircaseCouplingSimplex,
        staircaseCouplingCoord, triangleBoundaryEdgeLow,
        triangleBoundaryEdgeHigh, triangleBoundaryEdgeMissing,
        productGridVertex, Fin.sum_univ_succ] at hpzero hqzero hpsum hqsum ⊢ <;>
      (try split_ifs) <;> linarith

/-- The monotone coupling selected from deterministic supporting edges. -/
def boundaryProductToProductTorusCarrier
    (pq : TriangleBoundaryThreeCarrier × TriangleBoundaryThreeCarrier) :
    TriangleBoundaryProductCarrier :=
  staircaseCoupling pq.1 pq.2
    (triangleBoundarySupportEdge pq.1) (triangleBoundarySupportEdge pq.2)

theorem productTorusCarrierToBoundaryProduct_boundaryProductToProductTorusCarrier
    (pq : TriangleBoundaryThreeCarrier × TriangleBoundaryThreeCarrier) :
    productTorusCarrierToBoundaryProduct
        (boundaryProductToProductTorusCarrier pq) = pq := by
  rcases pq with ⟨p, q⟩
  exact staircaseCoupling_marginals p q
    (triangleBoundarySupportEdge p) (triangleBoundarySupportEdge q)
    (triangleBoundarySupportEdge_spec p) (triangleBoundarySupportEdge_spec q)

theorem boundaryProductToProductTorusCarrier_productTorusCarrierToBoundaryProduct
    (x : TriangleBoundaryProductCarrier) :
    boundaryProductToProductTorusCarrier
        (productTorusCarrierToBoundaryProduct x) = x := by
  apply staircaseCoupling_marginals_eq_self x
  · simpa [productTorusCarrierToBoundaryProduct, productTorusRowSimplex] using
      triangleBoundarySupportEdge_spec
        (productTorusCarrierToBoundaryProduct x).1
        (triangleBoundaryEdgeMissing
          (triangleBoundarySupportEdge
            (productTorusCarrierToBoundaryProduct x).1))
        (triangleBoundaryEdgeMissing_not_mem
          (triangleBoundarySupportEdge
            (productTorusCarrierToBoundaryProduct x).1))
  · simpa [productTorusCarrierToBoundaryProduct, productTorusColumnSimplex] using
      triangleBoundarySupportEdge_spec
        (productTorusCarrierToBoundaryProduct x).2
        (triangleBoundaryEdgeMissing
          (triangleBoundarySupportEdge
            (productTorusCarrierToBoundaryProduct x).2))
        (triangleBoundaryEdgeMissing_not_mem
          (triangleBoundarySupportEdge
            (productTorusCarrierToBoundaryProduct x).2))

theorem productTorusCarrierToBoundaryProduct_injective :
    Function.Injective productTorusCarrierToBoundaryProduct :=
  (show Function.LeftInverse boundaryProductToProductTorusCarrier
      productTorusCarrierToBoundaryProduct from
    boundaryProductToProductTorusCarrier_productTorusCarrierToBoundaryProduct).injective

theorem productTorusCarrierToBoundaryProduct_surjective :
    Function.Surjective productTorusCarrierToBoundaryProduct :=
  (show Function.RightInverse boundaryProductToProductTorusCarrier
      productTorusCarrierToBoundaryProduct from
    productTorusCarrierToBoundaryProduct_boundaryProductToProductTorusCarrier).surjective

/-- The nine-vertex staircase carrier is homeomorphic to the product of its two triangular
boundary carriers. -/
noncomputable def productTorusCarrierHomeomorphBoundaryProduct :
    TriangleBoundaryProductCarrier ≃ₜ
      TriangleBoundaryThreeCarrier × TriangleBoundaryThreeCarrier := by
  letI : T2Space (TriangleBoundaryThreeCarrier × TriangleBoundaryThreeCarrier) := by
    infer_instance
  exact IsHomeomorph.homeomorph productTorusCarrierToBoundaryProduct <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_productTorusCarrierToBoundaryProduct,
        productTorusCarrierToBoundaryProduct_injective,
        productTorusCarrierToBoundaryProduct_surjective⟩

/-! ## Identification with the exact product of metric circles -/

/-- The three vertices used for the triangular boundary. -/
def triangleBoundaryThreeVertices : Finset (Fin 3) := Finset.univ

theorem triangleBoundaryThreeFacets_eq_simplexBoundary :
    triangleBoundaryThreeFacets =
      simplexBoundaryFacets triangleBoundaryThreeVertices := by decide

theorem triangleBoundaryThreeVertices_card :
    triangleBoundaryThreeVertices.card = 2 + 1 := by decide

noncomputable def triangleBoundaryThreeSSetIsoBoundaryTwo :
    orderedSSet triangleBoundaryThreeFacets ≅ (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex
        triangleBoundaryThreeFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 triangleBoundaryThreeVertices
      triangleBoundaryThreeVertices_card

noncomputable def triangleBoundaryThreeRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet triangleBoundaryThreeFacets) ≃ₜ SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso triangleBoundaryThreeSSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

noncomputable def triangleBoundaryThreeCarrierHomeomorphSphereOne :
    TriangleBoundaryThreeCarrier ≃ₜ SphereSpace 1 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      triangleBoundaryThreeFacets).symm.trans
    triangleBoundaryThreeRealizationHomeomorphSphereOne

/-- The certified staircase product triangulation realizes as the exact product of two metric
circles. -/
noncomputable def productTorusRealizationHomeomorphSphereOneProduct :
    SSet.toTop.obj (orderedSSet triangleBoundaryProductFacets) ≃ₜ
      SphereSpace 1 × SphereSpace 1 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      triangleBoundaryProductFacets).trans
    (productTorusCarrierHomeomorphBoundaryProduct.trans
      (Homeomorph.prodCongr triangleBoundaryThreeCarrierHomeomorphSphereOne
        triangleBoundaryThreeCarrierHomeomorphSphereOne))

/-- The common central trisection interface is homeomorphic to the exact metric torus
`S¹ × S¹`. -/
noncomputable def centralInterfaceRealizationHomeomorphSphereOneProduct :
    SSet.toTop.obj (orderedSSet centralInterfaceFacets) ≃ₜ
      SphereSpace 1 × SphereSpace 1 :=
  centralInterfaceRealizationHomeomorphProductTriangulation.trans
    productTorusRealizationHomeomorphSphereOneProduct

/-- The fundamental group of the common central trisection interface is `ℤ × ℤ` at every
basepoint. -/
theorem centralInterface_piOne_mulEquiv_int_prod_int
    (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Nonempty
      (HomotopyGroup.Pi 1
          (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) x ≃*
        Multiplicative ℤ × Multiplicative ℤ) := by
  let e := centralInterfaceRealizationHomeomorphSphereOneProduct.toHomotopyEquiv
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin 1) e x
  obtain ⟨circle₁⟩ := pi1_sphere_one_mulEquiv_int_at (e x).1
  obtain ⟨circle₂⟩ := pi1_sphere_one_mulEquiv_int_at (e x).2
  exact ⟨changeSpace.trans
    ((HomotopyGroup.prodMulEquiv (N := Fin 1) (e x).1 (e x).2).trans
      (MulEquiv.prodCongr circle₁ circle₂))⟩

/-- Every homotopy group of the common central trisection interface above degree one vanishes,
at every basepoint. -/
theorem centralInterface_higher_homotopy_subsingleton
    (k : ℕ) (x : SSet.toTop.obj (orderedSSet centralInterfaceFacets)) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2)
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets)) x) := by
  let e := centralInterfaceRealizationHomeomorphSphereOneProduct.toHomotopyEquiv
  letI : Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1 × SphereSpace 1) (e x)) :=
    (homotopyGroup_product_subsingleton_iff (k + 1)
      (SphereSpace 1) (SphereSpace 1) (e x).1 (e x).2).mpr
        ⟨sphere_one_higher_homotopy_subsingleton_at k (e x).1,
          sphere_one_higher_homotopy_subsingleton_at k (e x).2⟩
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin (k + 2)) e x
  exact changeSpace.injective.subsingleton

end Submission.ComplexProjectivePlaneTriangulation
