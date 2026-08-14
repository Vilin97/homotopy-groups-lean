/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionFilling

/-!
# The trisection subdivision realizes the nine-vertex projective plane

The trisection uses a 13-vertex, 78-facet subdivision of the original nine-vertex complex.
This module gives the missing exact comparison. The forward carrier map sends the three new
edge vertices to the corresponding midpoints and the new face vertex to the barycenter of the
triangle on vertices `0`, `4`, and `5`. Its inverse is an explicit min/residual formula.

Six coordinate orderings select the six small triangles in that face. Finite certificates show
that each original facet has the required refinement and every refined facet belongs to one of
those six supports. The coordinate maps are proved inverse, yielding the carrier homeomorphism
and finally `trisectionSubdivisionRealizationHomeomorphProjectivePlane`.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

abbrev TrisectionSubdivisionCarrier :=
  facetFamilyCarrier trisectionSubdivisionFacets

abbrev ProjectivePlaneCarrier := facetFamilyCarrier facets

def trisectionSubdivisionForwardCoord
    (x : TrisectionSubdivisionCarrier) : Vertex → ℝ :=
  ![x.1.1 0 + (1 / 2 : ℝ) * x.1.1 9 + (1 / 2 : ℝ) * x.1.1 10 +
      (1 / 3 : ℝ) * x.1.1 12,
    x.1.1 1,
    x.1.1 2,
    x.1.1 3,
    x.1.1 4 + (1 / 2 : ℝ) * x.1.1 10 + (1 / 2 : ℝ) * x.1.1 11 +
      (1 / 3 : ℝ) * x.1.1 12,
    x.1.1 5 + (1 / 2 : ℝ) * x.1.1 9 + (1 / 2 : ℝ) * x.1.1 11 +
      (1 / 3 : ℝ) * x.1.1 12,
    x.1.1 6,
    x.1.1 7,
    x.1.1 8]

theorem trisectionSubdivisionForwardCoord_nonneg
    (x : TrisectionSubdivisionCarrier) (v : Vertex) :
    0 ≤ trisectionSubdivisionForwardCoord x v := by
  have hx := x.1.2.1
  fin_cases v <;> simp [trisectionSubdivisionForwardCoord] <;>
    norm_num at * <;>
    nlinarith [hx 0, hx 1, hx 2, hx 3, hx 4, hx 5, hx 6, hx 7, hx 8,
      hx 9, hx 10, hx 11, hx 12]

theorem trisectionSubdivisionForwardCoord_sum
    (x : TrisectionSubdivisionCarrier) :
    ∑ v, trisectionSubdivisionForwardCoord x v = 1 := by
  have hx := x.1.2.2
  simp [Fin.sum_univ_succ] at hx
  simp [trisectionSubdivisionForwardCoord, Fin.sum_univ_succ]
  norm_num at ⊢
  linarith

def trisectionSubdivisionForwardSimplex
    (x : TrisectionSubdivisionCarrier) : stdSimplex ℝ Vertex :=
  ⟨trisectionSubdivisionForwardCoord x,
    trisectionSubdivisionForwardCoord_nonneg x,
    trisectionSubdivisionForwardCoord_sum x⟩

theorem trisectionSubdivisionForwardSimplex_mem
    (x : TrisectionSubdivisionCarrier) :
    trisectionSubdivisionForwardSimplex x ∈ facetFamilyCarrier facets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff trisectionSubdivisionFacets x.1).mp x.2
  have hcarrier : trisectionSimplexCarrier facet ∈ facets := by
    rw [← trisectionSimplexCarrier_image]
    exact Finset.mem_image.mpr ⟨facet, hfacet, rfl⟩
  rw [mem_facetFamilyCarrier_iff]
  refine ⟨trisectionSimplexCarrier facet, hcarrier, ?_⟩
  intro v hv
  have hzero (w : TrisectionVertex)
      (hvw : v ∈ trisectionVertexCarrier w) : x.1.1 w = 0 := by
    have hw : w ∉ facet := by
      intro hw
      apply hv
      exact Finset.mem_biUnion.mpr ⟨w, hw, hvw⟩
    have h := hsupport w hw
    change x.1.1 w = 0 at h
    exact h
  change trisectionSubdivisionForwardCoord x v = 0
  fin_cases v
  · simp [trisectionSubdivisionForwardCoord]
    rw [hzero 0 (by decide), hzero 9 (by decide), hzero 10 (by decide),
      hzero 12 (by decide)]
    norm_num
  · exact hzero 1 (by decide)
  · exact hzero 2 (by decide)
  · exact hzero 3 (by decide)
  · simp [trisectionSubdivisionForwardCoord]
    rw [hzero 4 (by decide), hzero 10 (by decide), hzero 11 (by decide),
      hzero 12 (by decide)]
    norm_num
  · simp [trisectionSubdivisionForwardCoord]
    rw [hzero 5 (by decide), hzero 9 (by decide), hzero 11 (by decide),
      hzero 12 (by decide)]
    norm_num
  · exact hzero 6 (by decide)
  · exact hzero 7 (by decide)
  · exact hzero 8 (by decide)

def trisectionSubdivisionCarrierToProjectivePlane
    (x : TrisectionSubdivisionCarrier) : ProjectivePlaneCarrier :=
  ⟨trisectionSubdivisionForwardSimplex x,
    trisectionSubdivisionForwardSimplex_mem x⟩

def subdivisionInverseMin (y : ProjectivePlaneCarrier) : ℝ :=
  min (y.1.1 0) (min (y.1.1 4) (y.1.1 5))

def subdivisionInverseResidualZero (y : ProjectivePlaneCarrier) : ℝ :=
  y.1.1 0 - subdivisionInverseMin y

def subdivisionInverseResidualFour (y : ProjectivePlaneCarrier) : ℝ :=
  y.1.1 4 - subdivisionInverseMin y

def subdivisionInverseResidualFive (y : ProjectivePlaneCarrier) : ℝ :=
  y.1.1 5 - subdivisionInverseMin y

def trisectionSubdivisionInverseCoord
    (y : ProjectivePlaneCarrier) : TrisectionVertex → ℝ :=
  let r0 := subdivisionInverseResidualZero y
  let r4 := subdivisionInverseResidualFour y
  let r5 := subdivisionInverseResidualFive y
  ![r0 - min r0 r5 - min r0 r4,
    y.1.1 1,
    y.1.1 2,
    y.1.1 3,
    r4 - min r0 r4 - min r4 r5,
    r5 - min r0 r5 - min r4 r5,
    y.1.1 6,
    y.1.1 7,
    y.1.1 8,
    2 * min r0 r5,
    2 * min r0 r4,
    2 * min r4 r5,
    3 * subdivisionInverseMin y]

theorem trisectionSubdivisionInverseCoord_nonneg
    (y : ProjectivePlaneCarrier) (v : TrisectionVertex) :
    0 ≤ trisectionSubdivisionInverseCoord y v := by
  have hy := y.1.2.1
  fin_cases v <;>
    simp [trisectionSubdivisionInverseCoord, subdivisionInverseResidualZero,
      subdivisionInverseResidualFour, subdivisionInverseResidualFive,
      subdivisionInverseMin, min_def] <;>
    first
    | exact hy _
    | (split_ifs <;> norm_num at * <;>
        nlinarith [hy 0, hy 1, hy 2, hy 3, hy 4, hy 5, hy 6, hy 7, hy 8])

theorem trisectionSubdivisionInverseCoord_sum
    (y : ProjectivePlaneCarrier) :
    ∑ v, trisectionSubdivisionInverseCoord y v = 1 := by
  have hy := y.1.2.2
  simp [Fin.sum_univ_succ] at hy
  simp [trisectionSubdivisionInverseCoord, Fin.sum_univ_succ]
  ring_nf
  simp [subdivisionInverseResidualZero, subdivisionInverseResidualFour,
    subdivisionInverseResidualFive]
  linarith

def trisectionSubdivisionInverseSimplex
    (y : ProjectivePlaneCarrier) : stdSimplex ℝ TrisectionVertex :=
  ⟨trisectionSubdivisionInverseCoord y,
    trisectionSubdivisionInverseCoord_nonneg y,
    trisectionSubdivisionInverseCoord_sum y⟩

def oldVertexEmbedding : Vertex ↪ TrisectionVertex where
  toFun v := ⟨v.1, by omega⟩
  inj' := by
    intro v w h
    apply Fin.ext
    exact congrArg (fun z : TrisectionVertex ↦ z.val) h

def subdivisionRefinementChain : Fin 6 → Finset TrisectionVertex :=
  ![{5, 11, 12}, {4, 11, 12}, {5, 9, 12},
    {0, 9, 12}, {4, 10, 12}, {0, 10, 12}]

def subdivisionRefinementRequired
    (facet : Finset Vertex) (order : Fin 6) : Finset TrisectionVertex :=
  (facet \ originalTrisectionVertices).map oldVertexEmbedding ∪
    (subdivisionRefinementChain order).filter fun w ↦
      trisectionVertexCarrier w ⊆ facet

def subdivisionRefinementCandidates
    (facet : Finset Vertex) (order : Fin 6) :
    Finset (Finset TrisectionVertex) :=
  trisectionSubdivisionFacets.filter fun refined ↦
    trisectionSimplexCarrier refined = facet ∧
      subdivisionRefinementRequired facet order ⊆ refined

theorem subdivisionRefinementCandidates_nonempty
    (facet : Finset Vertex) (hfacet : facet ∈ facets) (order : Fin 6) :
    (subdivisionRefinementCandidates facet order).Nonempty := by
  exact (by decide : ∀ f : ↥facets, ∀ o : Fin 6,
    (subdivisionRefinementCandidates f.1 o).Nonempty) ⟨facet, hfacet⟩ order

noncomputable def subdivisionRefinementFacet
    (facet : Finset Vertex) (hfacet : facet ∈ facets) (order : Fin 6) :
    Finset TrisectionVertex :=
  (subdivisionRefinementCandidates_nonempty facet hfacet order).choose

theorem subdivisionRefinementFacet_spec
    (facet : Finset Vertex) (hfacet : facet ∈ facets) (order : Fin 6) :
    subdivisionRefinementFacet facet hfacet order ∈ trisectionSubdivisionFacets ∧
      trisectionSimplexCarrier (subdivisionRefinementFacet facet hfacet order) = facet ∧
      subdivisionRefinementRequired facet order ⊆
        subdivisionRefinementFacet facet hfacet order := by
  have hmem :=
    (subdivisionRefinementCandidates_nonempty facet hfacet order).choose_spec
  change (subdivisionRefinementCandidates_nonempty facet hfacet order).choose ∈
    trisectionSubdivisionFacets.filter (fun refined ↦
      trisectionSimplexCarrier refined = facet ∧
        subdivisionRefinementRequired facet order ⊆ refined) at hmem
  rw [Finset.mem_filter] at hmem
  unfold subdivisionRefinementFacet
  exact hmem

theorem subdivisionRefinementFacet_mem
    (facet : Finset Vertex) (hfacet : facet ∈ facets) (order : Fin 6) :
    subdivisionRefinementFacet facet hfacet order ∈ trisectionSubdivisionFacets :=
  (subdivisionRefinementFacet_spec facet hfacet order).1

theorem trisectionSimplexCarrier_subdivisionRefinementFacet
    (facet : Finset Vertex) (hfacet : facet ∈ facets) (order : Fin 6) :
    trisectionSimplexCarrier (subdivisionRefinementFacet facet hfacet order) = facet :=
  (subdivisionRefinementFacet_spec facet hfacet order).2.1

theorem trisectionSubdivisionInverseCoord_support_order_zero
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h04 : y.1.1 0 ≤ y.1.1 4) (h45 : y.1.1 4 ≤ y.1.1 5) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 0 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hf5 : 5 ∉ facet := by
      intro hf5
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf5]
    have hz5 := hsupport 5 hf5
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hpair : ¬({4, 5} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf4 : 4 ∈ facet
      · right
        intro hf5
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf4 hf5)
      · exact Or.inl hf4
    rcases hmissing with hf4 | hf5
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseCoord_support_order_one
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h05 : y.1.1 0 ≤ y.1.1 5) (h54 : y.1.1 5 ≤ y.1.1 4) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 1 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · have hf4 : 4 ∉ facet := by
      intro hf4
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf4]
    have hz4 := hsupport 4 hf4
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hpair : ¬({4, 5} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf4 : 4 ∈ facet
      · right
        intro hf5
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf4 hf5)
      · exact Or.inl hf4
    rcases hmissing with hf4 | hf5
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseCoord_support_order_two
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h40 : y.1.1 4 ≤ y.1.1 0) (h05 : y.1.1 0 ≤ y.1.1 5) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 2 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hf5 : 5 ∉ facet := by
      intro hf5
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf5]
    have hz5 := hsupport 5 hf5
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · have hpair : ¬({0, 5} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 0 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · right
        intro hf5
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf0 hf5)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseCoord_support_order_three
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h45 : y.1.1 4 ≤ y.1.1 5) (h50 : y.1.1 5 ≤ y.1.1 0) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 3 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · have hf0 : 0 ∉ facet := by
      intro hf0
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf0]
    have hz0 := hsupport 0 hf0
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · have hpair : ¬({0, 5} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 0 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · right
        intro hf5
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf0 hf5)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseCoord_support_order_four
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h50 : y.1.1 5 ≤ y.1.1 0) (h04 : y.1.1 0 ≤ y.1.1 4) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 4 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · have hf4 : 4 ∉ facet := by
      intro hf4
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf4]
    have hz4 := hsupport 4 hf4
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hpair : ¬({0, 4} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · right
        intro hf4
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf0 hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseCoord_support_order_five
    (y : ProjectivePlaneCarrier) (facet : Finset Vertex)
    (hsupport : ∀ v, v ∉ facet → y.1.1 v = 0)
    (h54 : y.1.1 5 ≤ y.1.1 4) (h40 : y.1.1 4 ≤ y.1.1 0) :
    ∀ w, w ∉ subdivisionRefinementRequired facet 5 →
      trisectionSubdivisionInverseCoord y w = 0 := by
  intro w hw
  have hy := y.1.2.1
  have hold (i : Vertex) (hi : i ∉ originalTrisectionVertices)
      (hwi : oldVertexEmbedding i = w) : i ∉ facet := by
    intro hif
    apply hw
    apply Finset.mem_union_left
    exact Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hif, hi⟩, hwi⟩
  fin_cases w
  · have hf0 : 0 ∉ facet := by
      intro hf0
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hf0]
    have hz0 := hsupport 0 hf0
    simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 1 (hold 1 (by decide) rfl)
  · exact hsupport 2 (hold 2 (by decide) rfl)
  · exact hsupport 3 (hold 3 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · exact hsupport 6 (hold 6 (by decide) rfl)
  · exact hsupport 7 (hold 7 (by decide) rfl)
  · exact hsupport 8 (hold 8 (by decide) rfl)
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have hpair : ¬({0, 4} : Finset Vertex) ⊆ facet := by
      intro hpair
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, hpair]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · right
        intro hf4
        exact hpair (by simpa [Finset.subset_iff] using And.intro hf0 hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · simp [trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
      subdivisionInverseResidualFive, subdivisionInverseMin, min_def]
    split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
  · have htri : ¬({0, 4, 5} : Finset Vertex) ⊆ facet := by
      intro htri
      apply hw
      simp [subdivisionRefinementRequired, subdivisionRefinementChain,
        trisectionVertexCarrier, htri]
    have hmissing : 0 ∉ facet ∨ 4 ∉ facet ∨ 5 ∉ facet := by
      by_cases hf0 : 0 ∈ facet
      · by_cases hf4 : 4 ∈ facet
        · exact Or.inr (Or.inr (by
            intro hf5
            exact htri (by
              simpa [Finset.subset_iff] using And.intro hf0 (And.intro hf4 hf5))))
        · exact Or.inr (Or.inl hf4)
      · exact Or.inl hf0
    rcases hmissing with hf0 | hf4 | hf5
    · have hz0 := hsupport 0 hf0
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz4 := hsupport 4 hf4
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]
    · have hz5 := hsupport 5 hf5
      simp [trisectionSubdivisionInverseCoord, subdivisionInverseMin, min_def]
      split_ifs <;> norm_num at * <;> nlinarith [hy 0, hy 4, hy 5]

theorem trisectionSubdivisionInverseSimplex_mem
    (y : ProjectivePlaneCarrier) :
    trisectionSubdivisionInverseSimplex y ∈
      facetFamilyCarrier trisectionSubdivisionFacets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff facets y.1).mp y.2
  have hland (order : Fin 6)
      (hsupportOrder : ∀ w,
        w ∉ subdivisionRefinementRequired facet order →
          trisectionSubdivisionInverseCoord y w = 0) :
      trisectionSubdivisionInverseSimplex y ∈
        facetFamilyCarrier trisectionSubdivisionFacets := by
    rw [mem_facetFamilyCarrier_iff]
    refine ⟨subdivisionRefinementFacet facet hfacet order,
      subdivisionRefinementFacet_mem facet hfacet order, ?_⟩
    intro w hw
    exact hsupportOrder w fun hrequired ↦
      hw ((subdivisionRefinementFacet_spec facet hfacet order).2.2 hrequired)
  by_cases h04 : y.1.1 0 ≤ y.1.1 4
  · by_cases h45 : y.1.1 4 ≤ y.1.1 5
    · exact hland 0
        (trisectionSubdivisionInverseCoord_support_order_zero
          y facet hsupport h04 h45)
    · have h54 : y.1.1 5 ≤ y.1.1 4 := le_of_not_ge h45
      by_cases h05 : y.1.1 0 ≤ y.1.1 5
      · exact hland 1
          (trisectionSubdivisionInverseCoord_support_order_one
            y facet hsupport h05 h54)
      · have h50 : y.1.1 5 ≤ y.1.1 0 := le_of_not_ge h05
        exact hland 4
          (trisectionSubdivisionInverseCoord_support_order_four
            y facet hsupport h50 h04)
  · have h40 : y.1.1 4 ≤ y.1.1 0 := le_of_not_ge h04
    by_cases h05 : y.1.1 0 ≤ y.1.1 5
    · exact hland 2
        (trisectionSubdivisionInverseCoord_support_order_two
          y facet hsupport h40 h05)
    · have h50 : y.1.1 5 ≤ y.1.1 0 := le_of_not_ge h05
      by_cases h45 : y.1.1 4 ≤ y.1.1 5
      · exact hland 3
          (trisectionSubdivisionInverseCoord_support_order_three
            y facet hsupport h45 h50)
      · have h54 : y.1.1 5 ≤ y.1.1 4 := le_of_not_ge h45
        exact hland 5
          (trisectionSubdivisionInverseCoord_support_order_five
            y facet hsupport h54 h40)

def projectivePlaneCarrierToTrisectionSubdivision
    (y : ProjectivePlaneCarrier) : TrisectionSubdivisionCarrier :=
  ⟨trisectionSubdivisionInverseSimplex y,
    trisectionSubdivisionInverseSimplex_mem y⟩

theorem trisectionSubdivisionCarrierToProjectivePlane_inverse
    (y : ProjectivePlaneCarrier) :
    trisectionSubdivisionCarrierToProjectivePlane
        (projectivePlaneCarrierToTrisectionSubdivision y) = y := by
  apply Subtype.ext
  apply stdSimplex.ext
  funext v
  change trisectionSubdivisionForwardCoord
      (projectivePlaneCarrierToTrisectionSubdivision y) v = y.1.1 v
  fin_cases v <;>
    simp [trisectionSubdivisionForwardCoord,
      projectivePlaneCarrierToTrisectionSubdivision,
      trisectionSubdivisionInverseSimplex,
      trisectionSubdivisionInverseCoord,
      subdivisionInverseResidualZero, subdivisionInverseResidualFour,
    subdivisionInverseResidualFive, subdivisionInverseMin, min_def] <;>
    split_ifs <;> norm_num at * <;> nlinarith

def subdivisionRefinementSupport (order : Fin 6) :
    Finset TrisectionVertex :=
  ({1, 2, 3, 6, 7, 8} : Finset TrisectionVertex) ∪
    subdivisionRefinementChain order

theorem trisectionSubdivisionFacet_subset_refinementSupport
    (refined : Finset TrisectionVertex)
    (hrefined : refined ∈ trisectionSubdivisionFacets) :
    ∃ order : Fin 6, refined ⊆ subdivisionRefinementSupport order := by
  exact (by decide : ∀ f : ↥trisectionSubdivisionFacets,
    ∃ order : Fin 6, f.1 ⊆ subdivisionRefinementSupport order)
      ⟨refined, hrefined⟩

theorem projectivePlaneCarrierToTrisectionSubdivision_forward_of_support
    (x : TrisectionSubdivisionCarrier) (order : Fin 6)
    (hsupport : ∀ w, w ∉ subdivisionRefinementSupport order → x.1.1 w = 0) :
    projectivePlaneCarrierToTrisectionSubdivision
        (trisectionSubdivisionCarrierToProjectivePlane x) = x := by
  have hx := x.1.2.1
  fin_cases order
  · have hx0 := hsupport 0 (by decide)
    have hx4 := hsupport 4 (by decide)
    have hx9 := hsupport 9 (by decide)
    have hx10 := hsupport 10 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx0, hx4, hx9, hx10] <;>
      split_ifs <;> norm_num at * <;>
      (try intro hcontra) <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]
  · have hx0 := hsupport 0 (by decide)
    have hx5 := hsupport 5 (by decide)
    have hx9 := hsupport 9 (by decide)
    have hx10 := hsupport 10 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx0, hx5, hx9, hx10] <;>
      split_ifs <;> norm_num at * <;>
      (try intro hcontra) <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]
  · have hx0 := hsupport 0 (by decide)
    have hx4 := hsupport 4 (by decide)
    have hx10 := hsupport 10 (by decide)
    have hx11 := hsupport 11 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx0, hx4, hx10, hx11] <;>
      split_ifs <;> norm_num at * <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]
  · have hx4 := hsupport 4 (by decide)
    have hx5 := hsupport 5 (by decide)
    have hx10 := hsupport 10 (by decide)
    have hx11 := hsupport 11 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx4, hx5, hx10, hx11] <;>
      split_ifs <;> norm_num at * <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]
  · have hx0 := hsupport 0 (by decide)
    have hx5 := hsupport 5 (by decide)
    have hx9 := hsupport 9 (by decide)
    have hx11 := hsupport 11 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx0, hx5, hx9, hx11] <;>
      split_ifs <;> norm_num at * <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]
  · have hx4 := hsupport 4 (by decide)
    have hx5 := hsupport 5 (by decide)
    have hx9 := hsupport 9 (by decide)
    have hx11 := hsupport 11 (by decide)
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change trisectionSubdivisionInverseCoord
        (trisectionSubdivisionCarrierToProjectivePlane x) v = x.1.1 v
    fin_cases v <;>
      simp [trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionForwardSimplex,
        trisectionSubdivisionForwardCoord,
        trisectionSubdivisionInverseCoord,
        subdivisionInverseResidualZero, subdivisionInverseResidualFour,
        subdivisionInverseResidualFive, subdivisionInverseMin, min_def,
        hx4, hx5, hx9, hx11] <;>
      split_ifs <;> norm_num at * <;>
      linarith [hx 0, hx 4, hx 5, hx 9, hx 10, hx 11, hx 12]

theorem projectivePlaneCarrierToTrisectionSubdivision_forward
    (x : TrisectionSubdivisionCarrier) :
    projectivePlaneCarrierToTrisectionSubdivision
        (trisectionSubdivisionCarrierToProjectivePlane x) = x := by
  obtain ⟨refined, hrefined, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff trisectionSubdivisionFacets x.1).mp x.2
  obtain ⟨order, horder⟩ :=
    trisectionSubdivisionFacet_subset_refinementSupport refined hrefined
  apply projectivePlaneCarrierToTrisectionSubdivision_forward_of_support x order
  intro w hw
  exact hsupport w fun hwrefined ↦ hw (horder hwrefined)

theorem continuous_trisectionSubdivisionForwardCoord (v : Vertex) :
    Continuous (fun x : TrisectionSubdivisionCarrier ↦
      trisectionSubdivisionForwardCoord x v) := by
  have hcoord (w : TrisectionVertex) :
      Continuous (fun x : TrisectionSubdivisionCarrier ↦ x.1.1 w) :=
    (continuous_apply w).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  fin_cases v <;> simp [trisectionSubdivisionForwardCoord] <;> fun_prop

theorem continuous_trisectionSubdivisionCarrierToProjectivePlane :
    Continuous trisectionSubdivisionCarrierToProjectivePlane := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  exact continuous_trisectionSubdivisionForwardCoord

theorem trisectionSubdivisionCarrierToProjectivePlane_injective :
    Function.Injective trisectionSubdivisionCarrierToProjectivePlane :=
  (show Function.LeftInverse projectivePlaneCarrierToTrisectionSubdivision
      trisectionSubdivisionCarrierToProjectivePlane from
    projectivePlaneCarrierToTrisectionSubdivision_forward).injective

theorem trisectionSubdivisionCarrierToProjectivePlane_surjective :
    Function.Surjective trisectionSubdivisionCarrierToProjectivePlane :=
  (show Function.RightInverse projectivePlaneCarrierToTrisectionSubdivision
      trisectionSubdivisionCarrierToProjectivePlane from
    trisectionSubdivisionCarrierToProjectivePlane_inverse).surjective

noncomputable def trisectionSubdivisionCarrierHomeomorphProjectivePlane :
    TrisectionSubdivisionCarrier ≃ₜ ProjectivePlaneCarrier := by
  letI : T2Space ProjectivePlaneCarrier := by infer_instance
  exact IsHomeomorph.homeomorph trisectionSubdivisionCarrierToProjectivePlane <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_trisectionSubdivisionCarrierToProjectivePlane,
        trisectionSubdivisionCarrierToProjectivePlane_injective,
        trisectionSubdivisionCarrierToProjectivePlane_surjective⟩

/-- The 78-facet trisection subdivision realizes the same space as the original nine-vertex
projective-plane triangulation. -/
noncomputable def trisectionSubdivisionRealizationHomeomorphProjectivePlane :
    SSet.toTop.obj (orderedSSet trisectionSubdivisionFacets) ≃ₜ
      SSet.toTop.obj (orderedSSet facets) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      trisectionSubdivisionFacets).trans
    (trisectionSubdivisionCarrierHomeomorphProjectivePlane.trans
      (orderedRealizationHomeomorphFacetFamilyCarrier facets).symm)

end Submission.ComplexProjectivePlaneTriangulation

