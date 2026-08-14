/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionFilling

/-!
# The prism component of a projective-plane trisection interface

The three tetrahedra in the first zero-five interface component form the join of a subdivided
interval with an edge. Explicit piecewise-affine barycentric coordinates identify its carrier
with one tetrahedron; compactness upgrades the continuous bijection to a homeomorphism, and the
finite realization/carrier comparison then identifies its realization with the three-disk.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

abbrev BallOneCarrier :=
  facetFamilyCarrier zeroFiveInterfaceBallOneFacets

def zeroFiveInterfaceBallOneTargetFacets :
    Finset (Finset TrisectionVertex) :=
  {{3, 6, 7, 8}}

abbrev BallOneTargetCarrier :=
  facetFamilyCarrier zeroFiveInterfaceBallOneTargetFacets

def ballOneForwardCoord (x : BallOneCarrier) (v : TrisectionVertex) : ℝ :=
  if v = 7 then x.1.1 7 + (2 / 3 : ℝ) * x.1.1 1 + (1 / 3 : ℝ) * x.1.1 2
  else if v = 6 then x.1.1 6 + (1 / 3 : ℝ) * x.1.1 1 + (2 / 3 : ℝ) * x.1.1 2
  else if v = 3 then x.1.1 3
  else if v = 8 then x.1.1 8
  else 0

theorem ballOneForwardCoord_nonneg (x : BallOneCarrier) (v : TrisectionVertex) :
    0 ≤ ballOneForwardCoord x v := by
  have hx := x.1.2.1
  simp only [ballOneForwardCoord]
  split_ifs
  · exact add_nonneg
      (add_nonneg (hx 7) (mul_nonneg (by norm_num) (hx 1)))
      (mul_nonneg (by norm_num) (hx 2))
  · exact add_nonneg
      (add_nonneg (hx 6) (mul_nonneg (by norm_num) (hx 1)))
      (mul_nonneg (by norm_num) (hx 2))
  · exact hx 3
  · exact hx 8
  · exact le_rfl

theorem ballOneForwardCoord_sum (x : BallOneCarrier) :
    ∑ v, ballOneForwardCoord x v = 1 := by
  have hzero (v : TrisectionVertex) (hv : v ∉ ({1, 2, 3, 6, 7, 8} : Finset TrisectionVertex)) :
      x.1 v = 0 := by
    obtain ⟨facet, hfacet, hsupport⟩ :=
      (mem_facetFamilyCarrier_iff zeroFiveInterfaceBallOneFacets x.1).mp x.2
    apply hsupport v
    simp [zeroFiveInterfaceBallOneFacets] at hfacet
    rcases hfacet with hfacet | hfacet | hfacet <;> subst facet
    · intro hvfacet
      apply hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvfacet ⊢
      aesop
    · intro hvfacet
      apply hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvfacet ⊢
      aesop
    · intro hvfacet
      apply hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvfacet ⊢
      aesop
  have hx := x.1.2.2
  have hx0 := hzero 0 (by decide)
  have hx4 := hzero 4 (by decide)
  have hx5 := hzero 5 (by decide)
  have hx9 := hzero 9 (by decide)
  have hx10 := hzero 10 (by decide)
  have hx11 := hzero 11 (by decide)
  have hx12 := hzero 12 (by decide)
  change x.1.1 0 = 0 at hx0
  change x.1.1 4 = 0 at hx4
  change x.1.1 5 = 0 at hx5
  change x.1.1 9 = 0 at hx9
  change x.1.1 10 = 0 at hx10
  change x.1.1 11 = 0 at hx11
  change x.1.1 12 = 0 at hx12
  simp [Fin.sum_univ_succ] at hx
  rw [hx0, hx4, hx5, hx9, hx10, hx11, hx12] at hx
  simp only [zero_add, add_zero] at hx
  simp [ballOneForwardCoord, Fin.sum_univ_succ]
  norm_num at ⊢
  linarith

def ballOneForwardSimplex (x : BallOneCarrier) :
    stdSimplex ℝ TrisectionVertex :=
  ⟨ballOneForwardCoord x,
    ballOneForwardCoord_nonneg x,
    ballOneForwardCoord_sum x⟩

theorem ballOneForwardSimplex_mem (x : BallOneCarrier) :
    ballOneForwardSimplex x ∈
      facetFamilyCarrier zeroFiveInterfaceBallOneTargetFacets := by
  rw [mem_facetFamilyCarrier_iff]
  refine ⟨{3, 6, 7, 8}, by simp [zeroFiveInterfaceBallOneTargetFacets], ?_⟩
  intro v hv
  change ballOneForwardCoord x v = 0
  simp only [ballOneForwardCoord]
  split_ifs with h7 h6 h3 h8
  · exact False.elim (hv (h7 ▸ by simp))
  · exact False.elim (hv (h6 ▸ by simp))
  · exact False.elim (hv (h3 ▸ by simp))
  · exact False.elim (hv (h8 ▸ by simp))
  · rfl

def ballOneCarrierToTarget (x : BallOneCarrier) : BallOneTargetCarrier :=
  ⟨ballOneForwardSimplex x, ballOneForwardSimplex_mem x⟩

def ballOneInverseCoord (y : BallOneTargetCarrier) (v : TrisectionVertex) : ℝ :=
  let s := y.1.1 7 + y.1.1 6
  let q := y.1.1 6
  if q ≤ s / 3 then
    if v = 7 then s - 3 * q
    else if v = 1 then 3 * q
    else if v = 3 then y.1.1 3
    else if v = 8 then y.1.1 8
    else 0
  else if q ≤ 2 * s / 3 then
    if v = 1 then 2 * s - 3 * q
    else if v = 2 then 3 * q - s
    else if v = 3 then y.1.1 3
    else if v = 8 then y.1.1 8
    else 0
  else
    if v = 2 then 3 * s - 3 * q
    else if v = 6 then 3 * q - 2 * s
    else if v = 3 then y.1.1 3
    else if v = 8 then y.1.1 8
    else 0

theorem ballOneInverseCoord_nonneg (y : BallOneTargetCarrier)
    (v : TrisectionVertex) : 0 ≤ ballOneInverseCoord y v := by
  have hy := y.1.2.1
  simp only [ballOneInverseCoord]
  split_ifs <;> norm_num at * <;>
    nlinarith [hy 1, hy 2, hy 3, hy 6, hy 7, hy 8]

theorem ballOneTargetCoord_eq_zero (y : BallOneTargetCarrier)
    (v : TrisectionVertex)
    (hv : v ∉ ({3, 6, 7, 8} : Finset TrisectionVertex)) :
    y.1.1 v = 0 := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff zeroFiveInterfaceBallOneTargetFacets y.1).mp y.2
  have hfacetEq : facet = {3, 6, 7, 8} := by
    simpa [zeroFiveInterfaceBallOneTargetFacets] using hfacet
  subst facet
  exact hsupport v hv

theorem ballOneInverseCoord_sum (y : BallOneTargetCarrier) :
    ∑ v, ballOneInverseCoord y v = 1 := by
  have hy0 := ballOneTargetCoord_eq_zero y 0 (by decide)
  have hy1 := ballOneTargetCoord_eq_zero y 1 (by decide)
  have hy2 := ballOneTargetCoord_eq_zero y 2 (by decide)
  have hy4 := ballOneTargetCoord_eq_zero y 4 (by decide)
  have hy5 := ballOneTargetCoord_eq_zero y 5 (by decide)
  have hy9 := ballOneTargetCoord_eq_zero y 9 (by decide)
  have hy10 := ballOneTargetCoord_eq_zero y 10 (by decide)
  have hy11 := ballOneTargetCoord_eq_zero y 11 (by decide)
  have hy12 := ballOneTargetCoord_eq_zero y 12 (by decide)
  have hsum := y.1.2.2
  simp [Fin.sum_univ_succ] at hsum
  rw [hy0, hy1, hy2, hy4, hy5, hy9, hy10, hy11, hy12] at hsum
  simp only [zero_add, add_zero] at hsum
  simp [ballOneInverseCoord, Fin.sum_univ_succ]
  split_ifs <;> norm_num at * <;> linarith

def ballOneInverseSimplex (y : BallOneTargetCarrier) :
    stdSimplex ℝ TrisectionVertex :=
  ⟨ballOneInverseCoord y, ballOneInverseCoord_nonneg y,
    ballOneInverseCoord_sum y⟩

theorem ballOneInverseSimplex_mem (y : BallOneTargetCarrier) :
    ballOneInverseSimplex y ∈
      facetFamilyCarrier zeroFiveInterfaceBallOneFacets := by
  rw [mem_facetFamilyCarrier_iff]
  by_cases hfirst : y.1.1 6 ≤ (y.1.1 7 + y.1.1 6) / 3
  · refine ⟨{1, 3, 7, 8}, by simp [zeroFiveInterfaceBallOneFacets], ?_⟩
    intro v hv
    change ballOneInverseCoord y v = 0
    simp only [ballOneInverseCoord, if_pos hfirst]
    split_ifs with h7 h1 h3 h8
    · exact False.elim (hv (h7 ▸ by simp))
    · exact False.elim (hv (h1 ▸ by simp))
    · exact False.elim (hv (h3 ▸ by simp))
    · exact False.elim (hv (h8 ▸ by simp))
    · rfl
  · by_cases hsecond : y.1.1 6 ≤
        2 * (y.1.1 7 + y.1.1 6) / 3
    · refine ⟨{1, 2, 3, 8}, by simp [zeroFiveInterfaceBallOneFacets], ?_⟩
      intro v hv
      change ballOneInverseCoord y v = 0
      simp only [ballOneInverseCoord, if_neg hfirst, if_pos hsecond]
      split_ifs with h1 h2 h3 h8
      · exact False.elim (hv (h1 ▸ by simp))
      · exact False.elim (hv (h2 ▸ by simp))
      · exact False.elim (hv (h3 ▸ by simp))
      · exact False.elim (hv (h8 ▸ by simp))
      · rfl
    · refine ⟨{2, 3, 6, 8}, by simp [zeroFiveInterfaceBallOneFacets], ?_⟩
      intro v hv
      change ballOneInverseCoord y v = 0
      simp only [ballOneInverseCoord, if_neg hfirst, if_neg hsecond]
      split_ifs with h2 h6 h3 h8
      · exact False.elim (hv (h2 ▸ by simp))
      · exact False.elim (hv (h6 ▸ by simp))
      · exact False.elim (hv (h3 ▸ by simp))
      · exact False.elim (hv (h8 ▸ by simp))
      · rfl

def ballOneTargetToCarrier (y : BallOneTargetCarrier) : BallOneCarrier :=
  ⟨ballOneInverseSimplex y, ballOneInverseSimplex_mem y⟩

theorem ballOneCarrierToTarget_targetToCarrier (y : BallOneTargetCarrier) :
    ballOneCarrierToTarget (ballOneTargetToCarrier y) = y := by
  have hy := y.1.2.1
  have hy0 := ballOneTargetCoord_eq_zero y 0 (by decide)
  have hy1 := ballOneTargetCoord_eq_zero y 1 (by decide)
  have hy2 := ballOneTargetCoord_eq_zero y 2 (by decide)
  have hy4 := ballOneTargetCoord_eq_zero y 4 (by decide)
  have hy5 := ballOneTargetCoord_eq_zero y 5 (by decide)
  have hy9 := ballOneTargetCoord_eq_zero y 9 (by decide)
  have hy10 := ballOneTargetCoord_eq_zero y 10 (by decide)
  have hy11 := ballOneTargetCoord_eq_zero y 11 (by decide)
  have hy12 := ballOneTargetCoord_eq_zero y 12 (by decide)
  apply Subtype.ext
  apply stdSimplex.ext
  funext v
  change ballOneForwardCoord (ballOneTargetToCarrier y) v = y.1.1 v
  fin_cases v <;>
    simp [ballOneForwardCoord, ballOneTargetToCarrier, ballOneInverseSimplex,
      ballOneInverseCoord,
      hy0, hy1, hy2, hy4, hy5, hy9, hy10, hy11, hy12] <;>
    split_ifs <;> norm_num at * <;>
    nlinarith [hy 3, hy 6, hy 7, hy 8]

theorem ballOneTargetToCarrier_carrierToTarget (x : BallOneCarrier) :
    ballOneTargetToCarrier (ballOneCarrierToTarget x) = x := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff zeroFiveInterfaceBallOneFacets x.1).mp x.2
  have hsupport' (v : TrisectionVertex) (hv : v ∉ facet) :
      x.1.1 v = 0 := by
    have h := hsupport v hv
    change x.1.1 v = 0 at h
    exact h
  simp [zeroFiveInterfaceBallOneFacets] at hfacet
  rcases hfacet with hfacet | hfacet | hfacet
  · subst facet
    have hx := x.1.2.1
    have hx2 := hsupport' 2 (by decide)
    have hx6 := hsupport' 6 (by decide)
    have hfirst : ballOneForwardCoord x 6 ≤
        (ballOneForwardCoord x 7 + ballOneForwardCoord x 6) / 3 := by
      simp [ballOneForwardCoord, hx2, hx6]
      norm_num at ⊢
      nlinarith [hx 7]
    apply Subtype.ext
    apply stdSimplex.ext
    funext v
    change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
    fin_cases v <;>
      simp only [ballOneInverseCoord, ballOneCarrierToTarget,
        ballOneForwardSimplex, if_pos hfirst] <;>
      simp [ballOneForwardCoord, hx2, hx6] <;>
      first
      | exact (hsupport' _ (by decide)).symm
      | norm_num at *; nlinarith [hx 1, hx 3, hx 7, hx 8]
  · subst facet
    have hx := x.1.2.1
    have hx6 := hsupport' 6 (by decide)
    have hx7 := hsupport' 7 (by decide)
    have hsecond : ballOneForwardCoord x 6 ≤
        2 * (ballOneForwardCoord x 7 + ballOneForwardCoord x 6) / 3 := by
      simp [ballOneForwardCoord, hx6, hx7]
      norm_num at ⊢
      nlinarith [hx 1]
    by_cases hfirst : ballOneForwardCoord x 6 ≤
        (ballOneForwardCoord x 7 + ballOneForwardCoord x 6) / 3
    · have hx2 : x.1.1 2 = 0 := by
        simp [ballOneForwardCoord, hx6, hx7] at hfirst
        norm_num at hfirst
        nlinarith [hx 2]
      apply Subtype.ext
      apply stdSimplex.ext
      funext v
      change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
      fin_cases v <;>
        simp only [ballOneInverseCoord, ballOneCarrierToTarget,
          ballOneForwardSimplex, if_pos hfirst] <;>
        simp [ballOneForwardCoord, hx2, hx6, hx7] <;>
        first
        | exact (hsupport' _ (by decide)).symm
        | norm_num at *; nlinarith [hx 1, hx 3, hx 8]
    · apply Subtype.ext
      apply stdSimplex.ext
      funext v
      change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
      fin_cases v <;>
        simp only [ballOneInverseCoord, ballOneCarrierToTarget,
          ballOneForwardSimplex, if_neg hfirst, if_pos hsecond] <;>
        simp [ballOneForwardCoord, hx6, hx7] <;>
        first
        | exact (hsupport' _ (by decide)).symm
        | norm_num at *; nlinarith [hx 1, hx 2, hx 3, hx 8]
  · subst facet
    have hx := x.1.2.1
    have hx1 := hsupport' 1 (by decide)
    have hx7 := hsupport' 7 (by decide)
    by_cases hfirst : ballOneForwardCoord x 6 ≤
        (ballOneForwardCoord x 7 + ballOneForwardCoord x 6) / 3
    · have hx2 : x.1.1 2 = 0 := by
        simp [ballOneForwardCoord, hx1, hx7] at hfirst
        norm_num at hfirst
        nlinarith [hx 2, hx 6]
      have hx6 : x.1.1 6 = 0 := by
        simp [ballOneForwardCoord, hx1, hx7] at hfirst
        norm_num at hfirst
        nlinarith [hx 2, hx 6]
      apply Subtype.ext
      apply stdSimplex.ext
      funext v
      change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
      fin_cases v <;>
        simp only [ballOneInverseCoord, ballOneCarrierToTarget,
          ballOneForwardSimplex, if_pos hfirst] <;>
        simp [ballOneForwardCoord, hx1, hx2, hx6, hx7] <;>
        exact (hsupport' _ (by decide)).symm
    · by_cases hsecond : ballOneForwardCoord x 6 ≤
          2 * (ballOneForwardCoord x 7 + ballOneForwardCoord x 6) / 3
      · have hx6 : x.1.1 6 = 0 := by
          simp [ballOneForwardCoord, hx1, hx7] at hsecond
          norm_num at hsecond
          nlinarith [hx 6]
        apply Subtype.ext
        apply stdSimplex.ext
        funext v
        change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
        fin_cases v <;>
          simp only [ballOneInverseCoord, ballOneCarrierToTarget,
            ballOneForwardSimplex, if_neg hfirst, if_pos hsecond] <;>
          simp [ballOneForwardCoord, hx1, hx6, hx7] <;>
          first
          | exact (hsupport' _ (by decide)).symm
          | norm_num at *; nlinarith [hx 2, hx 3, hx 8]
      · apply Subtype.ext
        apply stdSimplex.ext
        funext v
        change ballOneInverseCoord (ballOneCarrierToTarget x) v = x.1.1 v
        fin_cases v <;>
          simp only [ballOneInverseCoord, ballOneCarrierToTarget,
            ballOneForwardSimplex, if_neg hfirst, if_neg hsecond] <;>
          simp [ballOneForwardCoord, hx1, hx7] <;>
          first
          | exact (hsupport' _ (by decide)).symm
          | norm_num at *; nlinarith [hx 2, hx 3, hx 6, hx 8]

theorem continuous_ballOneForwardCoord (v : TrisectionVertex) :
    Continuous (fun x : BallOneCarrier ↦ ballOneForwardCoord x v) := by
  have hcoord (i : TrisectionVertex) :
      Continuous (fun x : BallOneCarrier ↦ x.1.1 i) :=
    (continuous_apply i).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  simp only [ballOneForwardCoord]
  split_ifs
  · exact ((hcoord 7).add (continuous_const.mul (hcoord 1))).add
      (continuous_const.mul (hcoord 2))
  · exact ((hcoord 6).add (continuous_const.mul (hcoord 1))).add
      (continuous_const.mul (hcoord 2))
  · exact hcoord 3
  · exact hcoord 8
  · exact continuous_const

theorem continuous_ballOneCarrierToTarget :
    Continuous ballOneCarrierToTarget := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  exact continuous_ballOneForwardCoord

theorem ballOneCarrierToTarget_injective :
    Function.Injective ballOneCarrierToTarget :=
  (show Function.LeftInverse ballOneTargetToCarrier ballOneCarrierToTarget from
    ballOneTargetToCarrier_carrierToTarget).injective

theorem ballOneCarrierToTarget_surjective :
    Function.Surjective ballOneCarrierToTarget :=
  (show Function.RightInverse ballOneTargetToCarrier ballOneCarrierToTarget from
    ballOneCarrierToTarget_targetToCarrier).surjective

noncomputable def zeroFiveInterfaceBallOneCarrierHomeomorphTarget :
    BallOneCarrier ≃ₜ BallOneTargetCarrier := by
  letI : T2Space BallOneTargetCarrier := by infer_instance
  exact IsHomeomorph.homeomorph ballOneCarrierToTarget <|
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_ballOneCarrierToTarget,
        ballOneCarrierToTarget_injective,
        ballOneCarrierToTarget_surjective⟩

noncomputable def zeroFiveInterfaceBallOneTargetRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallOneTargetFacets) ≃ₜ
      TopCat.disk.{0} 3 := by
  let q : orderedSSet zeroFiveInterfaceBallOneTargetFacets ≅
      orderedSSet ({{3, 6, 7, 8}} : Finset (Finset TrisectionVertex)) :=
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex (by
      rfl))
  exact (TopCat.homeoOfIso (SSet.toTop.mapIso q)).trans
    (simplexRealizationHomeomorphDisk 3
      ({3, 6, 7, 8} : Finset TrisectionVertex) (by decide))

noncomputable def zeroFiveInterfaceBallOneRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallOneFacets) ≃ₜ
      TopCat.disk.{0} 3 :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      zeroFiveInterfaceBallOneFacets).trans
    (zeroFiveInterfaceBallOneCarrierHomeomorphTarget.trans
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        zeroFiveInterfaceBallOneTargetFacets).symm.trans
          zeroFiveInterfaceBallOneTargetRealizationHomeomorphDisk))


end Submission.ComplexProjectivePlaneTriangulation

