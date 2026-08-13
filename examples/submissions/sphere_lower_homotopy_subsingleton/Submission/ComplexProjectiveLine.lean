/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexHopfFibration
import Submission.HopfLocalTrivialization

/-!
# The complex projective line and the exact Hopf map

This file identifies the quotient-topology complex projective line with the exact metric
two-sphere. Under this homeomorphism and the realification homeomorphism on the total space, the
projective quotient map is exactly the concrete quadratic Hopf map.

This is the first geometric comparison needed to identify the mapping cone of the Hopf map with
the two-cell model of complex projective two-space.
-/

open Topology
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

private abbrev NonzeroComplexVector (n : ℕ) :=
  {v : ComplexEuclidean n // v ≠ 0}

/-- Radially normalize a nonzero complex vector to the complex unit sphere. -/
private def complexNormalizeToUnitSphere (n : ℕ) :
    C(NonzeroComplexVector n, ComplexUnitSphere n) where
  toFun v := ⟨NormedSpace.normalize v.1, by
    rw [Metric.mem_sphere, dist_zero_right, NormedSpace.norm_normalize]
    exact v.2⟩
  continuous_toFun := by
    have hv : Continuous fun v : NonzeroComplexVector n ↦ (v.1 : ComplexEuclidean n) :=
      continuous_subtype_val
    refine Continuous.subtype_mk ?_ _
    exact (hv.norm.inv₀ fun v h ↦ v.2 (norm_eq_zero.mp h)).smul hv

private theorem complexHopfMap_complexNormalizeToUnitSphere (n : ℕ)
    (v : NonzeroComplexVector n) :
    complexHopfMap n (complexNormalizeToUnitSphere n v) =
      Projectivization.mk ℂ v.1 v.2 := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(‖(v.1 : ComplexEuclidean n)‖⁻¹ : ℂ), ?_⟩
  ext i
  simp [complexNormalizeToUnitSphere, NormedSpace.normalize, Complex.real_smul]

/-- The quotient from the complex unit sphere to complex projective space is a topological
quotient map. -/
theorem complexHopfMap_isQuotientMap (n : ℕ) :
    IsQuotientMap (complexHopfMap n) := by
  let q : NonzeroComplexVector n → ComplexProjectiveModel n := Projectivization.mk' ℂ
  have hq : IsQuotientMap q := by
    change IsQuotientMap
      (@Quotient.mk' (NonzeroComplexVector n)
        (projectivizationSetoid ℂ (ComplexEuclidean n)))
    exact isQuotientMap_quotient_mk'
  have hcomp : (complexHopfMap n : ComplexUnitSphere n → ComplexProjectiveModel n) ∘
      complexNormalizeToUnitSphere n = q := by
    funext v
    simpa [q] using complexHopfMap_complexNormalizeToUnitSphere n v
  exact IsQuotientMap.of_comp (complexNormalizeToUnitSphere n).continuous
    (complexHopfMap n).continuous (hcomp ▸ hq)

/-- Simultaneous multiplication of all complex coordinates by a unit scalar. -/
noncomputable def complexUnitSphereCircleAction (n : ℕ)
    (t : Circle) (x : ComplexUnitSphere n) : ComplexUnitSphere n :=
  ⟨(t : ℂ) • (x : ComplexEuclidean n), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Circle.norm_coe,
      norm_coe_complexUnitSphere, one_mul]⟩

/-- In complex dimension two, realification intertwines complex scalar multiplication with the
explicit real-coordinate circle action. -/
theorem complexUnitSphereHomeomorphSphere_one_circleAction
    (t : Circle) (x : ComplexUnitSphere 1) :
    complexUnitSphereHomeomorphSphere 1
        (complexUnitSphereCircleAction 1 t x) =
      hopfCircleAction (circleHomeomorphSphOne t)
        (complexUnitSphereHomeomorphSphere 1 x) := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · change (((t : ℂ) * (x : ComplexEuclidean 1) 0).re) =
      (t : ℂ).re * ((x : ComplexEuclidean 1) 0).re -
        (t : ℂ).im * ((x : ComplexEuclidean 1) 0).im
    exact Complex.mul_re _ _
  · change (((t : ℂ) * (x : ComplexEuclidean 1) 0).im) =
      (t : ℂ).im * ((x : ComplexEuclidean 1) 0).re +
        (t : ℂ).re * ((x : ComplexEuclidean 1) 0).im
    rw [Complex.mul_im, add_comm]
  · change (((t : ℂ) * (x : ComplexEuclidean 1) 1).re) =
      (t : ℂ).re * ((x : ComplexEuclidean 1) 1).re -
        (t : ℂ).im * ((x : ComplexEuclidean 1) 1).im
    exact Complex.mul_re _ _
  · change (((t : ℂ) * (x : ComplexEuclidean 1) 1).im) =
      (t : ℂ).im * ((x : ComplexEuclidean 1) 1).re +
        (t : ℂ).re * ((x : ComplexEuclidean 1) 1).im
    rw [Complex.mul_im, add_comm]

/-- Multiplication by a unit scalar does not change the associated projective point. -/
@[simp]
theorem complexHopfMap_circleAction (n : ℕ)
    (t : Circle) (x : ComplexUnitSphere n) :
    complexHopfMap n (complexUnitSphereCircleAction n t x) =
      complexHopfMap n x := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨(t : ℂ), rfl⟩

/-- The concrete Hopf map expressed on the complex unit three-sphere. -/
noncomputable def complexProjectiveLineSphereCover :
    C(ComplexUnitSphere 1, Sph 2) :=
  hopfMap.comp (complexUnitSphereHomeomorphSphere 1)

/-- The complex projective quotient and the concrete quadratic Hopf map have exactly the same
fibres under realification. -/
theorem complexHopfMap_one_fiber_iff_sphereCover_fiber
    (x y : ComplexUnitSphere 1) :
    complexHopfMap 1 x = complexHopfMap 1 y ↔
      complexProjectiveLineSphereCover x =
        complexProjectiveLineSphereCover y := by
  constructor
  · intro hxy
    change Projectivization.mk ℂ (x : ComplexEuclidean 1) (complexUnitSphere_ne_zero x) =
      Projectivization.mk ℂ (y : ComplexEuclidean 1) (complexUnitSphere_ne_zero y) at hxy
    rw [Projectivization.mk_eq_mk_iff'] at hxy
    obtain ⟨c, hc⟩ := hxy
    have hcNorm : ‖c‖ = 1 := by
      have h := congrArg norm hc
      rw [norm_smul, norm_coe_complexUnitSphere,
        norm_coe_complexUnitSphere, mul_one] at h
      exact h
    let t : Circle := ⟨c, mem_sphere_zero_iff_norm.mpr hcNorm⟩
    have haction : x = complexUnitSphereCircleAction 1 t y := by
      apply Subtype.ext
      exact hc.symm
    change hopfMap (complexUnitSphereHomeomorphSphere 1 x) =
      hopfMap (complexUnitSphereHomeomorphSphere 1 y)
    rw [haction, complexUnitSphereHomeomorphSphere_one_circleAction,
      hopfMap_hopfCircleAction]
  · intro hxy
    change hopfMap (complexUnitSphereHomeomorphSphere 1 x) =
      hopfMap (complexUnitSphereHomeomorphSphere 1 y) at hxy
    obtain ⟨s, hs⟩ :=
      (hopfMap_eq_iff_exists_hopfCircleAction _ _).mp hxy
    let t : Circle := circleHomeomorphSphOne.symm s
    have haction : x = complexUnitSphereCircleAction 1 t y := by
      apply (complexUnitSphereHomeomorphSphere 1).injective
      rw [complexUnitSphereHomeomorphSphere_one_circleAction]
      simpa [t] using hs
    rw [haction, complexHopfMap_circleAction]

/-- The concrete quadratic Hopf map is surjective. -/
theorem hopfMap_surjective : Function.Surjective hopfMap := by
  intro y
  have hcover : y ∈ hopfNorthChart ∨ y ∈ hopfSouthChart := by
    have h := Set.ext_iff.mp hopfNorthChart_union_hopfSouthChart y
    simpa only [Set.mem_union, Set.mem_univ, iff_true] using h
  rcases hcover with hnorth | hsouth
  · exact ⟨hopfNorthSection ⟨y, hnorth⟩, hopfMap_hopfNorthSection ⟨y, hnorth⟩⟩
  · let p : HopfSouthBase × Sph 1 := (⟨y, hsouth⟩, sphereBasepoint 1)
    let z : HopfSouthTotal := hopfSouthTrivialization.symm p
    refine ⟨z, ?_⟩
    have hfst := hopfSouthTrivialization_fst z
    rw [show hopfSouthTrivialization z = p by exact
      hopfSouthTrivialization.apply_symm_apply p] at hfst
    exact hfst.symm

/-- The complex-coordinate form of the Hopf map is surjective. -/
theorem complexProjectiveLineSphereCover_surjective :
    Function.Surjective complexProjectiveLineSphereCover :=
  hopfMap_surjective.comp (complexUnitSphereHomeomorphSphere 1).surjective

/-- The map from the complex projective line to the metric two-sphere obtained by descending the
quadratic Hopf map through the projective quotient. -/
noncomputable def complexProjectiveLineToSphere :
    C(ComplexProjectiveModel 1, Sph 2) :=
  (complexHopfMap_isQuotientMap 1).lift
    complexProjectiveLineSphereCover
    (fun x y h ↦
      (complexHopfMap_one_fiber_iff_sphereCover_fiber x y).mp h)

/-- The descended map commutes exactly with the two quotient maps. -/
@[simp]
theorem complexProjectiveLineToSphere_comp_complexHopfMap :
    complexProjectiveLineToSphere.comp (complexHopfMap 1) =
      complexProjectiveLineSphereCover :=
  (complexHopfMap_isQuotientMap 1).lift_comp _ _

/-- The descended map from the projective line to the metric sphere is bijective. -/
theorem complexProjectiveLineToSphere_bijective :
    Function.Bijective complexProjectiveLineToSphere := by
  constructor
  · intro p q hpq
    obtain ⟨x, rfl⟩ := (complexHopfMap_isQuotientMap 1).surjective p
    obtain ⟨y, rfl⟩ := (complexHopfMap_isQuotientMap 1).surjective q
    apply (complexHopfMap_one_fiber_iff_sphereCover_fiber x y).mpr
    have hx := ContinuousMap.congr_fun
      complexProjectiveLineToSphere_comp_complexHopfMap x
    have hy := ContinuousMap.congr_fun
      complexProjectiveLineToSphere_comp_complexHopfMap y
    exact hx.symm.trans (hpq.trans hy)
  · intro y
    obtain ⟨x, rfl⟩ := complexProjectiveLineSphereCover_surjective y
    exact ⟨complexHopfMap 1 x,
      ContinuousMap.congr_fun
        complexProjectiveLineToSphere_comp_complexHopfMap x⟩

/-- The complex projective line is homeomorphic to the exact metric two-sphere. -/
noncomputable def complexProjectiveLineHomeomorphSphere :
    ComplexProjectiveModel 1 ≃ₜ Sph 2 := by
  let hcover : IsQuotientMap complexProjectiveLineSphereCover :=
    IsQuotientMap.of_surjective_continuous
      complexProjectiveLineSphereCover_surjective
      complexProjectiveLineSphereCover.continuous
  let hline : IsQuotientMap complexProjectiveLineToSphere := by
    apply IsQuotientMap.of_comp (complexHopfMap_isQuotientMap 1).continuous
      complexProjectiveLineToSphere.continuous
    have heq : ⇑complexProjectiveLineToSphere ∘ ⇑(complexHopfMap 1) =
        ⇑complexProjectiveLineSphereCover := by
      funext x
      exact ContinuousMap.congr_fun
        complexProjectiveLineToSphere_comp_complexHopfMap x
    rw [heq]
    exact hcover
  let e := Equiv.ofBijective complexProjectiveLineToSphere
    complexProjectiveLineToSphere_bijective
  exact
    { e with
      continuous_toFun := complexProjectiveLineToSphere.continuous
      continuous_invFun := hline.continuous_iff.mpr <| by
        change Continuous (⇑e.symm ∘ ⇑complexProjectiveLineToSphere)
        have heq : ⇑e.symm ∘ ⇑complexProjectiveLineToSphere = id := by
          funext x
          exact e.symm_apply_apply x
        rw [heq]
        exact continuous_id }

/-- Under the projective-line homeomorphism, the complex projective quotient is exactly the
concrete quadratic Hopf map in real sphere coordinates. -/
@[simp]
theorem complexProjectiveLineHomeomorphSphere_complexHopfMap
    (x : ComplexUnitSphere 1) :
    complexProjectiveLineHomeomorphSphere (complexHopfMap 1 x) =
      hopfMap (complexUnitSphereHomeomorphSphere 1 x) := by
  exact ContinuousMap.congr_fun
    complexProjectiveLineToSphere_comp_complexHopfMap x

/-- Realification sends the standard complex unit-sphere point to the standard point of the
metric three-sphere. -/
@[simp]
theorem complexUnitSphereHomeomorphSphere_one_basepoint :
    complexUnitSphereHomeomorphSphere 1 (complexUnitSphereBasepoint 1) =
      sphereBasepoint 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · change ((EuclideanSpace.single 0 1 : ComplexEuclidean 1) 0).re =
      (sphereBasepoint 3 : EuclideanSpace ℝ (Fin 4)) 0
    simp [sphereBasepoint]
  · change ((EuclideanSpace.single 0 1 : ComplexEuclidean 1) 0).im =
      (sphereBasepoint 3 : EuclideanSpace ℝ (Fin 4)) 1
    simp [sphereBasepoint]
  · change ((EuclideanSpace.single 0 1 : ComplexEuclidean 1) 1).re =
      (sphereBasepoint 3 : EuclideanSpace ℝ (Fin 4)) 2
    simp [sphereBasepoint]
  · change ((EuclideanSpace.single 0 1 : ComplexEuclidean 1) 1).im =
      (sphereBasepoint 3 : EuclideanSpace ℝ (Fin 4)) 3
    simp [sphereBasepoint]

/-- The projective-line/sphere homeomorphism preserves the chosen basepoints. -/
@[simp]
theorem complexProjectiveLineHomeomorphSphere_basepoint :
    complexProjectiveLineHomeomorphSphere (complexProjectiveModelBasepoint 1) =
      sphereBasepoint 2 := by
  rw [complexProjectiveModelBasepoint,
    complexProjectiveLineHomeomorphSphere_complexHopfMap,
    complexUnitSphereHomeomorphSphere_one_basepoint,
    hopfMap_basepoint]

end Submission
