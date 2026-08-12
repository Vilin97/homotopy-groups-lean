/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.FibrationLESGroup
import Submission.Hurewicz.SphereDiagonal
import Submission.MetricSpherePiOne

/-!
# The explicit Hopf map on exact metric spheres

This file constructs the classical Hopf map in the exact sphere models used by the lattice.  In
real coordinates it sends `(a,b,c,d) in S^3` to

`(a^2+b^2-c^2-d^2, 2(ac+bd), 2(bc-ad)) in S^2`.

The basepoint fibre is identified homeomorphically with the exact metric circle.  Combined with
the existing long exact sequence of a Serre fibration, this reduces `pi_3(S^2) = Z` to the one
remaining geometric assertion that this concrete Hopf map is a Serre fibration.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## Coordinate formula -/

/-- The ambient quadratic formula underlying the Hopf map. -/
noncomputable def hopfVec (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![
    x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2,
    2 * (x 0 * x 2 + x 1 * x 3),
    2 * (x 1 * x 2 - x 0 * x 3)]

@[simp]
theorem hopfVec_zero (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec x 0 = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  simp [hopfVec]

@[simp]
theorem hopfVec_one (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec x 1 = 2 * (x 0 * x 2 + x 1 * x 3) := by
  simp [hopfVec]

@[simp]
theorem hopfVec_two (x : EuclideanSpace ℝ (Fin 4)) :
    hopfVec x 2 = 2 * (x 1 * x 2 - x 0 * x 3) := by
  simp [hopfVec]

/-- The Hopf quadratic formula squares the Euclidean norm. -/
theorem norm_hopfVec_sq (x : EuclideanSpace ℝ (Fin 4)) :
    ‖hopfVec x‖ ^ 2 = ‖x‖ ^ 4 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, EuclideanSpace.real_norm_sq_eq]
  simp [hopfVec, Fin.sum_univ_succ]
  ring

/-- The ambient Hopf formula is continuous. -/
theorem continuous_hopfVec : Continuous hopfVec := by
  unfold hopfVec
  fun_prop

/-- Unit vectors are sent to unit vectors by the Hopf formula. -/
theorem norm_hopfVec_of_norm_eq_one (x : EuclideanSpace ℝ (Fin 4)) (hx : ‖x‖ = 1) :
    ‖hopfVec x‖ = 1 := by
  apply norm_eq_one_of_norm_sq_eq_one
  rw [norm_hopfVec_sq, hx]
  norm_num

/-- The classical Hopf map as a continuous map between the exact metric spheres `S^3` and
`S^2`. -/
noncomputable def hopfMap : C(Sph 3, Sph 2) where
  toFun x := ⟨hopfVec x, mem_sphere_zero_iff_norm.mpr <|
    norm_hopfVec_of_norm_eq_one x (norm_coe_sph x)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_hopfVec.comp continuous_subtype_val) ?_

/-- The chosen first-coordinate point is preserved by the Hopf map. -/
@[simp]
theorem hopfMap_basepoint : hopfMap (sphereBasepoint 3) = sphereBasepoint 2 := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have ht10 : (1 : Fin 3) ≠ 0 := by decide
  have ht20 : (2 : Fin 3) ≠ 0 := by decide
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfMap, hopfVec, sphereBasepoint, h10, h20, h30]
  · simp [hopfMap, hopfVec, sphereBasepoint, h10, h20, h30, ht10]
  · simp [hopfMap, hopfVec, sphereBasepoint, h10, h20, h30, ht20]

/-! ## The basepoint fibre -/

/-- Insert a two-dimensional Euclidean vector as the first two coordinates of a
four-dimensional one. -/
noncomputable def hopfCircleInclVec (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![z 0, z 1, 0, 0]

@[simp]
theorem hopfCircleInclVec_zero (z : EuclideanSpace ℝ (Fin 2)) :
    hopfCircleInclVec z 0 = z 0 := by
  simp [hopfCircleInclVec]

@[simp]
theorem hopfCircleInclVec_one (z : EuclideanSpace ℝ (Fin 2)) :
    hopfCircleInclVec z 1 = z 1 := by
  simp [hopfCircleInclVec]

@[simp]
theorem hopfCircleInclVec_two (z : EuclideanSpace ℝ (Fin 2)) :
    hopfCircleInclVec z 2 = 0 := by
  simp [hopfCircleInclVec]

@[simp]
theorem hopfCircleInclVec_three (z : EuclideanSpace ℝ (Fin 2)) :
    hopfCircleInclVec z 3 = 0 := by
  simp [hopfCircleInclVec]

/-- Coordinate insertion preserves the Euclidean norm. -/
theorem norm_hopfCircleInclVec (z : EuclideanSpace ℝ (Fin 2)) :
    ‖hopfCircleInclVec z‖ = ‖z‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfCircleInclVec, Fin.sum_univ_succ]

/-- Coordinate insertion is continuous. -/
theorem continuous_hopfCircleInclVec : Continuous hopfCircleInclVec := by
  unfold hopfCircleInclVec
  fun_prop

/-- Insert the exact metric circle as the coordinate circle in `S^3`. -/
noncomputable def hopfCircleIncl (z : Sph 1) : Sph 3 :=
  ⟨hopfCircleInclVec z, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfCircleInclVec, norm_coe_sph]⟩

/-- The coordinate-circle inclusion is continuous. -/
theorem continuous_hopfCircleIncl : Continuous hopfCircleIncl := by
  refine Continuous.subtype_mk
    (continuous_hopfCircleInclVec.comp continuous_subtype_val) ?_

/-- The coordinate circle lies in the basepoint fibre of the Hopf map. -/
theorem hopfMap_hopfCircleIncl (z : Sph 1) :
    hopfMap (hopfCircleIncl z) = sphereBasepoint 2 := by
  have hz : (z : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
      (z : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
    have h := congrArg (fun a : ℝ => a ^ 2) (norm_coe_sph z)
    rw [EuclideanSpace.real_norm_sq_eq] at h
    simpa [Fin.sum_univ_succ] using h
  have ht10 : (1 : Fin 3) ≠ 0 := by decide
  have ht20 : (2 : Fin 3) ≠ 0 := by decide
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [hopfMap, hopfVec, hopfCircleIncl, sphereBasepoint, hz]
  · simp [hopfMap, hopfVec, hopfCircleIncl, sphereBasepoint, ht10]
  · simp [hopfMap, hopfVec, hopfCircleIncl, sphereBasepoint, ht20]

/-- The basepoint fibre of the concrete Hopf map. -/
abbrev HopfFiber := (⇑hopfMap ⁻¹' {sphereBasepoint 2} : Set (Sph 3))

/-- The chosen point of the Hopf fibre, lying over the standard sphere basepoint. -/
noncomputable def hopfFiberBasepoint : HopfFiber :=
  ⟨sphereBasepoint 3, hopfMap_basepoint⟩

/-- Project a four-dimensional vector onto its first two coordinates. -/
noncomputable def hopfCircleProjVec (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![x 0, x 1]

@[simp]
theorem hopfCircleProjVec_zero (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleProjVec x 0 = x 0 := by
  simp [hopfCircleProjVec]

@[simp]
theorem hopfCircleProjVec_one (x : EuclideanSpace ℝ (Fin 4)) :
    hopfCircleProjVec x 1 = x 1 := by
  simp [hopfCircleProjVec]

/-- Projection onto the first two coordinates is continuous. -/
theorem continuous_hopfCircleProjVec : Continuous hopfCircleProjVec := by
  unfold hopfCircleProjVec
  fun_prop

/-- The four coordinate squares of a point of `S^3` sum to one. -/
theorem sphereThree_sum_sq (x : Sph 3) :
    (x : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
        (x : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 +
        (x : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 +
        (x : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 1 := by
  have h := congrArg (fun a : ℝ => a ^ 2) (norm_coe_sph x)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  simpa [Fin.sum_univ_succ, add_assoc] using h

/-- A point in the basepoint fibre has zero in its last two coordinates. -/
theorem hopfFiber_last_coords (x : HopfFiber) :
    ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3 = 0 := by
  have hs := sphereThree_sum_sq (x : Sph 3)
  have hmap : hopfMap (x : Sph 3) = sphereBasepoint 2 := x.property
  have hh : ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 0 ^ 2 +
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 1 ^ 2 -
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 -
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 1 := by
    have h := congrArg
      (fun y : Sph 2 => (y : EuclideanSpace ℝ (Fin 3)) 0) hmap
    simpa [hopfMap, sphereBasepoint] using h
  have hsum : ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 +
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 0 := by
    nlinarith
  have htwo : ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2 ^ 2 = 0 := by
    nlinarith [sq_nonneg (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3)]
  have hthree : ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 3 ^ 2 = 0 := by
    nlinarith [sq_nonneg (((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) 2)]
  exact ⟨sq_eq_zero_iff.mp htwo, sq_eq_zero_iff.mp hthree⟩

/-- Exact description of the fibre over the chosen basepoint: it is the coordinate circle cut out
by the last two coordinates. -/
theorem hopfMap_eq_basepoint_iff (x : Sph 3) :
    hopfMap x = sphereBasepoint 2 ↔
      (x : EuclideanSpace ℝ (Fin 4)) 2 = 0 ∧
        (x : EuclideanSpace ℝ (Fin 4)) 3 = 0 := by
  constructor
  · intro hx
    exact hopfFiber_last_coords ⟨x, hx⟩
  · rintro ⟨htwo, hthree⟩
    have hs := sphereThree_sum_sq x
    rw [htwo, hthree] at hs
    norm_num at hs
    have ht10 : (1 : Fin 3) ≠ 0 := by decide
    have ht20 : (2 : Fin 3) ≠ 0 := by decide
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [hopfMap, sphereBasepoint, htwo, hthree, hs]
    · simp [hopfMap, sphereBasepoint, htwo, hthree, ht10]
    · simp [hopfMap, sphereBasepoint, htwo, hthree, ht20]

/-- Projection of a fibre point onto its first two coordinates has unit norm. -/
theorem norm_hopfCircleProjVec (x : HopfFiber) :
    ‖hopfCircleProjVec ((x : Sph 3) : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
  rcases hopfFiber_last_coords x with ⟨htwo, hthree⟩
  have hs := sphereThree_sum_sq (x : Sph 3)
  apply norm_eq_one_of_norm_sq_eq_one
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [hopfCircleProjVec, Fin.sum_univ_succ]
  rw [htwo, hthree] at hs
  norm_num at hs
  exact hs

/-- The coordinate circle as a map into the basepoint fibre. -/
noncomputable def circleToHopfFiber (z : Sph 1) : HopfFiber :=
  ⟨hopfCircleIncl z, hopfMap_hopfCircleIncl z⟩

/-- Project a basepoint-fibre point back to the exact metric circle. -/
noncomputable def hopfFiberToCircle (x : HopfFiber) : Sph 1 :=
  ⟨hopfCircleProjVec ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)),
    mem_sphere_zero_iff_norm.mpr (norm_hopfCircleProjVec x)⟩

/-- The inclusion of the coordinate circle into the Hopf fibre is continuous. -/
theorem continuous_circleToHopfFiber : Continuous circleToHopfFiber := by
  refine Continuous.subtype_mk continuous_hopfCircleIncl ?_

/-- Projection of the Hopf fibre to the coordinate circle is continuous. -/
theorem continuous_hopfFiberToCircle : Continuous hopfFiberToCircle := by
  have hval : Continuous fun x : HopfFiber =>
      ((x : Sph 3) : EuclideanSpace ℝ (Fin 4)) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.subtype_mk (continuous_hopfCircleProjVec.comp hval) ?_

/-- The basepoint fibre of the exact Hopf map is homeomorphic to the exact metric circle. -/
noncomputable def circleHomeomorphHopfFiber : Sph 1 ≃ₜ HopfFiber where
  toFun := circleToHopfFiber
  invFun := hopfFiberToCircle
  left_inv z := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [circleToHopfFiber, hopfFiberToCircle, hopfCircleIncl]
  right_inv x := by
    rcases hopfFiber_last_coords x with ⟨htwo, hthree⟩
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [circleToHopfFiber, hopfFiberToCircle, hopfCircleIncl, htwo, hthree]
  continuous_toFun := continuous_circleToHopfFiber
  continuous_invFun := continuous_hopfFiberToCircle

/-- The fibre homeomorphism preserves the chosen basepoints. -/
@[simp]
theorem circleHomeomorphHopfFiber_basepoint :
    circleHomeomorphHopfFiber (sphereBasepoint 1) = hopfFiberBasepoint := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have ht10 : (1 : Fin 4) ≠ 0 := by decide
  have ht20 : (2 : Fin 4) ≠ 0 := by decide
  have ht30 : (3 : Fin 4) ≠ 0 := by decide
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [circleHomeomorphHopfFiber, circleToHopfFiber, hopfCircleIncl,
      hopfFiberBasepoint, sphereBasepoint, h10, ht10, ht20, ht30]

/-! ## Reduction of `pi_3(S^2)` to the fibration property -/

/-- Every homotopy group of the Hopf fibre above degree one is trivial. -/
theorem hopfFiber_higher_homotopy_subsingleton (k : ℕ) :
    Subsingleton (π_ (k + 2) HopfFiber hopfFiberBasepoint) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (k + 2))
    circleHomeomorphHopfFiber circleHomeomorphHopfFiber_basepoint
  exact e.toEquiv.subsingleton_congr.mp <|
    sph_one_higher_homotopy_subsingleton_at k (sphereBasepoint 1)

/-- The homomorphism on third homotopy groups induced by the exact Hopf map. -/
noncomputable def hopfPiThreeHom :
    π_ 3 (Sph 3) (sphereBasepoint 3) →* π_ 3 (Sph 2) (sphereBasepoint 2) :=
  pStarAbsHom hopfFiberBasepoint 2

/-- If the concrete Hopf map is a Serre fibration, its induced map on third homotopy groups is
bijective. -/
theorem hopfPiThreeHom_bijective (hp : IsSerreFibration hopfMap) :
    Function.Bijective hopfPiThreeHom := by
  have h := bijective_pStarAbs_of_subsingleton_fibre hopfFiberBasepoint hp 2
    (hopfFiber_higher_homotopy_subsingleton 1)
    (hopfFiber_higher_homotopy_subsingleton 0)
  have heq : (⇑hopfPiThreeHom) = pStarAbs hopfFiberBasepoint 3 := by
    funext x
    exact pStarAbsHom_apply hopfFiberBasepoint 2 x
  rw [heq]
  exact h

/-- The induced Hopf homomorphism as an equivalence, conditional only on the concrete map's
Serre-fibration property. -/
noncomputable def hopfPiThreeEquiv (hp : IsSerreFibration hopfMap) :
    π_ 3 (Sph 3) (sphereBasepoint 3) ≃* π_ 3 (Sph 2) (sphereBasepoint 2) :=
  MulEquiv.ofBijective hopfPiThreeHom (hopfPiThreeHom_bijective hp)

/-- The first off-diagonal sphere computation follows from the Serre-fibration property of the
explicit Hopf map.  All algebraic, fibre, and long-exact-sequence inputs are discharged here. -/
theorem pi3_sphere_two_mulEquiv_int_of_hopf_isSerreFibration
    (hp : IsSerreFibration hopfMap) :
    Nonempty
      (π_ 3 (Sph 2) (sphereBasepoint 2) ≃* Multiplicative ℤ) := by
  obtain ⟨source⟩ := sphere_diagonal_homotopy_mulEquiv_int 2
  exact ⟨(hopfPiThreeEquiv hp).symm.trans source⟩

end Submission
