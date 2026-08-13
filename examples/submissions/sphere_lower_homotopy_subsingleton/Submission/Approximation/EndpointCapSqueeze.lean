/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.RelativeSphereHomotopyCompression

/-!
# A southern half-space margin at the endpoints of a cap homotopy

Radial PL approximation preserves cap conditions cleanly when they are expressed as linear
half-space inequalities.  For a homotopy whose endpoints lie in the lower cap, this file moves
the endpoint values into the closed southern half-sphere while retaining a nonnegative-height
condition on every spatial boundary face.

The deformation keeps the equatorial vector and replaces height `h` by a convex interpolation
towards `min h 0`.  Its weight is `|2t-1|`, where `t` is homotopy time, so it is fully applied at
the two endpoints and is strictly partial at every interior time.  The raw vector can vanish
only at the north pole with full weight; the lower-cap endpoint hypothesis rules this out.

## Main results

* `Submission.endpointCapSqueezeWeight`
* `Submission.endpointCapSqueezeAmbient_eq_zero_imp`
* `Submission.endpointCapSqueezeRelativeSphereHomotopy`
* `Submission.endpointCapSqueezeRelativeSphereHomotopy_endpointHeightNonpos`
* `Submission.exists_endpointCapSqueezed_relativeSpherePLHomotopy_cellCompression`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d q : ℕ}

/-- Full strength at both time endpoints and smaller strength in the interior. -/
def endpointCapSqueezeWeight (t : I) : I :=
  ⟨|2 * (t : ℝ) - 1|, abs_nonneg _, by
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2]⟩

theorem continuous_endpointCapSqueezeWeight : Continuous endpointCapSqueezeWeight := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem endpointCapSqueezeWeight_zero : endpointCapSqueezeWeight 0 = 1 := by
  apply Subtype.ext
  norm_num [endpointCapSqueezeWeight]

@[simp] theorem endpointCapSqueezeWeight_one : endpointCapSqueezeWeight 1 = 1 := by
  apply Subtype.ext
  norm_num [endpointCapSqueezeWeight]

/-- The squeeze has full strength only at the two time endpoints. -/
theorem endpointCapSqueezeWeight_eq_one_iff (t : I) :
    endpointCapSqueezeWeight t = 1 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    have habs : |2 * (t : ℝ) - 1| = 1 := congrArg Subtype.val h
    have hsq := congrArg (fun x : ℝ => x ^ 2) habs
    rw [sq_abs] at hsq
    norm_num at hsq
    rcases hsq with ht | ht
    · have htval : (t : ℝ) = 1 := by linarith
      have htI : t = (1 : I) := by
        apply Subtype.ext
        exact htval
      exact Or.inr htI
    · exact Or.inl ht
  · rintro (rfl | rfl) <;> simp

/-- Interpolate the last coordinate towards the nonpositive half-line. -/
def endpointCapSqueezeHeight (u : I) (z : Sph (d + 1)) : ℝ :=
  (1 - (u : ℝ)) * sphHeight z +
    (u : ℝ) * min (sphHeight z) 0

theorem continuous_endpointCapSqueezeHeight :
    Continuous fun p : I × Sph (d + 1) => endpointCapSqueezeHeight p.1 p.2 := by
  have hu : Continuous fun p : I × Sph (d + 1) => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hh : Continuous fun p : I × Sph (d + 1) => sphHeight p.2 :=
    continuous_sphHeight.comp continuous_snd
  exact ((continuous_const.sub hu).mul hh).add
    (hu.mul (hh.min continuous_const))

/-- The ambient vector underlying the endpoint squeeze. -/
def endpointCapSqueezeAmbient (u : I) (z : Sph (d + 1)) :
    EuclideanSpace ℝ (Fin (d + 2)) :=
  snocLp (sphEquator z) (endpointCapSqueezeHeight u z)

theorem continuous_endpointCapSqueezeAmbient :
    Continuous fun p : I × Sph (d + 1) => endpointCapSqueezeAmbient p.1 p.2 := by
  exact continuous_snocLp.comp
    ((continuous_sphEquator.comp continuous_snd).prodMk
      continuous_endpointCapSqueezeHeight)

@[simp] theorem endpointCapSqueezeAmbient_one
    (z : Sph (d + 1)) :
    endpointCapSqueezeAmbient 1 z =
      snocLp (sphEquator z) (min (sphHeight z) 0) := by
  simp [endpointCapSqueezeAmbient, endpointCapSqueezeHeight]

/-- The raw vector can vanish only at the north pole, and only at full squeeze strength. -/
theorem endpointCapSqueezeAmbient_eq_zero_imp
    (u : I) (z : Sph (d + 1))
    (hz : endpointCapSqueezeAmbient u z = 0) :
    z = sphNorthPole d ∧ u = 1 := by
  have heq : sphEquator z = 0 := by
    apply PiLp.ext
    intro i
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
      v i.castSucc) hz
    simpa [endpointCapSqueezeAmbient] using h
  have hlast : endpointCapSqueezeHeight u z = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 2)) =>
      v (Fin.last (d + 1))) hz
    simpa [endpointCapSqueezeAmbient] using h
  have hsq : sphHeight z ^ 2 = 1 := by
    have h := norm_sphEquator_sq z
    rw [heq, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
    linarith
  have hheight : sphHeight z = 1 := by
    have hor := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq.trans (one_pow 2).symm)
    rcases hor with h | h
    · exact h
    · have hraw : endpointCapSqueezeHeight u z = -1 := by
        rw [endpointCapSqueezeHeight, h]
        norm_num
        ring
      linarith
  have hu : u = 1 := by
    rw [endpointCapSqueezeHeight, hheight] at hlast
    norm_num at hlast
    apply Subtype.ext
    exact (sub_eq_zero.mp hlast).symm
  refine ⟨?_, hu⟩
  apply Subtype.ext
  rw [← snocLp_sphEquator_sphHeight z]
  change snocLp (sphEquator z) (sphHeight z) = snocLp 0 1
  rw [heq, hheight]

/-- The endpoint squeeze is nonzero whenever full strength is used only on lower-cap values. -/
theorem endpointCapSqueezeAmbient_ne_zero_of_endpoint_mem_lowerCap
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d)
    (p : I × I^ Fin (q + 2)) :
    endpointCapSqueezeAmbient (endpointCapSqueezeWeight p.1) (H p) ≠ 0 := by
  rcases p with ⟨t, y⟩
  intro hraw
  obtain ⟨hnorth, hweight⟩ := endpointCapSqueezeAmbient_eq_zero_imp _ _ hraw
  rcases (endpointCapSqueezeWeight_eq_one_iff t).mp hweight with ht | ht
  · subst t
    have hmem : H (0, y) ∈ sphLowerCap d := hzero y
    rw [hnorth, mem_sphLowerCap, sphHeight_sphNorthPole] at hmem
    norm_num at hmem
  · subst t
    have hmem : H (1, y) ∈ sphLowerCap d := hone y
    rw [hnorth, mem_sphLowerCap, sphHeight_sphNorthPole] at hmem
    norm_num at hmem

/-- Apply the time-dependent endpoint squeeze and radially normalize. -/
def endpointCapSqueezeRelativeSphereHomotopy
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d) :
    C(I × I^ Fin (q + 2), Sph (d + 1)) where
  toFun p := radialSpherePoint
    (endpointCapSqueezeAmbient (endpointCapSqueezeWeight p.1) (H p))
    (endpointCapSqueezeAmbient_ne_zero_of_endpoint_mem_lowerCap H hzero hone p)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact continuous_endpointCapSqueezeAmbient.comp
        ((continuous_endpointCapSqueezeWeight.comp continuous_fst).prodMk H.continuous)
    · exact endpointCapSqueezeAmbient_ne_zero_of_endpoint_mem_lowerCap H hzero hone

@[simp] theorem coe_endpointCapSqueezeRelativeSphereHomotopy
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d)
    (p : I × I^ Fin (q + 2)) :
    ((endpointCapSqueezeRelativeSphereHomotopy H hzero hone p : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj
        (endpointCapSqueezeAmbient (endpointCapSqueezeWeight p.1) (H p)) :=
  rfl

/-- The two squeezed endpoints have nonpositive height. -/
theorem endpointCapSqueezeRelativeSphereHomotopy_endpointHeightNonpos
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d) :
    RelativeSphereHomotopy.EndpointHeightNonpos
      (endpointCapSqueezeRelativeSphereHomotopy H hzero hone) := by
  constructor
  · intro y
    change radialProj (endpointCapSqueezeAmbient
      (endpointCapSqueezeWeight 0) (H (0, y))) (Fin.last (d + 1)) ≤ 0
    apply radialProj_last_nonpos
    rw [endpointCapSqueezeWeight_zero, endpointCapSqueezeAmbient_one, snocLp_last]
    exact min_le_right _ _
  · intro y
    change radialProj (endpointCapSqueezeAmbient
      (endpointCapSqueezeWeight 1) (H (1, y))) (Fin.last (d + 1)) ≤ 0
    apply radialProj_last_nonpos
    rw [endpointCapSqueezeWeight_one, endpointCapSqueezeAmbient_one, snocLp_last]
    exact min_le_right _ _

/-- A nonnegative spatial-boundary height remains nonnegative during the endpoint squeeze. -/
theorem endpointCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d)
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H) :
    RelativeSphereHomotopy.BoundaryHeightNonneg
      (endpointCapSqueezeRelativeSphereHomotopy H hzero hone) := by
  intro t y hy
  apply radialProj_last_nonneg
  rw [endpointCapSqueezeAmbient, snocLp_last, endpointCapSqueezeHeight,
    min_eq_right (hheight t y hy)]
  simpa using mul_nonneg (sub_nonneg.mpr (endpointCapSqueezeWeight t).2.2)
    (hheight t y hy)

/-- A constant boundary jar remains exactly constant during the endpoint squeeze. -/
theorem endpointCapSqueezeRelativeSphereHomotopy_jarBased
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d)
    (hjar : RelativeSphereHomotopy.JarBased H) :
    RelativeSphereHomotopy.JarBased
      (endpointCapSqueezeRelativeSphereHomotopy H hzero hone) := by
  intro t y hy
  apply Subtype.ext
  change radialProj (endpointCapSqueezeAmbient
    (endpointCapSqueezeWeight t) (H (t, y))) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2)))
  rw [hjar t y hy]
  have hamb : endpointCapSqueezeAmbient (endpointCapSqueezeWeight t)
      (sphereBasepoint (d + 1)) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := by
    rw [endpointCapSqueezeAmbient, endpointCapSqueezeHeight,
      sphHeight_sphereBasepoint_succ]
    norm_num
    exact snocLp_sphEquator_sphHeight (sphereBasepoint (d + 1))
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1)))]

/-- Endpoint squeezing removes the strict endpoint hypothesis from the stable PL compression
theorem. -/
theorem exists_endpointCapSqueezed_relativeSpherePLHomotopy_cellCompression
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hzero : ∀ y, H (0, y) ∈ sphLowerCap d)
    (hone : ∀ y, H (1, y) ∈ sphLowerCap d)
    (hrange : q + 3 ≤ 2 * d) :
    ∃ (H' : C(I × I^ Fin (q + 2), Sph (d + 1)))
      (hheight' : RelativeSphereHomotopy.BoundaryHeightNonneg H')
      (hjar' : RelativeSphereHomotopy.JarBased H')
      (_hend' : RelativeSphereHomotopy.EndpointHeightNonpos H')
      (A : RelativeSpherePLHomotopyApproximation H' hheight' hjar')
      (x y : Sph (d + 1)),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 3), Sph (d + 1)),
        ∃ K : ContinuousMap.HomotopyRel
            (radialSphereCubeMap
              (cubeGridAffineApprox (q + 3) A.mesh
                (relativeSphereHomotopyToEuclidean H')) A.approx_ne_zero)
            g' (⊔I^(q + 3)),
          (∀ t z, z ∈ relativeSphereHomotopyLid q →
            K.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  let H' := endpointCapSqueezeRelativeSphereHomotopy H hzero hone
  let hheight' := endpointCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg
    H hzero hone hheight
  let hjar' := endpointCapSqueezeRelativeSphereHomotopy_jarBased H hzero hone hjar
  let hend' := endpointCapSqueezeRelativeSphereHomotopy_endpointHeightNonpos H hzero hone
  obtain ⟨A⟩ := exists_relativeSpherePLHomotopyApproximation H' hheight' hjar'
  obtain ⟨x, y, hx, hy, g', K, hK⟩ :=
    exists_relativeSpherePLHomotopy_cellCompression
      H' hheight' hjar' hend' A hrange
  exact ⟨H', hheight', hjar', hend', A, x, y, hx, hy, g', K, hK⟩

end Submission
