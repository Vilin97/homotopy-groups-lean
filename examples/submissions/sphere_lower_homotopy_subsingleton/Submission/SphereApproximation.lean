/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.SphereConnected

/-!
# Piecewise-affine approximation of based sphere maps

Every generalized loop in a metric sphere admits a finite piecewise-affine ambient
approximation which stays within distance `1 / 2`, never meets the origin, remains constant on
the cube boundary after radial projection, and represents the same homotopy-group element.

Unlike the general-position argument in `Submission.Model.SphereConnected`, this construction
has no inequality between the source and target dimensions.  It is therefore the reusable
finite-model reduction needed for diagonal sphere calculations and for a future degree
classification.

## Main results

* `Submission.SpherePLApproximation` — the finite approximation data attached to a based sphere
  map;
* `Submission.exists_spherePLApproximation` — existence in every source and sphere dimension;
* `Submission.homotopyGroup_exists_spherePLRepresentative` — every sphere homotopy class has
  such a finite representative.
-/

open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {k n : ℕ} {x : Sph n}

/-- A based sphere map together with a finite piecewise-affine ambient representative and a
proof that radial projection of that representative is based-homotopic to the original map. -/
structure SpherePLApproximation (f : Ω^ (Fin k) (Sph n) x) where
  /-- Number of grid subdivisions in each coordinate. -/
  mesh : ℕ
  /-- The grid is nondegenerate. -/
  mesh_pos : 1 ≤ mesh
  /-- Radial projection of the piecewise-affine map, regarded as a based sphere map. -/
  approx : Ω^ (Fin k) (Sph n) x
  /-- The piecewise-affine ambient map is uniformly close to the original unit-vector map. -/
  dist_le_half : ∀ y, dist
    (cubeGridAffineApprox k mesh (genLoopToEuclidean f) y)
    (genLoopToEuclidean f y) ≤ 1 / 2
  /-- Consequently the ambient approximation never meets the origin. -/
  approx_ne_zero : ∀ y, cubeGridAffineApprox k mesh (genLoopToEuclidean f) y ≠ 0
  /-- The sphere-valued approximation is exactly the radial projection of the ambient one. -/
  coe_approx : ∀ y,
    ((approx y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) =
      radialProj (cubeGridAffineApprox k mesh (genLoopToEuclidean f) y)
  /-- The approximation represents the same based homotopy class. -/
  homotopic : _root_.GenLoop.Homotopic f approx

/-- **Finite approximation of a based sphere map.**  Every generalized loop in `Sⁿ` is based
homotopic to the radial projection of a piecewise-affine map on a finite cubical grid.  The
ambient approximation remains within `1 / 2` of the original unit-vector map and hence never
vanishes.

No relation between `k` and `n` is required. -/
theorem exists_spherePLApproximation (f : Ω^ (Fin k) (Sph n) x) :
    Nonempty (SpherePLApproximation f) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  let F : C(I^ Fin k, EuclideanSpace ℝ (Fin (n + 1))) := genLoopToEuclidean f
  have hFnorm : ∀ y, ‖F y‖ = 1 := fun y => norm_coe_sph (f y)
  have hFbd : ∀ z ∈ Cube.boundary (Fin k),
      F z = ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun z hz => congrArg Subtype.val (_root_.GenLoop.boundary f z hz)
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le k F hhalf
  have hHdist : ∀ (t : I) (y : I^ Fin k),
      dist (cubeGridAffineApproxHomotopy k N F (t, y)) (F y) ≤ 1 / 2 :=
    fun t y => cubeGridAffineApproxHomotopy_dist_le F hdist t y
  have hHne : ∀ p : I × I^ Fin k, cubeGridAffineApproxHomotopy k N F p ≠ 0 := by
    rintro ⟨t, y⟩ hzero
    have h := hHdist t y
    rw [hzero, dist_zero_left, hFnorm] at h
    linarith
  have hGne : ∀ y : I^ Fin k, cubeGridAffineApprox k N F y ≠ 0 := by
    intro y
    have h := hHne (1, y)
    rwa [cubeGridAffineApproxHomotopy_one] at h
  have hxnorm : ‖((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := norm_coe_sph x
  have hGbd : ∀ z ∈ Cube.boundary (Fin k),
      cubeGridAffineApprox k N F z =
        ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun z hz => cubeGridAffineApprox_eq_of_mem_boundary hN F hFbd hz
  have hHbd : ∀ (t : I) (z : I^ Fin k), z ∈ Cube.boundary (Fin k) →
      cubeGridAffineApproxHomotopy k N F (t, z) =
        ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) := by
    intro t z hz
    rw [cubeGridAffineApproxHomotopy_apply, hFbd z hz, hGbd z hz, ← add_smul]
    norm_num
  obtain ⟨g, hg⟩ : ∃ g : Ω^ (Fin k) (Sph n) x, ∀ y : I^ Fin k,
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) =
        radialProj (cubeGridAffineApprox k N F y) :=
    ⟨⟨⟨fun y => ⟨radialProj (cubeGridAffineApprox k N F y),
          mem_sphere_zero_iff_norm.mpr (norm_radialProj (hGne y))⟩,
        Continuous.subtype_mk
          (continuous_radialProj (cubeGridAffineApprox k N F).continuous hGne) _⟩,
      fun z hz => Subtype.ext (by
        change radialProj (cubeGridAffineApprox k N F z) = _
        rw [hGbd z hz]
        exact radialProj_of_norm_eq_one hxnorm)⟩, fun _ => rfl⟩
  have hhom : _root_.GenLoop.Homotopic f g := by
    apply genLoopHomotopic_of_radialHomotopy f g
      (cubeGridAffineApproxHomotopy k N F) hHne
    · intro y
      rw [cubeGridAffineApproxHomotopy_zero]
      exact radialProj_of_norm_eq_one (hFnorm y)
    · intro y
      rw [cubeGridAffineApproxHomotopy_one]
      exact (hg y).symm
    · intro s z hz
      rw [hHbd s z hz, radialProj_of_norm_eq_one hxnorm]
  refine ⟨⟨N, hN, g, ?_, ?_, ?_, hhom⟩⟩
  · simpa [F] using hdist
  · simpa [F] using hGne
  · simpa [F] using hg

/-- **Every sphere homotopy class has a finite piecewise-affine representative.**  More
precisely, each class can be represented by the radial projection of a finite-grid affine map,
with all quantitative and relative-boundary data retained in `SpherePLApproximation`. -/
theorem homotopyGroup_exists_spherePLRepresentative
    (a : HomotopyGroup (Fin k) (Sph n) x) :
    ∃ (f : Ω^ (Fin k) (Sph n) x) (A : SpherePLApproximation f), a = ⟦A.approx⟧ := by
  induction a using Quotient.inductionOn with
  | h f =>
      obtain ⟨A⟩ := exists_spherePLApproximation f
      exact ⟨f, A, Quotient.sound A.homotopic⟩

end Submission
