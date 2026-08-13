/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCellCompression
import Submission.Approximation.RelativeSphereHomotopy

/-!
# Stable two-cell compression of a relative sphere homotopy

A homotopy between two maps into the lower spherical cap has the precise cubical tetrad shape
needed by `SphereCellCompression`.  We put homotopy time in the first coordinate and compress
the final spatial coordinate.  The two time faces and all jar faces land in the lower cap, while
the spatial lid lands in the upper cap.

To make these statements survive radial piecewise-linear approximation, this file uses strict
half-space margins: both time endpoints have nonpositive height and every spatial boundary has
nonnegative height.  Affine interpolation preserves these linear inequalities.  The resulting
stable compression avoids an upper-cell point globally while preserving avoidance of a
lower-cell point on the spatial lid.

## Main results

* `Submission.RelativeSphereHomotopy.EndpointHeightNonpos`
* `Submission.cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_zero`
* `Submission.exists_relativeSpherePLHomotopy_cellCompression`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d q N : ℕ}

/-- Both time endpoints of a sphere homotopy lie in the closed southern half-sphere. -/
def RelativeSphereHomotopy.EndpointHeightNonpos
    (H : C(I × I^ Fin (q + 2), Sph (d + 1))) : Prop :=
  (∀ y, sphHeight (H (0, y)) ≤ 0) ∧
    ∀ y, sphHeight (H (1, y)) ≤ 0

/-- On the time-zero face, affine grid approximation preserves nonpositive height. -/
theorem cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_zero
    (hN : 1 ≤ N) (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (y : I^ Fin (q + 2)) :
    cubeGridAffineApprox (q + 3) N (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 0 y) (Fin.last (d + 1)) ≤ 0 := by
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ), map_sum]
  simp only [map_smul, PiLp.projₗ_apply, smul_eq_mul]
  apply Finset.sum_nonpos
  intro v hv
  apply mul_nonpos_of_nonneg_of_nonpos gridCoeff_nonneg
  have hvzero : gridVertex N v 0 = 0 :=
    gridVertex_eq_zero_of_gridCoeff_pos hN (by simp) hv
  change sphHeight (H (gridVertex N v 0,
    fun i : Fin (q + 2) => gridVertex N v i.succ)) ≤ 0
  rw [hvzero]
  exact hend.1 _

/-- On the time-one face, affine grid approximation preserves nonpositive height. -/
theorem cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_one
    (hN : 1 ≤ N) (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (y : I^ Fin (q + 2)) :
    cubeGridAffineApprox (q + 3) N (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 1 y) (Fin.last (d + 1)) ≤ 0 := by
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ), map_sum]
  simp only [map_smul, PiLp.projₗ_apply, smul_eq_mul]
  apply Finset.sum_nonpos
  intro v hv
  apply mul_nonpos_of_nonneg_of_nonpos gridCoeff_nonneg
  have hvone : gridVertex N v 0 = 1 :=
    gridVertex_eq_one_of_gridCoeff_pos hN (by simp) hv
  change sphHeight (H (gridVertex N v 0,
    fun i : Fin (q + 2) => gridVertex N v i.succ)) ≤ 0
  rw [hvone]
  exact hend.2 _

/-- Radial normalization preserves a nonpositive last coordinate. -/
theorem radialProj_last_nonpos
    {v : EuclideanSpace ℝ (Fin (d + 2))}
    (hv : v (Fin.last (d + 1)) ≤ 0) :
    radialProj v (Fin.last (d + 1)) ≤ 0 := by
  rw [radialProj, PiLp.smul_apply, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.mpr (norm_nonneg v)) hv

/-- The spatial lid, viewed inside the time-first homotopy cube. -/
def relativeSphereHomotopyLid (q : ℕ) : Set (I^ Fin (q + 3)) :=
  {z | (fun i : Fin (q + 2) => z i.succ) ∈ Cube.boundaryLid (q + 2)}

theorem relativeSphereHomotopyLid_subset_spatialBoundary
    {z : I^ Fin (q + 3)} (hz : z ∈ relativeSphereHomotopyLid q) :
    (fun i : Fin (q + 2) => z i.succ) ∈ ∂I^(q + 2) := by
  refine ⟨Fin.last (q + 1), Or.inr ?_⟩
  exact hz

/-- The bottom face for the last spatial coordinate is part of the spatial boundary jar. -/
theorem splitAtLast_bottom_spatialTail_mem_boundaryJar
    (r : I^ Fin (q + 2)) :
    (fun i : Fin (q + 2) =>
      Cube.splitAtLast.symm (0, r) i.succ) ∈ ⊔I^(q + 2) := by
  apply Cube.mem_boundaryJar_of_exists_eq_zero
  refine ⟨Fin.last (q + 1), ?_⟩
  have hi : (Fin.last (q + 1)).succ = Fin.last (q + 2) := Fin.ext rfl
  rw [hi]
  exact Cube.splitAtLast_symm_apply_last 0 r

/-- A non-time boundary coordinate of the projected cube is a side coordinate of the spatial
boundary jar. -/
theorem splitAtLast_spatialTail_mem_boundaryJar_of_projected_succ_boundary
    (s : I) (r : I^ Fin (q + 2)) (i : Fin (q + 1))
    (hi : r i.succ = 0 ∨ r i.succ = 1) :
    (fun j : Fin (q + 2) =>
      Cube.splitAtLast.symm (s, r) j.succ) ∈ ⊔I^(q + 2) := by
  apply Cube.mem_boundaryJar_of_lt_last
  refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
  have hindex : (i.castSucc : Fin (q + 2)).succ ≠ Fin.last (q + 2) := by
    have heq : (i.castSucc : Fin (q + 2)).succ = i.succ.castSucc := Fin.ext rfl
    rw [heq]
    exact Fin.castSucc_ne_last i.succ
  rw [Cube.splitAtLast_symm_apply_eq_of_neq_last s r _ hindex]
  have hindex' :
      (⟨(i.castSucc : Fin (q + 2)).succ,
        Fin.lt_last_iff_ne_last.mpr hindex⟩ : Fin (q + 2)) = i.succ :=
    Fin.ext rfl
  rw [hindex']
  exact hi

/-- A time endpoint of the projected cube is a time endpoint of the full cube. -/
theorem splitAtLast_symm_zero_apply
    (s : I) (r : I^ Fin (q + 2)) :
    Cube.splitAtLast.symm (s, r) 0 = r 0 := by
  apply Cube.splitAtLast_symm_apply_eq_of_neq_last
  change (0 : Fin (q + 2)).castSucc ≠ Fin.last (q + 2)
  exact Fin.castSucc_ne_last 0

/-- The radial map on the full PL homotopy cube is the corresponding bundled relative-loop
slice after separating the first coordinate. -/
theorem radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (z : I^ Fin (q + 3)) :
    radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero z =
      (A.approxSlice (z 0)).val (fun i => z i.succ) := by
  apply Subtype.ext
  change radialProj (cubeGridAffineApprox (q + 3) A.mesh
      (relativeSphereHomotopyToEuclidean H) z) =
    radialProj (cubeGridAffineApprox (q + 3) A.mesh
      (relativeSphereHomotopyToEuclidean H)
        (Fin.cons (z 0) fun i => z i.succ))
  rw [show Fin.cons (z 0) (fun i => z i.succ) = z from Fin.cons_self_tail z]

/-- Stable two-cell compression of a cap-safe PL approximation to a relative sphere homotopy. -/
theorem exists_relativeSpherePLHomotopy_cellCompression
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hrange : q + 3 ≤ 2 * d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 3), Sph (d + 1)),
        ∃ K : ContinuousMap.HomotopyRel
            (radialSphereCubeMap
              (cubeGridAffineApprox (q + 3) A.mesh
                (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
            g' (⊔I^(q + 3)),
          (∀ t z, z ∈ relativeSphereHomotopyLid q →
            K.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  let G := cubeGridAffineApprox (q + 3) A.mesh
    (relativeSphereHomotopyToEuclidean H)
  have hhalf : ∀ z, 1 / 2 ≤ ‖G z‖ :=
    cubeGridAffineApprox_norm_ge_half (relativeSphereHomotopyToEuclidean H)
      (fun z => norm_coe_sph (H (z 0, fun i => z i.succ))) A.dist_le_half
  apply exists_sphereCell_compression_of_stableRange G
    (locallyLipschitz_cubeGridAffineApprox (relativeSphereHomotopyToEuclidean H))
    A.approx_ne_zero hhalf hrange (relativeSphereHomotopyLid q)
  · intro r hr s
    obtain ⟨i, hi⟩ := hr
    induction i using Fin.cases with
    | zero =>
        rcases hi with hi | hi
        · let z := Cube.splitAtLast.symm (s, r)
          have hz0 : z 0 = 0 := by
            dsimp only [z]
            exact (splitAtLast_symm_zero_apply s r).trans hi
          have hzcons : z = Fin.cons 0 (fun j => z j.succ) := by
            rw [← hz0]
            exact (Fin.cons_self_tail z).symm
          rw [mem_sphLowerCap]
          change radialProj (G z) (Fin.last (d + 1)) ≤ 1 / 3
          rw [hzcons]
          dsimp only [G]
          exact (radialProj_last_nonpos
            (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_zero
              A.mesh_pos H hend (fun j => z j.succ))).trans
            (by norm_num)
        · let z := Cube.splitAtLast.symm (s, r)
          have hz1 : z 0 = 1 := by
            dsimp only [z]
            exact (splitAtLast_symm_zero_apply s r).trans hi
          have hzcons : z = Fin.cons 1 (fun j => z j.succ) := by
            rw [← hz1]
            exact (Fin.cons_self_tail z).symm
          rw [mem_sphLowerCap]
          change radialProj (G z) (Fin.last (d + 1)) ≤ 1 / 3
          rw [hzcons]
          dsimp only [G]
          exact (radialProj_last_nonpos
            (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_one
              A.mesh_pos H hend (fun j => z j.succ))).trans
            (by norm_num)
    | succ i =>
        have htail :=
          splitAtLast_spatialTail_mem_boundaryJar_of_projected_succ_boundary s r i hi
        let z := Cube.splitAtLast.symm (s, r)
        rw [show radialSphereCubeMap G A.approx_ne_zero z =
            (A.approxSlice (z 0)).val (fun j => z j.succ) by
          exact radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
            H hheight hjar A z]
        rw [(A.approxSlice (z 0)).property.2 _ htail]
        exact sphereBasepoint_mem_sphLowerCap d
  · intro r
    have htail := splitAtLast_bottom_spatialTail_mem_boundaryJar (q := q) r
    let z := Cube.splitAtLast.symm (0, r)
    rw [show radialSphereCubeMap G A.approx_ne_zero z =
        (A.approxSlice (z 0)).val (fun j => z j.succ) by
      exact radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
        H hheight hjar A z]
    rw [(A.approxSlice (z 0)).property.2 _ htail]
    exact sphereBasepoint_mem_sphLowerCap d
  · intro z hz
    rw [show radialSphereCubeMap G A.approx_ne_zero z =
        (A.approxSlice (z 0)).val (fun j => z j.succ) by
      exact radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
        H hheight hjar A z]
    exact (A.approxSlice (z 0)).property.1 _
      (relativeSphereHomotopyLid_subset_spatialBoundary hz)

end Submission
