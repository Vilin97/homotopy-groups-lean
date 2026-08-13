/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCellPairGeneralPosition

/-!
# Stable two-cell compression on a sphere

This file joins the two independent parts of the direct cubical homotopy-excision argument.
`SphereCellPairGeneralPosition` chooses points `x` and `y` in the lower and upper open cells,
respectively, with `x` absent from the vertical prism over the `y`-fiber.
`ProjectedFiberPrism` then compresses the last source coordinate.

If the side and bottom faces land in the lower cap, they avoid `y`.  If a distinguished source
set lands in the upper cap, it avoids `x`; exact preservation of the `x`-fiber keeps this true
throughout the compression.  The endpoint avoids `y` everywhere.  This is the complete
geometric deformation step in the one-cell-per-side proof of homotopy excision.

## Main results

* `Submission.exists_sphereCell_compression`
* `Submission.exists_sphereCell_compression_of_stableRange`
* `Submission.exists_cubeGridAffineApprox_sphereCell_compression_of_stableRange`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d n q N : ℕ}

/-- Stable two-cell compression for a nowhere-zero locally Lipschitz ambient cubical map. -/
theorem exists_sphereCell_compression
    (G : C(I^ Fin (n + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hG : LocallyLipschitz G) (hGne : ∀ z, G z ≠ 0)
    (hhalf : ∀ z, 1 / 2 ≤ ‖G z‖)
    (hdim : n + 4 < 2 * (d + 2))
    (S : Set (I^ Fin (n + 1)))
    (hside : ∀ (r : I^ Fin n), r ∈ Cube.boundary (Fin n) →
      ∀ s : I, radialSphereCubeMap G hGne
        (Cube.splitAtLast.symm (s, r)) ∈ sphLowerCap d)
    (hbot : ∀ r : I^ Fin n, radialSphereCubeMap G hGne
      (Cube.splitAtLast.symm (0, r)) ∈ sphLowerCap d)
    (hprotected : ∀ z ∈ S, radialSphereCubeMap G hGne z ∈ sphUpperCap d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (n + 1), Sph (d + 1)),
        ∃ H : ContinuousMap.HomotopyRel (radialSphereCubeMap G hGne) g'
            (⊔I^(n + 1)),
          (∀ t z, z ∈ S → H.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  obtain ⟨x, y, hx, hy, hprism⟩ :=
    exists_sphereCell_pair_not_mem_prism_image G hG hGne hhalf hdim
  obtain ⟨g', H, hHprotected, hg'y⟩ :=
    exists_homotopicRel_boundaryJar_avoiding_on_protectedSet
      (radialSphereCubeMap G hGne) x y S hprism
      (fun r hr s hsy => hy (hsy ▸ hside r hr s))
      (fun r hry => hy (hry ▸ hbot r))
      (fun z hz hzx => hx (hzx ▸ hprotected z hz))
  exact ⟨x, y, hx, hy, g', H, hHprotected, hg'y⟩

/-- The preceding theorem in the stable cap-excision indexing.  Here the source is a
`(q+3)`-cube and `q+3 ≤ 2d` is the subtraction-free stable inequality. -/
theorem exists_sphereCell_compression_of_stableRange
    (G : C(I^ Fin (q + 3), EuclideanSpace ℝ (Fin (d + 2))))
    (hG : LocallyLipschitz G) (hGne : ∀ z, G z ≠ 0)
    (hhalf : ∀ z, 1 / 2 ≤ ‖G z‖)
    (hrange : q + 3 ≤ 2 * d)
    (S : Set (I^ Fin (q + 3)))
    (hside : ∀ (r : I^ Fin (q + 2)), r ∈ Cube.boundary (Fin (q + 2)) →
      ∀ s : I, radialSphereCubeMap G hGne
        (Cube.splitAtLast.symm (s, r)) ∈ sphLowerCap d)
    (hbot : ∀ r : I^ Fin (q + 2), radialSphereCubeMap G hGne
      (Cube.splitAtLast.symm (0, r)) ∈ sphLowerCap d)
    (hprotected : ∀ z ∈ S, radialSphereCubeMap G hGne z ∈ sphUpperCap d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 3), Sph (d + 1)),
        ∃ H : ContinuousMap.HomotopyRel (radialSphereCubeMap G hGne) g'
            (⊔I^(q + 3)),
          (∀ t z, z ∈ S → H.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  exact exists_sphereCell_compression (n := q + 2) G hG hGne hhalf
    (by omega) S hside hbot hprotected

/-- A cubical approximation within distance `1/2` of a norm-one map never vanishes. -/
theorem cubeGridAffineApprox_ne_zero_of_dist_le_half
    (g : C(I^ Fin (q + 3), EuclideanSpace ℝ (Fin (d + 2))))
    (hgnorm : ∀ z, ‖g z‖ = 1)
    (hdist : ∀ z,
      dist (cubeGridAffineApprox (q + 3) N g z) (g z) ≤ 1 / 2)
    (z : I^ Fin (q + 3)) :
    cubeGridAffineApprox (q + 3) N g z ≠ 0 := by
  have hhalf := cubeGridAffineApprox_norm_ge_half g hgnorm hdist z
  intro hzero
  rw [hzero, norm_zero] at hhalf
  norm_num at hhalf

/-- A grid approximation within distance `1/2` of a unit-sphere map automatically has the norm
bound and local Lipschitz regularity required for stable two-cell compression. -/
theorem exists_cubeGridAffineApprox_sphereCell_compression_of_stableRange
    (g : C(I^ Fin (q + 3), EuclideanSpace ℝ (Fin (d + 2))))
    (hgnorm : ∀ z, ‖g z‖ = 1)
    (hdist : ∀ z,
      dist (cubeGridAffineApprox (q + 3) N g z) (g z) ≤ 1 / 2)
    (hrange : q + 3 ≤ 2 * d)
    (S : Set (I^ Fin (q + 3)))
    (hside : ∀ (r : I^ Fin (q + 2)), r ∈ Cube.boundary (Fin (q + 2)) →
      ∀ s : I, radialSphereCubeMap (cubeGridAffineApprox (q + 3) N g)
          (fun z => cubeGridAffineApprox_ne_zero_of_dist_le_half g hgnorm hdist z)
        (Cube.splitAtLast.symm (s, r)) ∈ sphLowerCap d)
    (hbot : ∀ r : I^ Fin (q + 2),
      radialSphereCubeMap (cubeGridAffineApprox (q + 3) N g)
          (fun z => cubeGridAffineApprox_ne_zero_of_dist_le_half g hgnorm hdist z)
        (Cube.splitAtLast.symm (0, r)) ∈ sphLowerCap d)
    (hprotected : ∀ z ∈ S,
      radialSphereCubeMap (cubeGridAffineApprox (q + 3) N g)
          (fun z => cubeGridAffineApprox_ne_zero_of_dist_le_half g hgnorm hdist z) z ∈
        sphUpperCap d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 3), Sph (d + 1)),
        ∃ H : ContinuousMap.HomotopyRel
            (radialSphereCubeMap (cubeGridAffineApprox (q + 3) N g)
              (fun z => cubeGridAffineApprox_ne_zero_of_dist_le_half g hgnorm hdist z))
            g' (⊔I^(q + 3)),
          (∀ t z, z ∈ S → H.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  let G := cubeGridAffineApprox (q + 3) N g
  have hhalf : ∀ z, 1 / 2 ≤ ‖G z‖ :=
    cubeGridAffineApprox_norm_ge_half g hgnorm hdist
  have hGne : ∀ z, G z ≠ 0 :=
    cubeGridAffineApprox_ne_zero_of_dist_le_half g hgnorm hdist
  exact exists_sphereCell_compression_of_stableRange G
    (locallyLipschitz_cubeGridAffineApprox g) hGne hhalf hrange S
    (by simpa only [G] using hside)
    (by simpa only [G] using hbot)
    (by simpa only [G] using hprotected)

end Submission
