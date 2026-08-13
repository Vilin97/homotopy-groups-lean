/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.BoundaryRelativeGeneralPosition

/-!
# Finite PL approximation of relative sphere homotopies

A relative homotopy is a map on a time interval times a cube. Placing time in the first cube
coordinate lets one approximate the whole family on a single Kuhn grid. The key face lemmas show
that this approximation preserves nonnegative height on every spatial boundary face and fixes the
spatial boundary jar exactly. A uniform distance bound keeps both the approximation and its
straight-line comparison away from zero, so radial projection supplies a homotopy through
relative sphere loops.

Every relative homotopy can first be postcomposed with the upper-cap squeeze. Thus the strict
nonnegative-height hypothesis entails no loss of relative homotopy classes.

## Main results

* `Submission.exists_relativeSpherePLHomotopyApproximation`
* `Submission.upperCapSqueezeRelativeSphereHomotopy`
* `Submission.exists_relativeSpherePLHomotopyRepresentatives_of_homotopic`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {k N d : ℕ}

/-! ### Grid approximation on the spatial faces of a homotopy cube -/

theorem gridVertex_tail_mem_boundary_of_gridCoeff_pos (hN : 1 ≤ N)
    {v : Fin (k + 2) → ℕ} {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ∂I^(k + 1))
    (hv : v ∈ activeVerts N y) :
    (fun i : Fin (k + 1) => gridVertex N v i.succ) ∈ ∂I^(k + 1) := by
  obtain ⟨i, hi⟩ := hy
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact Or.inl (gridVertex_eq_zero_of_gridCoeff_pos hN hi hv)
  · exact Or.inr (gridVertex_eq_one_of_gridCoeff_pos hN hi hv)

theorem gridVertex_tail_mem_boundaryJar_of_gridCoeff_pos (hN : 1 ≤ N)
    {v : Fin (k + 2) → ℕ} {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ⊔I^(k + 1))
    (hv : v ∈ activeVerts N y) :
    (fun i : Fin (k + 1) => gridVertex N v i.succ) ∈ ⊔I^(k + 1) := by
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hside
  · apply Cube.mem_boundaryJar_of_exists_eq_zero
    refine ⟨Fin.last k, ?_⟩
    rw [Cube.splitAtLast_fst_eq] at hbot
    exact gridVertex_eq_zero_of_gridCoeff_pos hN hbot hv
  · obtain ⟨i, hi⟩ := hside
    apply Cube.mem_boundaryJar_of_lt_last
    refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
    rw [Cube.splitAtLast_snd_apply_eq] at hi
    rcases hi with hi | hi
    · exact Or.inl (gridVertex_eq_zero_of_gridCoeff_pos hN hi hv)
    · exact Or.inr (gridVertex_eq_one_of_gridCoeff_pos hN hi hv)

theorem cubeGridAffineApprox_last_nonneg_of_tail_mem_boundary
    (hN : 1 ≤ N)
    (g : C(I^ Fin (k + 2), EuclideanSpace ℝ (Fin (d + 2))))
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (∂I^(k + 1)) →
      0 ≤ g z (Fin.last (d + 1)))
    {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApprox (k + 2) N g y (Fin.last (d + 1)) := by
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ), map_sum]
  simp only [map_smul, PiLp.projₗ_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun v hv => mul_nonneg gridCoeff_nonneg
    (hg _ (gridVertex_tail_mem_boundary_of_gridCoeff_pos hN hy hv))

theorem cubeGridAffineApprox_eq_of_tail_mem_boundaryJar
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 2), V)) {b : V}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b)
    {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ⊔I^(k + 1)) :
    cubeGridAffineApprox (k + 2) N g y = b := by
  have hval : ∀ v ∈ activeVerts N y, g (gridVertex N v) = b := fun v hv =>
    hg _ (gridVertex_tail_mem_boundaryJar_of_gridCoeff_pos hN hy hv)
  rw [cubeGridAffineApprox_eq_sum_activeVerts,
    Finset.sum_congr rfl (fun v hv => by rw [hval v hv]), ← Finset.sum_smul,
    sum_gridCoeff_activeVerts hN, one_smul]

/-! ### Relative sphere homotopies as maps on one larger cube -/

/-- A sphere-valued homotopy, with time placed in the first cube coordinate, read in the
ambient Euclidean space. -/
noncomputable def relativeSphereHomotopyToEuclidean
    (H : C(I × I^ Fin (k + 1), Sph (d + 1))) :
    C(I^ Fin (k + 2), EuclideanSpace ℝ (Fin (d + 2))) :=
  ⟨fun y => ((H (y 0, fun i => y i.succ) : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))), by fun_prop⟩

@[simp] theorem relativeSphereHomotopyToEuclidean_apply
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (s : I) (y : I^ Fin (k + 1)) :
    relativeSphereHomotopyToEuclidean H (Fin.cons s y) =
      ((H (s, y) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) := by
  rfl

/-- The strengthened cap condition needed for radial PL approximation of a relative
homotopy: every spatial boundary value has nonnegative height. -/
def RelativeSphereHomotopy.BoundaryHeightNonneg
    (H : C(I × I^ Fin (k + 1), Sph (d + 1))) : Prop :=
  ∀ s y, y ∈ (∂I^(k + 1)) → 0 ≤ sphHeight (H (s, y))

/-- The relative base condition for a sphere-valued homotopy: every time slice fixes the
spatial boundary jar. -/
def RelativeSphereHomotopy.JarBased
    (H : C(I × I^ Fin (k + 1), Sph (d + 1))) : Prop :=
  ∀ s y, y ∈ (⊔I^(k + 1)) → H (s, y) = sphereBasepoint (d + 1)

/-- A time slice of a cap-safe, jar-relative sphere homotopy, bundled as a relative loop. -/
noncomputable def relativeSphereHomotopySlice
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H) (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y => H (s, y), by fun_prop⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        exact le_trans (by norm_num) (hheight s y hy),
      fun y hy => hjar s y hy⟩⟩

@[simp] theorem relativeSphereHomotopySlice_apply
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H) (s : I) (y : I^ Fin (k + 1)) :
    (relativeSphereHomotopySlice H hheight hjar s).val y = H (s, y) :=
  rfl

/-- Grid approximation on the homotopy cube preserves nonnegative height on every spatial
boundary face. -/
theorem cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
    (hN : 1 ≤ N) (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApprox (k + 2) N (relativeSphereHomotopyToEuclidean H)
      (Fin.cons s y) (Fin.last (d + 1)) := by
  apply cubeGridAffineApprox_last_nonneg_of_tail_mem_boundary hN _ _ hy
  intro z hz
  exact hheight (z 0) (fun i => z i.succ) hz

/-- Grid approximation on the homotopy cube fixes every spatial jar face exactly. -/
theorem cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar
    (hN : 1 ≤ N) (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hjar : RelativeSphereHomotopy.JarBased H)
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeGridAffineApprox (k + 2) N (relativeSphereHomotopyToEuclidean H)
      (Fin.cons s y) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := by
  apply cubeGridAffineApprox_eq_of_tail_mem_boundaryJar hN _ _ hy
  intro z hz
  exact congrArg Subtype.val (hjar (z 0) (fun i => z i.succ) hz)

/-- A time slice of the radial projection of a PL approximation to a relative sphere
homotopy. The spatial cap and jar conditions are preserved simultaneously for every time. -/
noncomputable def radialCubeGridAffineApproxRelativeSphereHomotopySlice
    (N : ℕ) (hN : 1 ≤ N)
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hne : ∀ y, cubeGridAffineApprox (k + 2) N
      (relativeSphereHomotopyToEuclidean H) y ≠ 0)
    (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (cubeGridAffineApprox (k + 2) N
          (relativeSphereHomotopyToEuclidean H) (Fin.cons s y)),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne (Fin.cons s y)))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        ((cubeGridAffineApprox (k + 2) N
          (relativeSphereHomotopyToEuclidean H)).continuous.comp (by fun_prop))
        (fun y => hne (Fin.cons s y))) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤ radialProj
          (cubeGridAffineApprox (k + 2) N
            (relativeSphereHomotopyToEuclidean H) (Fin.cons s y))
              (Fin.last (d + 1))
        exact le_trans (by norm_num)
          (radialProj_last_nonneg
            (cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
              hN H hheight s hy)),
      fun y hy => Subtype.ext (by
        change radialProj (cubeGridAffineApprox (k + 2) N
          (relativeSphereHomotopyToEuclidean H) (Fin.cons s y)) =
            ((sphereBasepoint (d + 1) : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2)))
        rw [cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar
          hN H hjar s hy]
        exact radialProj_of_norm_eq_one
          (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialCubeGridAffineApproxRelativeSphereHomotopySlice
    (N : ℕ) (hN : 1 ≤ N)
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hne : ∀ y, cubeGridAffineApprox (k + 2) N
      (relativeSphereHomotopyToEuclidean H) y ≠ 0)
    (s : I) (y : I^ Fin (k + 1)) :
    (((radialCubeGridAffineApproxRelativeSphereHomotopySlice
      N hN H hheight hjar hne s).val y : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (cubeGridAffineApprox (k + 2) N
        (relativeSphereHomotopyToEuclidean H) (Fin.cons s y)) :=
  rfl

/-- The radial PL slices themselves vary through relative sphere loops. -/
theorem radialCubeGridAffineApproxRelativeSphereHomotopy_homotopic
    (N : ℕ) (hN : 1 ≤ N)
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hne : ∀ y, cubeGridAffineApprox (k + 2) N
      (relativeSphereHomotopyToEuclidean H) y ≠ 0) :
    RelGenLoop.Homotopic
      (radialCubeGridAffineApproxRelativeSphereHomotopySlice
        N hN H hheight hjar hne 0)
      (radialCubeGridAffineApproxRelativeSphereHomotopySlice
        N hN H hheight hjar hne 1) := by
  let G : C(I^ Fin (k + 2), EuclideanSpace ℝ (Fin (d + 2))) :=
    cubeGridAffineApprox (k + 2) N (relativeSphereHomotopyToEuclidean H)
  have hGcont : Continuous fun sy : I × I^ Fin (k + 1) =>
      G (Fin.cons sy.1 sy.2) := G.continuous.comp (by fun_prop)
  have hGne : ∀ sy : I × I^ Fin (k + 1), G (Fin.cons sy.1 sy.2) ≠ 0 :=
    fun sy => hne (Fin.cons sy.1 sy.2)
  refine ⟨⟨⟨fun sy =>
      ⟨radialProj (G (Fin.cons sy.1 sy.2)),
        mem_sphere_zero_iff_norm.mpr
          (norm_radialProj (hGne sy))⟩,
      Continuous.subtype_mk
        (continuous_radialProj hGcont hGne) _⟩,
    fun _ => rfl, fun _ => rfl⟩, fun s => ?_⟩
  constructor
  · intro y hy
    exact (radialCubeGridAffineApproxRelativeSphereHomotopySlice
      N hN H hheight hjar hne s).property.1 y hy
  · intro y hy
    exact (radialCubeGridAffineApproxRelativeSphereHomotopySlice
      N hN H hheight hjar hne s).property.2 y hy

/-! ### The radial straight-line comparison on each time slice -/

/-- The straight-line comparison between a homotopy cube and its grid approximation preserves
nonnegative height on every spatial boundary face. -/
theorem cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonneg
    (hN : 1 ≤ N) (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (u s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApproxHomotopy (k + 2) N
      (relativeSphereHomotopyToEuclidean H) (u, Fin.cons s y)
        (Fin.last (d + 1)) := by
  rw [cubeGridAffineApproxHomotopy_apply]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ),
    map_add, map_smul, map_smul]
  simp only [PiLp.projₗ_apply, smul_eq_mul]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr u.2.2) (hheight s y hy))
    (mul_nonneg u.2.1
      (cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
        hN H hheight s hy))

/-- The straight-line comparison between a homotopy cube and its grid approximation fixes every
spatial jar face. -/
theorem cubeGridAffineApproxHomotopy_relativeSphereHomotopy_eq_on_boundaryJar
    (hN : 1 ≤ N) (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hjar : RelativeSphereHomotopy.JarBased H)
    (u s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeGridAffineApproxHomotopy (k + 2) N
      (relativeSphereHomotopyToEuclidean H) (u, Fin.cons s y) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := by
  rw [cubeGridAffineApproxHomotopy_apply,
    relativeSphereHomotopyToEuclidean_apply,
    show ((H (s, y) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) from congrArg Subtype.val (hjar s y hy),
    cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar hN H hjar s hy,
    ← add_smul]
  norm_num

/-- At each original homotopy time, radial projection of the straight-line grid comparison is a
relative homotopy from the original slice to the corresponding radial PL slice. -/
theorem relativeSphereHomotopySlice_homotopic_radialCubeGridAffineApprox
    (N : ℕ) (hN : 1 ≤ N)
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hne : ∀ y, cubeGridAffineApprox (k + 2) N
      (relativeSphereHomotopyToEuclidean H) y ≠ 0)
    (hHne : ∀ q, cubeGridAffineApproxHomotopy (k + 2) N
      (relativeSphereHomotopyToEuclidean H) q ≠ 0)
    (s : I) :
    RelGenLoop.Homotopic
      (relativeSphereHomotopySlice H hheight hjar s)
      (radialCubeGridAffineApproxRelativeSphereHomotopySlice
        N hN H hheight hjar hne s) := by
  let F := relativeSphereHomotopyToEuclidean H
  have hcont : Continuous fun uy : I × I^ Fin (k + 1) =>
      cubeGridAffineApproxHomotopy (k + 2) N F (uy.1, Fin.cons s uy.2) :=
    (cubeGridAffineApproxHomotopy (k + 2) N F).continuous.comp (by fun_prop)
  have hne' : ∀ uy : I × I^ Fin (k + 1),
      cubeGridAffineApproxHomotopy (k + 2) N F (uy.1, Fin.cons s uy.2) ≠ 0 :=
    fun uy => hHne (uy.1, Fin.cons s uy.2)
  refine ⟨⟨⟨fun uy =>
      ⟨radialProj (cubeGridAffineApproxHomotopy (k + 2) N F
          (uy.1, Fin.cons s uy.2)),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne' uy))⟩,
      Continuous.subtype_mk (continuous_radialProj hcont hne') _⟩,
    fun y => ?_, fun y => ?_⟩, fun u => ?_⟩
  · apply Subtype.ext
    change radialProj (cubeGridAffineApproxHomotopy (k + 2) N F
      (0, Fin.cons s y)) =
        ((H (s, y) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [cubeGridAffineApproxHomotopy_zero, relativeSphereHomotopyToEuclidean_apply]
    exact radialProj_of_norm_eq_one (norm_coe_sph (H (s, y)))
  · apply Subtype.ext
    change radialProj (cubeGridAffineApproxHomotopy (k + 2) N F
      (1, Fin.cons s y)) = radialProj (cubeGridAffineApprox (k + 2) N F
        (Fin.cons s y))
    rw [cubeGridAffineApproxHomotopy_one]
  · constructor
    · intro y hy
      rw [mem_sphUpperCap]
      change -(1 / 3 : ℝ) ≤ radialProj
        (cubeGridAffineApproxHomotopy (k + 2) N F (u, Fin.cons s y))
          (Fin.last (d + 1))
      exact le_trans (by norm_num)
        (radialProj_last_nonneg
          (cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonneg
            hN H hheight u s hy))
    · intro y hy
      apply Subtype.ext
      change radialProj (cubeGridAffineApproxHomotopy (k + 2) N F
        (u, Fin.cons s y)) =
          ((sphereBasepoint (d + 1) : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))
      rw [cubeGridAffineApproxHomotopy_relativeSphereHomotopy_eq_on_boundaryJar
        hN H hjar u s hy]
      exact radialProj_of_norm_eq_one
        (norm_coe_sph (sphereBasepoint (d + 1)))

/-! ### Finite PL approximation data for a cap-safe relative homotopy -/

/-- Simultaneous finite PL approximation data for every slice of a cap-safe, jar-relative
sphere homotopy. In particular, the two endpoint approximations are joined through relative
loops, and each approximated slice represents the same relative class as the original slice. -/
structure RelativeSpherePLHomotopyApproximation
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H) where
  mesh : ℕ
  mesh_pos : 1 ≤ mesh
  dist_le_half : ∀ y, dist
    (cubeGridAffineApprox (k + 2) mesh (relativeSphereHomotopyToEuclidean H) y)
    (relativeSphereHomotopyToEuclidean H y) ≤ 1 / 2
  approx_ne_zero : ∀ y,
    cubeGridAffineApprox (k + 2) mesh (relativeSphereHomotopyToEuclidean H) y ≠ 0
  comparison_ne_zero : ∀ q,
    cubeGridAffineApproxHomotopy (k + 2) mesh
      (relativeSphereHomotopyToEuclidean H) q ≠ 0
  slice_homotopic : ∀ s, RelGenLoop.Homotopic
    (relativeSphereHomotopySlice H hheight hjar s)
    (radialCubeGridAffineApproxRelativeSphereHomotopySlice
      mesh mesh_pos H hheight hjar approx_ne_zero s)
  approx_homotopic : RelGenLoop.Homotopic
    (radialCubeGridAffineApproxRelativeSphereHomotopySlice
      mesh mesh_pos H hheight hjar approx_ne_zero 0)
    (radialCubeGridAffineApproxRelativeSphereHomotopySlice
      mesh mesh_pos H hheight hjar approx_ne_zero 1)

/-- A cap-safe, jar-relative sphere homotopy admits one finite grid approximation valid
simultaneously for all times. Radial projection gives a relative homotopy between the endpoint
PL representatives. -/
theorem exists_relativeSpherePLHomotopyApproximation
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H) :
    Nonempty (RelativeSpherePLHomotopyApproximation H hheight hjar) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  let F := relativeSphereHomotopyToEuclidean H
  have hFnorm : ∀ y, ‖F y‖ = 1 := fun y =>
    norm_coe_sph (H (y 0, fun i => y i.succ))
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le (k + 2) F hhalf
  have hHdist : ∀ (u : I) (y : I^ Fin (k + 2)),
      dist (cubeGridAffineApproxHomotopy (k + 2) N F (u, y)) (F y) ≤ 1 / 2 :=
    fun u y => cubeGridAffineApproxHomotopy_dist_le F hdist u y
  have hHne : ∀ q : I × I^ Fin (k + 2),
      cubeGridAffineApproxHomotopy (k + 2) N F q ≠ 0 := by
    rintro ⟨u, y⟩ hzero
    have h := hHdist u y
    rw [hzero, dist_zero_left, hFnorm] at h
    linarith
  have hGne : ∀ y : I^ Fin (k + 2), cubeGridAffineApprox (k + 2) N F y ≠ 0 := by
    intro y
    have h := hHne (1, y)
    rwa [cubeGridAffineApproxHomotopy_one] at h
  exact ⟨⟨N, hN, hdist, hGne, hHne,
    fun s => relativeSphereHomotopySlice_homotopic_radialCubeGridAffineApprox
      N hN H hheight hjar hGne hHne s,
    radialCubeGridAffineApproxRelativeSphereHomotopy_homotopic
      N hN H hheight hjar hGne⟩⟩

/-! ### Removing the strict-cap hypothesis -/

/-- Postcompose a relative sphere homotopy with the upper-cap squeeze. This keeps the endpoints
equal to the squeezed endpoint loops and remains a homotopy through relative loops. -/
noncomputable def upperCapSqueezeRelativeSphereHomotopy
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    ContinuousMap.HomotopyWith
      (upperCapSqueezeRelGenLoop p).val (upperCapSqueezeRelGenLoop q).val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)) := by
  refine ⟨⟨⟨fun sy => upperCapSqueezeSphere d (H sy), by fun_prop⟩,
    fun y => ?_, fun y => ?_⟩, fun s => ?_⟩
  · change upperCapSqueezeSphere d (H (0, y)) = upperCapSqueezeSphere d (p.val y)
    exact congrArg (upperCapSqueezeSphere d) (H.toHomotopy.apply_zero y)
  · change upperCapSqueezeSphere d (H (1, y)) = upperCapSqueezeSphere d (q.val y)
    exact congrArg (upperCapSqueezeSphere d) (H.toHomotopy.apply_one y)
  · constructor
    · intro y hy
      have hnonneg := upperCapSqueezeSphere_boundaryHeightNonneg
        ((H.prop s).1 y hy)
      rw [mem_sphUpperCap]
      exact le_trans (by norm_num) hnonneg
    · intro y hy
      change upperCapSqueezeSphere d (H (s, y)) =
        (sphUpperCapBase d : Sph (d + 1))
      have hbase := (H.prop s).2 y hy
      change H (s, y) = (sphUpperCapBase d : Sph (d + 1)) at hbase
      rw [hbase]
      exact upperCapSqueezeSphere_base d

/-- The underlying sphere-valued map of a squeezed relative homotopy. -/
noncomputable def upperCapSqueezeRelativeSphereHomotopyMap
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    C(I × I^ Fin (k + 1), Sph (d + 1)) :=
  (upperCapSqueezeRelativeSphereHomotopy H).toHomotopy.toContinuousMap

@[simp] theorem upperCapSqueezeRelativeSphereHomotopyMap_apply
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (s : I) (y : I^ Fin (k + 1)) :
    upperCapSqueezeRelativeSphereHomotopyMap H (s, y) =
      upperCapSqueezeSphere d (H (s, y)) :=
  rfl

theorem upperCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    RelativeSphereHomotopy.BoundaryHeightNonneg
      (upperCapSqueezeRelativeSphereHomotopyMap H) := by
  intro s y hy
  exact upperCapSqueezeSphere_boundaryHeightNonneg ((H.prop s).1 y hy)

theorem upperCapSqueezeRelativeSphereHomotopy_jarBased
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    RelativeSphereHomotopy.JarBased
      (upperCapSqueezeRelativeSphereHomotopyMap H) := by
  intro s y hy
  have hbase := (H.prop s).2 y hy
  change H (s, y) = (sphUpperCapBase d : Sph (d + 1)) at hbase
  rw [upperCapSqueezeRelativeSphereHomotopyMap_apply, hbase]
  exact upperCapSqueezeSphere_base d

theorem relativeSphereHomotopySlice_upperCapSqueeze_zero
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg
      (upperCapSqueezeRelativeSphereHomotopyMap H))
    (hjar : RelativeSphereHomotopy.JarBased
      (upperCapSqueezeRelativeSphereHomotopyMap H)) :
    relativeSphereHomotopySlice
      (upperCapSqueezeRelativeSphereHomotopyMap H) hheight hjar 0 =
      upperCapSqueezeRelGenLoop p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change upperCapSqueezeSphere d (H (0, y)) = upperCapSqueezeSphere d (p.val y)
  exact congrArg (upperCapSqueezeSphere d) (H.toHomotopy.apply_zero y)

theorem relativeSphereHomotopySlice_upperCapSqueeze_one
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (H : ContinuousMap.HomotopyWith p.val q.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg
      (upperCapSqueezeRelativeSphereHomotopyMap H))
    (hjar : RelativeSphereHomotopy.JarBased
      (upperCapSqueezeRelativeSphereHomotopyMap H)) :
    relativeSphereHomotopySlice
      (upperCapSqueezeRelativeSphereHomotopyMap H) hheight hjar 1 =
      upperCapSqueezeRelGenLoop q := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change upperCapSqueezeSphere d (H (1, y)) = upperCapSqueezeSphere d (q.val y)
  exact congrArg (upperCapSqueezeSphere d) (H.toHomotopy.apply_one y)

namespace RelativeSpherePLHomotopyApproximation

/-- The radial PL relative loop at time `s` represented by simultaneous approximation data. -/
noncomputable def approxSlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar) (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialCubeGridAffineApproxRelativeSphereHomotopySlice
    A.mesh A.mesh_pos H hheight hjar A.approx_ne_zero s

theorem originalSlice_homotopic_approxSlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar) (s : I) :
    RelGenLoop.Homotopic (relativeSphereHomotopySlice H hheight hjar s)
      (A.approxSlice s) :=
  A.slice_homotopic s

theorem approxSlice_zero_homotopic_one
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar) :
    RelGenLoop.Homotopic (A.approxSlice 0) (A.approxSlice 1) :=
  A.approx_homotopic

end RelativeSpherePLHomotopyApproximation

/-- Any relative homotopy of sphere/upper-cap loops can be squeezed and approximated by one
finite PL homotopy cube. Its endpoint PL slices remain in the original endpoint classes. -/
theorem exists_relativeSpherePLHomotopyRepresentatives_of_homotopic
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (hpq : RelGenLoop.Homotopic p q) :
    ∃ (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
      (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
      (hjar : RelativeSphereHomotopy.JarBased H)
      (A : RelativeSpherePLHomotopyApproximation H hheight hjar),
      RelGenLoop.Homotopic p (A.approxSlice 0) ∧
        RelGenLoop.Homotopic q (A.approxSlice 1) := by
  rcases hpq with ⟨H₀⟩
  let H := upperCapSqueezeRelativeSphereHomotopyMap H₀
  let hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H :=
    upperCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg H₀
  let hjar : RelativeSphereHomotopy.JarBased H :=
    upperCapSqueezeRelativeSphereHomotopy_jarBased H₀
  obtain ⟨A⟩ := exists_relativeSpherePLHomotopyApproximation H hheight hjar
  have hzero := A.originalSlice_homotopic_approxSlice 0
  have hone := A.originalSlice_homotopic_approxSlice 1
  have hszero : relativeSphereHomotopySlice H hheight hjar 0 =
      upperCapSqueezeRelGenLoop p := by
    exact relativeSphereHomotopySlice_upperCapSqueeze_zero H₀ hheight hjar
  have hsone : relativeSphereHomotopySlice H hheight hjar 1 =
      upperCapSqueezeRelGenLoop q := by
    exact relativeSphereHomotopySlice_upperCapSqueeze_one H₀ hheight hjar
  rw [hszero] at hzero
  rw [hsone] at hone
  exact ⟨H, hheight, hjar, A,
    (relGenLoopHomotopic_upperCapSqueeze p).trans hzero,
    (relGenLoopHomotopic_upperCapSqueeze q).trans hone⟩

end Submission
