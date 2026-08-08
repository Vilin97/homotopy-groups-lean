/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Approx
import Mathlib.Analysis.Convex.Combination

/-!
# The approximation estimate and the straight-line homotopy

`Submission.cubeGridAffineApprox n N g y` is a convex combination of values of `g` at grid
vertices within sup-distance `1 / N` of `y`.  Consequently it stays within any modulus of
continuity of `g` at scale `1 / N` (`Submission.cubeGridAffineApprox_dist_le`), and it stays
inside any convex set containing those values (`Submission.cubeGridAffineApprox_mem_of_convex`).

Combining with uniform continuity of `g` on the compact cube gives
`Submission.exists_cubeGridAffineApprox_dist_le`: for every `δ > 0` some `N` works.

Finally the straight-line homotopy from `g` to the approximation is recorded, together with the
fact that it stays within `δ` of `g` and inside a convex set containing the relevant values of
`g`.
-/

open scoped unitInterval Topology

namespace Submission

variable {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The value is a convex combination of nearby values of `g` -/

/-- The grid vertices that actually contribute to the value of the approximation at `y`. -/
noncomputable def activeVerts (N : ℕ) (y : I^ Fin n) : Finset (Fin n → ℕ) :=
  (gridVerts n N).filter fun v => 0 < gridCoeff N v fun j => (y j : ℝ)

theorem mem_activeVerts {N : ℕ} {y : I^ Fin n} {v : Fin n → ℕ} :
    v ∈ activeVerts N y ↔ v ∈ gridVerts n N ∧ 0 < gridCoeff N v fun j => (y j : ℝ) := by
  simp [activeVerts]

theorem sum_gridCoeff_activeVerts (hN : 1 ≤ N) (y : I^ Fin n) :
    ∑ v ∈ activeVerts N y, gridCoeff N v (fun j => (y j : ℝ)) = 1 := by
  rw [activeVerts, Finset.sum_filter_of_ne fun v _ hv => lt_of_le_of_ne gridCoeff_nonneg
    (Ne.symm hv)]
  exact sum_gridCoeff_cube hN y

theorem cubeGridAffineApprox_eq_sum_activeVerts (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y =
      ∑ v ∈ activeVerts N y, gridCoeff N v (fun j => (y j : ℝ)) • g (gridVertex N v) := by
  rw [cubeGridAffineApprox_apply, activeVerts,
    Finset.sum_filter_of_ne fun v _ hv => lt_of_le_of_ne gridCoeff_nonneg
      (Ne.symm fun h => hv (by rw [h, zero_smul]))]

/-- The value of the approximation at `y` lies in any convex set containing the values of `g`
at all points of the cube within sup-distance `1 / N` of `y`. -/
theorem cubeGridAffineApprox_mem_of_convex (hN : 1 ≤ N) (g : C(I^ Fin n, E)) {C : Set E}
    (hC : Convex ℝ C) (y : I^ Fin n) (hg : ∀ z : I^ Fin n, dist z y ≤ 1 / N → g z ∈ C) :
    cubeGridAffineApprox n N g y ∈ C := by
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  refine hC.sum_mem (fun v _ => gridCoeff_nonneg) (sum_gridCoeff_activeVerts hN y) ?_
  intro v hv
  exact hg _ (dist_gridVertex_le_of_gridCoeff_pos hN (mem_activeVerts.mp hv).2)

/-- The value of the approximation lies in any convex set containing the whole image of `g`. -/
theorem cubeGridAffineApprox_mem_of_convex_of_range (hN : 1 ≤ N) (g : C(I^ Fin n, E)) {C : Set E}
    (hC : Convex ℝ C) (hg : ∀ z : I^ Fin n, g z ∈ C) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y ∈ C :=
  cubeGridAffineApprox_mem_of_convex hN g hC y fun z _ => hg z

/-! ### The approximation estimate -/

/-- **The approximation estimate.**  If `g` moves by at most `δ` on pairs of points at
sup-distance at most `1 / N`, then the piecewise-affine approximation on the `N`-fold grid stays
within `δ` of `g`. -/
theorem cubeGridAffineApprox_dist_le (n N : ℕ) (hN : 1 ≤ N) (g : C(I^ Fin n, E)) (δ : ℝ)
    (hδ : ∀ y z : I^ Fin n, dist y z ≤ 1 / N → dist (g y) (g z) ≤ δ) :
    ∀ y, dist (cubeGridAffineApprox n N g y) (g y) ≤ δ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro y
  have hδ0 : 0 ≤ δ := le_trans dist_nonneg (hδ y y (by simp))
  have hsum := sum_gridCoeff_cube (n := n) hN y
  have key : ∑ v ∈ gridVerts n N,
      gridCoeff N v (fun j => (y j : ℝ)) • (g (gridVertex N v) - g y)
      = cubeGridAffineApprox n N g y - g y := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul,
      cubeGridAffineApprox_apply]
  rw [dist_eq_norm, ← key]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ v ∈ gridVerts n N, ‖gridCoeff N v (fun j => (y j : ℝ)) • (g (gridVertex N v) - g y)‖
      ≤ ∑ v ∈ gridVerts n N, gridCoeff N v (fun j => (y j : ℝ)) * δ := by
        refine Finset.sum_le_sum fun v _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg gridCoeff_nonneg]
        rcases eq_or_lt_of_le (gridCoeff_nonneg (N := N) (v := v) (y := fun j => (y j : ℝ)))
          with h | h
        · rw [← h]; simp
        · refine mul_le_mul_of_nonneg_left ?_ h.le
          rw [← dist_eq_norm]
          exact hδ _ _ (dist_gridVertex_le_of_gridCoeff_pos hN h)
    _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- For every `δ > 0` there is a grid fine enough that the piecewise-affine approximation stays
within `δ` of `g`. -/
theorem exists_cubeGridAffineApprox_dist_le (n : ℕ) (g : C(I^ Fin n, E)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ y, dist (cubeGridAffineApprox n N g y) (g y) ≤ δ := by
  have huc : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous g.continuous
  obtain ⟨ε, hε, hgε⟩ := Metric.uniformContinuous_iff.mp huc δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  refine ⟨m + 1, by omega, cubeGridAffineApprox_dist_le n (m + 1) (by omega) g δ ?_⟩
  intro y z hyz
  refine le_of_lt (hgε (lt_of_le_of_lt hyz ?_))
  push_cast
  exact hm

/-! ### The straight-line homotopy -/

/-- The straight-line homotopy `(1 - t) • g + t • (cubeGridAffineApprox n N g)` from `g` to its
piecewise-affine approximation. -/
noncomputable def cubeGridAffineApproxHomotopy (n N : ℕ) (g : C(I^ Fin n, E)) :
    C(I × I^ Fin n, E) where
  toFun p := (1 - (p.1 : ℝ)) • g p.2 + (p.1 : ℝ) • cubeGridAffineApprox n N g p.2
  continuous_toFun := by
    have hc : Continuous fun p : I × I^ Fin n => ((p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub hc).smul (g.continuous.comp continuous_snd)).add
      (hc.smul ((cubeGridAffineApprox n N g).continuous.comp continuous_snd))

@[simp] theorem cubeGridAffineApproxHomotopy_apply (g : C(I^ Fin n, E)) (t : I) (y : I^ Fin n) :
    cubeGridAffineApproxHomotopy n N g (t, y) =
      (1 - (t : ℝ)) • g y + (t : ℝ) • cubeGridAffineApprox n N g y := rfl

@[simp] theorem cubeGridAffineApproxHomotopy_zero (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApproxHomotopy n N g (0, y) = g y := by
  simp [cubeGridAffineApproxHomotopy]

@[simp] theorem cubeGridAffineApproxHomotopy_one (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApproxHomotopy n N g (1, y) = cubeGridAffineApprox n N g y := by
  simp [cubeGridAffineApproxHomotopy]

/-- Every value of the straight-line homotopy at `y` lies on the segment from `g y` to the
approximation at `y`. -/
theorem cubeGridAffineApproxHomotopy_mem_segment (g : C(I^ Fin n, E)) (t : I) (y : I^ Fin n) :
    cubeGridAffineApproxHomotopy n N g (t, y) ∈
      segment ℝ (g y) (cubeGridAffineApprox n N g y) :=
  ⟨1 - (t : ℝ), (t : ℝ), by simpa using (unitInterval.le_one t), t.2.1, by ring, rfl⟩

/-- The straight-line homotopy stays inside any convex set containing the values of `g` at all
points of the cube within sup-distance `1 / N` of `y`. -/
theorem cubeGridAffineApproxHomotopy_mem_of_convex (hN : 1 ≤ N) (g : C(I^ Fin n, E)) {C : Set E}
    (hC : Convex ℝ C) (t : I) (y : I^ Fin n)
    (hg : ∀ z : I^ Fin n, dist z y ≤ 1 / N → g z ∈ C) (hgy : g y ∈ C) :
    cubeGridAffineApproxHomotopy n N g (t, y) ∈ C :=
  hC.segment_subset hgy (cubeGridAffineApprox_mem_of_convex hN g hC y hg)
    (cubeGridAffineApproxHomotopy_mem_segment g t y)

/-- The straight-line homotopy stays within `δ` of `g` whenever the approximation does. -/
theorem cubeGridAffineApproxHomotopy_dist_le (g : C(I^ Fin n, E)) {δ : ℝ}
    (hδ : ∀ y, dist (cubeGridAffineApprox n N g y) (g y) ≤ δ) (t : I) (y : I^ Fin n) :
    dist (cubeGridAffineApproxHomotopy n N g (t, y)) (g y) ≤ δ := by
  have ht := t.2
  rw [cubeGridAffineApproxHomotopy_apply, dist_eq_norm]
  have hrw : (1 - (t : ℝ)) • g y + (t : ℝ) • cubeGridAffineApprox n N g y - g y
      = (t : ℝ) • (cubeGridAffineApprox n N g y - g y) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc (t : ℝ) * ‖cubeGridAffineApprox n N g y - g y‖
      ≤ 1 * ‖cubeGridAffineApprox n N g y - g y‖ :=
        mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ = dist (cubeGridAffineApprox n N g y) (g y) := by rw [one_mul, dist_eq_norm]
    _ ≤ δ := hδ y

end Submission
