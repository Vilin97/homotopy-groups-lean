/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Grid
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Piecewise-affine approximation on the cube

Given a continuous map `g : C(I^ Fin n, E)` into a real normed space `E`, we define
`Submission.cubeGridAffineApprox n N g`, the map obtained by interpolating the values of `g` at
the vertices of the `N`-fold grid on the cube affinely on each simplex of the Kuhn
(Freudenthal) triangulation.

Because the barycentric coordinates of the Kuhn triangulation are given globally by the closed
formula of `Submission/Approximation/Grid.lean`, the definition is a single finite sum of
continuous functions; no gluing argument is needed, and continuity is immediate.

## Main definitions

* `Submission.gridVertex` — the grid point `v / N` as a point of the cube;
* `Submission.cubeGridAffineApprox` — the piecewise-affine approximation.

## Main results

* `Submission.cubeGridAffineApprox_gridVertex` — the approximation agrees with `g` at every
  grid vertex;
* `Submission.dist_gridVertex_le_of_gridCoeff_pos` — a vertex contributing to the value at `y`
  is at sup-distance at most `1 / N` from `y`.
-/

open scoped unitInterval Topology

namespace Submission

variable {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The grid point `v / N`, as a point of the cube `I^ Fin n`.  The coordinates are clamped to
`[0,1]`, so the definition makes sense for every `v`; for `v ∈ gridVerts n N` and `1 ≤ N` no
clamping occurs (`coe_gridVertex`). -/
noncomputable def gridVertex (N : ℕ) (v : Fin n → ℕ) : I^ Fin n :=
  fun j => Set.projIcc (0 : ℝ) 1 zero_le_one ((v j : ℝ) / N)

theorem coe_gridVertex (hN : 1 ≤ N) {v : Fin n → ℕ} (hv : v ∈ gridVerts n N) (j : Fin n) :
    ((gridVertex N v j : ℝ)) = (v j : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : ((v j : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN']
    exact_mod_cast mem_gridVerts.mp hv j
  rw [gridVertex, Set.projIcc_of_mem _ hmem]

/-- The coordinate function of the cube, as a map to `Fin n → ℝ`. -/
private theorem continuous_cubeCoe :
    Continuous fun y : I^ Fin n => (fun j => (y j : ℝ)) :=
  continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)

/-- The piecewise-affine approximation of `g` on the `N`-fold grid triangulation of the cube:
the affine interpolation, on each simplex of the Kuhn triangulation, of the values of `g` at the
grid vertices. -/
noncomputable def cubeGridAffineApprox (n N : ℕ) (g : C(I^ Fin n, E)) : C(I^ Fin n, E) where
  toFun y := ∑ v ∈ gridVerts n N, gridCoeff N v (fun j => (y j : ℝ)) • g (gridVertex N v)
  continuous_toFun :=
    continuous_finsetSum _ fun v _ =>
      (((continuous_gridCoeff N v).comp continuous_cubeCoe).smul continuous_const)

theorem cubeGridAffineApprox_apply (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y =
      ∑ v ∈ gridVerts n N, gridCoeff N v (fun j => (y j : ℝ)) • g (gridVertex N v) :=
  rfl

/-- Points of the cube have coordinates in `[0,1]`; this is the form in which the results of
`Submission/Approximation/Grid.lean` are applied. -/
theorem cubeCoe_mem_Icc (y : I^ Fin n) (j : Fin n) : (y j : ℝ) ∈ Set.Icc (0 : ℝ) 1 := (y j).2

/-- The barycentric coordinates at a point of the cube sum to `1`. -/
theorem sum_gridCoeff_cube (hN : 1 ≤ N) (y : I^ Fin n) :
    ∑ v ∈ gridVerts n N, gridCoeff N v (fun j => (y j : ℝ)) = 1 :=
  sum_gridCoeff hN (cubeCoe_mem_Icc y)

/-- The approximation agrees with `g` at every vertex of the grid. -/
theorem cubeGridAffineApprox_gridVertex (hN : 1 ≤ N) (g : C(I^ Fin n, E)) {w : Fin n → ℕ}
    (hw : w ∈ gridVerts n N) :
    cubeGridAffineApprox n N g (gridVertex N w) = g (gridVertex N w) := by
  have hcoe : (fun j => ((gridVertex N w j : ℝ))) = fun j => (w j : ℝ) / N :=
    funext (coe_gridVertex hN hw)
  rw [cubeGridAffineApprox_apply, hcoe]
  rw [Finset.sum_eq_single w]
  · rw [gridCoeff_grid_point hN, if_pos rfl, one_smul]
  · intro v _ hv
    rw [gridCoeff_grid_point hN, if_neg hv, zero_smul]
  · intro h; exact absurd hw h

/-- A grid vertex whose barycentric coordinate at `y` is nonzero lies at sup-distance at most
`1 / N` from `y`. -/
theorem dist_gridVertex_le_of_gridCoeff_pos (hN : 1 ≤ N) {v : Fin n → ℕ} {y : I^ Fin n}
    (h : 0 < gridCoeff N v (fun j => (y j : ℝ))) : dist (gridVertex N v) y ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : v ∈ gridVerts n N := mem_gridVerts_of_gridCoeff_pos (cubeCoe_mem_Icc y) h
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  rw [Subtype.dist_eq, Real.dist_eq, coe_gridVertex hN hv]
  have hrw : (v j : ℝ) / N - (y j : ℝ) = -(((N : ℝ) * (y j : ℝ) - (v j : ℝ)) / N) := by
    field_simp
    ring
  rw [hrw, abs_neg, abs_div, abs_of_pos hN', div_le_div_iff_of_pos_right hN']
  exact (abs_sub_lt_one_of_gridCoeff_pos h j).le

end Submission
