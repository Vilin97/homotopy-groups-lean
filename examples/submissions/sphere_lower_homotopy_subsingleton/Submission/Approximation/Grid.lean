/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Barycentric coordinates of the Kuhn grid triangulation of a cube

Fix `n N : ℕ`.  Subdividing the cube `[0,1]^(Fin n)` into `N^n` small cubes and each small cube
into `n!` simplices by the *Kuhn* (or *Freudenthal*) rule "order the fractional parts of the
coordinates" produces a triangulation whose vertices are exactly the grid points `v / N` with
`v : Fin n → ℕ`, `v j ≤ N`.

The barycentric coordinate of the grid point `v / N` at a point `y` of the cube admits the
following closed formula, which is the *layer cake* description of the Kuhn triangulation: for
`t ∈ [0,1)` the vector `j ↦ ⌈N * y j - t⌉` runs through the vertices of the Kuhn simplex
containing `y`, and the barycentric coordinate of a vertex `v` is the length of the set of
parameters `t` producing it.  That set is the interval `[gridLo N v y, gridHi N v y)` and its
length is `gridCoeff N v y`.

Defining the interpolation by this formula rather than piecewise on each simplex makes
continuity *obvious* (the coefficients are built from `min`, `max` and affine functions), which
is why we take it as the definition.  That the pieces really are the Kuhn simplices, i.e. that
the resulting function is affine on each of them, is proved in `Submission/Approximation/
Simplex.lean`.

## Main definitions

* `Submission.gridLo`, `Submission.gridHi` — the endpoints of the parameter interval;
* `Submission.gridCoeff` — the barycentric coordinate of the grid vertex `v` at `y`;
* `Submission.gridVerts` — the finite index set of grid vertices.

## Main results

* `Submission.gridCoeff_nonneg` — the coefficients are nonnegative;
* `Submission.sum_gridCoeff` — they sum to `1` on the cube;
* `Submission.abs_sub_lt_one_of_gridCoeff_pos` — a vertex with a nonzero coefficient is at
  sup-distance `< 1 / N` from `y`;
* `Submission.gridCoeff_grid_point` — the coefficients at a grid point are the Kronecker delta;
* `Submission.continuous_gridCoeff` — continuity.
-/

namespace Submission

open scoped unitInterval

variable {n N : ℕ} {v w : Fin n → ℕ} {y : Fin n → ℝ}

/-! ### The parameter interval of a grid vertex -/

/-- The left endpoint of the parameter interval attached to the grid vertex `v` at the point `y`
of the cube: `max (0, maxⱼ (N * y j - v j))`. -/
noncomputable def gridLo (N : ℕ) (v : Fin n → ℕ) (y : Fin n → ℝ) : ℝ :=
  Finset.univ.fold max (0 : ℝ) fun j => (N : ℝ) * y j - v j

/-- The right endpoint of the parameter interval attached to the grid vertex `v` at the point `y`
of the cube: `min (1, minⱼ (N * y j - v j + 1))`. -/
noncomputable def gridHi (N : ℕ) (v : Fin n → ℕ) (y : Fin n → ℝ) : ℝ :=
  Finset.univ.fold min (1 : ℝ) fun j => (N : ℝ) * y j - v j + 1

/-- The barycentric coordinate of the grid vertex `v / N` at the point `y` of the cube: the
length of the interval `[gridLo N v y, gridHi N v y)`. -/
noncomputable def gridCoeff (N : ℕ) (v : Fin n → ℕ) (y : Fin n → ℝ) : ℝ :=
  max 0 (gridHi N v y - gridLo N v y)

theorem gridLo_le_iff (c : ℝ) :
    gridLo N v y ≤ c ↔ 0 ≤ c ∧ ∀ j, (N : ℝ) * y j - v j ≤ c := by
  simp [gridLo, Finset.fold_max_le]

theorem lt_gridHi_iff (c : ℝ) :
    c < gridHi N v y ↔ c < 1 ∧ ∀ j, c < (N : ℝ) * y j - v j + 1 := by
  simp [gridHi, Finset.lt_fold_min]

theorem le_gridHi_iff (c : ℝ) :
    c ≤ gridHi N v y ↔ c ≤ 1 ∧ ∀ j, c ≤ (N : ℝ) * y j - v j + 1 := by
  simp [gridHi, Finset.le_fold_min]

theorem gridLo_nonneg : 0 ≤ gridLo N v y := by
  simp [gridLo, Finset.le_fold_max]

theorem gridHi_le_one : gridHi N v y ≤ 1 := by
  simp [gridHi, Finset.fold_min_le]

theorem le_gridLo (j : Fin n) : (N : ℝ) * y j - v j ≤ gridLo N v y :=
  (gridLo_le_iff _).mp le_rfl |>.2 j

theorem gridHi_le (j : Fin n) : gridHi N v y ≤ (N : ℝ) * y j - v j + 1 :=
  not_lt.mp fun h => absurd ((lt_gridHi_iff _).mp h |>.2 j) (lt_irrefl _)

/-! ### Elementary properties of the coefficients -/

theorem gridCoeff_nonneg : 0 ≤ gridCoeff N v y := le_max_left _ _

theorem gridCoeff_eq_zero (h : gridHi N v y ≤ gridLo N v y) : gridCoeff N v y = 0 :=
  max_eq_left (by linarith)

theorem gridLo_lt_gridHi_of_pos (h : 0 < gridCoeff N v y) : gridLo N v y < gridHi N v y := by
  by_contra hc
  exact absurd (gridCoeff_eq_zero (not_lt.mp hc)) h.ne'

theorem gridCoeff_pos_iff : 0 < gridCoeff N v y ↔ gridLo N v y < gridHi N v y := by
  constructor
  · exact gridLo_lt_gridHi_of_pos
  · intro h; exact lt_max_of_lt_right (by linarith)

/-- A grid vertex with a nonzero barycentric coordinate at `y` differs from `N • y` by less than
one in every coordinate.  Equivalently, it is at sup-distance `< 1 / N` from `y`. -/
theorem abs_sub_lt_one_of_gridCoeff_pos (h : 0 < gridCoeff N v y) (j : Fin n) :
    |(N : ℝ) * y j - v j| < 1 := by
  have hlt := gridLo_lt_gridHi_of_pos h
  have h₁ : (N : ℝ) * y j - v j ≤ gridLo N v y := le_gridLo j
  have h₂ : gridHi N v y ≤ (N : ℝ) * y j - v j + 1 := gridHi_le j
  have h₃ : (0 : ℝ) ≤ gridLo N v y := gridLo_nonneg
  have h₄ : gridHi N v y ≤ 1 := gridHi_le_one
  rw [abs_lt]
  constructor <;> linarith

/-! ### The interval description and the partition of `[0,1)` -/

theorem mem_Ico_gridLo_gridHi_iff (t : ℝ) :
    t ∈ Set.Ico (gridLo N v y) (gridHi N v y) ↔
      t ∈ Set.Ico (0 : ℝ) 1 ∧ ∀ j, (v j : ℝ) - 1 < (N : ℝ) * y j - t ∧ (N : ℝ) * y j - t ≤ v j := by
  simp only [Set.mem_Ico, gridLo_le_iff, lt_gridHi_iff]
  constructor
  · rintro ⟨⟨h0, hj⟩, ⟨h1, hj'⟩⟩
    exact ⟨⟨h0, h1⟩, fun j => ⟨by have := hj' j; linarith, by have := hj j; linarith⟩⟩
  · rintro ⟨⟨h0, h1⟩, hj⟩
    exact ⟨⟨h0, fun j => by have := (hj j).2; linarith⟩,
      ⟨h1, fun j => by have := (hj j).1; linarith⟩⟩

/-- If the barycentric coordinate of `v` at `y` is positive, then the left endpoint of its
parameter interval belongs to it, and hence witnesses `v` as the vector of ceilings. -/
theorem gridLo_spec_of_pos (h : 0 < gridCoeff N v y) :
    gridLo N v y ∈ Set.Ico (0 : ℝ) 1 ∧
      ∀ j, (v j : ℝ) - 1 < (N : ℝ) * y j - gridLo N v y ∧
        (N : ℝ) * y j - gridLo N v y ≤ v j :=
  (mem_Ico_gridLo_gridHi_iff _).mp ⟨le_rfl, gridLo_lt_gridHi_of_pos h⟩

/-- **The grid vertices with a positive barycentric coordinate at `y` are totally ordered.**
If `v` and `w` both contribute at `y` and the parameter interval of `v` starts no later than
that of `w`, then `v` dominates `w` coordinatewise, and by at most one unit.

This is the combinatorial heart of the Kuhn triangulation: the contributing vertices are the
vertices of a single small simplex, so they form a chain `k, k + e_{σ 0}, k + e_{σ 0} + e_{σ 1},
…`. -/
theorem le_of_gridCoeff_pos_of_gridLo_le {w : Fin n → ℕ} (hv : 0 < gridCoeff N v y)
    (hw : 0 < gridCoeff N w y) (hle : gridLo N v y ≤ gridLo N w y) (j : Fin n) :
    w j ≤ v j ∧ v j ≤ w j + 1 := by
  obtain ⟨hv0, hvj⟩ := gridLo_spec_of_pos hv
  obtain ⟨hw0, hwj⟩ := gridLo_spec_of_pos hw
  constructor
  · have h : (w j : ℝ) < (v j : ℝ) + 1 := by
      have h1 := (hwj j).1
      have h2 := (hvj j).2
      linarith
    have : w j < v j + 1 := by exact_mod_cast h
    omega
  · have h : (v j : ℝ) < (w j : ℝ) + 2 := by
      have h1 := (hvj j).1
      have h2 := (hwj j).2
      have h3 := hv0.1
      have h4 := hw0.2
      linarith
    have : v j < w j + 2 := by exact_mod_cast h
    omega

/-- The finite index set of vertices of the `N`-fold grid on the `n`-cube. -/
def gridVerts (n N : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (N + 1)

@[simp] theorem mem_gridVerts : v ∈ gridVerts n N ↔ ∀ j, v j ≤ N := by
  simp [gridVerts]

/-- The parameter intervals of distinct grid vertices are disjoint. -/
theorem gridLo_gridHi_pairwiseDisjoint :
    (Set.univ : Set (Fin n → ℕ)).PairwiseDisjoint
      fun v => Set.Ico (gridLo N v y) (gridHi N v y) := by
  intro v _ w _ hvw
  refine Set.disjoint_left.mpr fun t htv htw => hvw (funext fun j => ?_)
  obtain ⟨-, hv⟩ := (mem_Ico_gridLo_gridHi_iff t).mp htv
  obtain ⟨-, hw⟩ := (mem_Ico_gridLo_gridHi_iff t).mp htw
  have h₁ : (v j : ℝ) < (w j : ℝ) + 1 := by have := (hv j).1; have := (hw j).2; linarith
  have h₂ : (w j : ℝ) < (v j : ℝ) + 1 := by have := (hw j).1; have := (hv j).2; linarith
  have h₁' : v j < w j + 1 := by exact_mod_cast h₁
  have h₂' : w j < v j + 1 := by exact_mod_cast h₂
  omega

/-- Only genuine grid vertices carry a nonzero barycentric coordinate. -/
theorem mem_gridVerts_of_gridCoeff_pos (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (h : 0 < gridCoeff N v y) : v ∈ gridVerts n N := by
  refine mem_gridVerts.mpr fun j => ?_
  have habs := abs_lt.mp (abs_sub_lt_one_of_gridCoeff_pos h j)
  have hyj : y j ≤ 1 := (hy j).2
  have hNy : (N : ℝ) * y j ≤ (N : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have : (v j : ℝ) < (N : ℝ) + 1 := by linarith [habs.2]
  have : v j < N + 1 := by exact_mod_cast this
  omega

/-- On the cube, the parameter intervals of the grid vertices partition `[0,1)`. -/
theorem iUnion_Ico_gridLo_gridHi (hN : 1 ≤ N) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    ⋃ v ∈ gridVerts n N, Set.Ico (gridLo N v y) (gridHi N v y) = Set.Ico (0 : ℝ) 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Ico, exists_prop]
  constructor
  · rintro ⟨v, -, ht⟩
    exact ((mem_Ico_gridLo_gridHi_iff t).mp ht).1
  · rintro ⟨ht0, ht1⟩
    refine ⟨fun j => ⌈(N : ℝ) * y j - t⌉.toNat, mem_gridVerts.mpr fun j => ?_, ?_⟩
    · have hyj : y j ≤ 1 := (hy j).2
      have : (N : ℝ) * y j - t ≤ (N : ℤ) := by
        have : (N : ℝ) * y j ≤ (N : ℝ) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) N]
        push_cast
        linarith
      have hc : ⌈(N : ℝ) * y j - t⌉ ≤ (N : ℤ) := Int.ceil_le.mpr (by exact_mod_cast this)
      omega
    · refine (mem_Ico_gridLo_gridHi_iff t).mpr ⟨⟨ht0, ht1⟩, fun j => ?_⟩
      have hnn : (0 : ℤ) ≤ ⌈(N : ℝ) * y j - t⌉ := by
        have hyj : 0 ≤ y j := (hy j).1
        have hmul : (0 : ℝ) ≤ (N : ℝ) * y j := by positivity
        have hlt : ((-1 : ℤ) : ℝ) < (N : ℝ) * y j - t := by push_cast; linarith
        have := Int.lt_ceil.mpr hlt
        omega
      have hcast : ((⌈(N : ℝ) * y j - t⌉.toNat : ℕ) : ℝ) = (⌈(N : ℝ) * y j - t⌉ : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
      rw [hcast]
      exact ⟨by have := Int.ceil_lt_add_one ((N : ℝ) * y j - t); linarith,
        Int.le_ceil _⟩

/-- The barycentric coordinates of a point of the cube sum to `1`. -/
theorem sum_gridCoeff (hN : 1 ≤ N) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ v ∈ gridVerts n N, gridCoeff N v y = 1 := by
  classical
  have hmeas : ∀ v ∈ gridVerts n N,
      MeasurableSet (Set.Ico (gridLo N v y) (gridHi N v y)) := fun _ _ => measurableSet_Ico
  have hdisj : (↑(gridVerts n N) : Set (Fin n → ℕ)).PairwiseDisjoint
      fun v => Set.Ico (gridLo N v y) (gridHi N v y) :=
    gridLo_gridHi_pairwiseDisjoint.subset (Set.subset_univ _)
  have key := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hdisj hmeas
  rw [iUnion_Ico_gridLo_gridHi hN hy] at key
  simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one] at key
  have hstep : ∀ v : Fin n → ℕ,
      ENNReal.ofReal (gridHi N v y - gridLo N v y) = ENNReal.ofReal (gridCoeff N v y) := by
    intro v
    rcases le_or_gt (gridHi N v y) (gridLo N v y) with h | h
    · rw [gridCoeff_eq_zero h, ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.ofReal_zero]
    · rw [gridCoeff, max_eq_right (by linarith)]
  simp only [hstep] at key
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => gridCoeff_nonneg)] at key
  have hnn : (0 : ℝ) ≤ ∑ v ∈ gridVerts n N, gridCoeff N v y :=
    Finset.sum_nonneg fun _ _ => gridCoeff_nonneg
  have h1 : ENNReal.ofReal (∑ v ∈ gridVerts n N, gridCoeff N v y) = ENNReal.ofReal 1 := by
    rw [← key, ENNReal.ofReal_one]
  exact (ENNReal.ofReal_eq_ofReal_iff hnn zero_le_one).mp h1

/-! ### The coefficients at a grid point -/

/-- At a grid point `w / N` the barycentric coordinates are the Kronecker delta at `w`. -/
theorem gridCoeff_grid_point (hN : 1 ≤ N) (w : Fin n → ℕ) (v : Fin n → ℕ) :
    gridCoeff N v (fun j => (w j : ℝ) / N) = if v = w then 1 else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set y : Fin n → ℝ := fun j => (w j : ℝ) / N with hydef
  have hy : ∀ j, (N : ℝ) * y j - v j = (w j : ℝ) - v j := by
    intro j; rw [hydef]; field_simp
  split_ifs with h
  · subst h
    have hlo : gridLo N v y = 0 :=
      le_antisymm ((gridLo_le_iff (v := v) (y := y) 0).mpr
        ⟨le_rfl, fun j => by rw [hy]; simp⟩) gridLo_nonneg
    have hhi : gridHi N v y = 1 :=
      le_antisymm gridHi_le_one ((le_gridHi_iff (v := v) (y := y) 1).mpr
        ⟨le_rfl, fun j => by rw [hy]; simp⟩)
    rw [gridCoeff, hlo, hhi]; norm_num
  · obtain ⟨j, hj⟩ : ∃ j, v j ≠ w j := Function.ne_iff.mp h
    have hlo := le_gridLo (N := N) (v := v) (y := y) j
    have hhi := gridHi_le (N := N) (v := v) (y := y) j
    rw [hy] at hlo hhi
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · refine gridCoeff_eq_zero (le_trans gridHi_le_one ?_)
      have : (v j : ℝ) + 1 ≤ (w j : ℝ) := by exact_mod_cast hlt
      linarith
    · refine gridCoeff_eq_zero (le_trans ?_ gridLo_nonneg)
      have : (w j : ℝ) + 1 ≤ (v j : ℝ) := by exact_mod_cast hgt
      linarith

/-! ### Continuity -/

private theorem continuous_fold_max {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (b : ℝ)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun x => s.fold max b fun i => f i x := by
  induction s using Finset.cons_induction with
  | empty => simpa using continuous_const
  | cons a s ha ih => simpa [Finset.fold_cons ha] using (hf a).max ih

private theorem continuous_fold_min {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (b : ℝ)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    Continuous fun x => s.fold min b fun i => f i x := by
  induction s using Finset.cons_induction with
  | empty => simpa using continuous_const
  | cons a s ha ih => simpa [Finset.fold_cons ha] using (hf a).min ih

theorem continuous_gridLo (N : ℕ) (v : Fin n → ℕ) : Continuous (gridLo N v) :=
  continuous_fold_max _ _ _ fun j =>
    ((continuous_apply j).const_smul (N : ℝ)).sub continuous_const

theorem continuous_gridHi (N : ℕ) (v : Fin n → ℕ) : Continuous (gridHi N v) :=
  continuous_fold_min _ _ _ fun j =>
    (((continuous_apply j).const_smul (N : ℝ)).sub continuous_const).add continuous_const

theorem continuous_gridCoeff (N : ℕ) (v : Fin n → ℕ) : Continuous (gridCoeff N v) :=
  continuous_const.max ((continuous_gridHi N v).sub (continuous_gridLo N v))

end Submission
