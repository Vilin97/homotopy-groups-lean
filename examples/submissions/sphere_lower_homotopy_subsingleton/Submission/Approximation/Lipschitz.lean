/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Approx
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Lipschitz regularity of cubical grid approximations

The closed formulas for the Kuhn-grid barycentric coordinates use only finite maxima, finite
minima, and affine coordinate functions.  Consequently they are locally Lipschitz, as is every
finite-dimensional grid approximation.  This file records that regularity and the resulting
Hausdorff-dimension bound for images of cubes.

The dimension bound is useful for stable general position: a locally Lipschitz map from an
`n`-cube cannot cover a nonempty open subset of a Euclidean space of dimension greater than `n`.

## Main results

* `Submission.locallyLipschitz_gridCoeff`
* `Submission.locallyLipschitz_cubeGridAffineApprox`
* `Submission.dimH_univ_cube_le`
* `Submission.exists_notMem_range_locallyLipschitz_cube`
-/

open Set
open scoped unitInterval Topology

noncomputable section

namespace Submission

variable {α ι E : Type*} [PseudoEMetricSpace α]

/-- A finite maximum of locally Lipschitz real-valued functions is locally Lipschitz. -/
theorem locallyLipschitz_finset_fold_max (s : Finset ι) (b : α → ℝ) (f : ι → α → ℝ)
    (hb : LocallyLipschitz b) (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x => s.fold max (b x) fun i => f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | @insert i s hi ih =>
      simpa only [Finset.fold_insert hi] using
        (hf i (by simp)).max (ih fun j hj => hf j (by simp [hj]))

/-- A finite minimum of locally Lipschitz real-valued functions is locally Lipschitz. -/
theorem locallyLipschitz_finset_fold_min (s : Finset ι) (b : α → ℝ) (f : ι → α → ℝ)
    (hb : LocallyLipschitz b) (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x => s.fold min (b x) fun i => f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | @insert i s hi ih =>
      simpa only [Finset.fold_insert hi] using
        (hf i (by simp)).min (ih fun j hj => hf j (by simp [hj]))

variable {n N : ℕ} {v : Fin n → ℕ}

/-- An affine coordinate occurring in `gridLo` and `gridHi` is globally Lipschitz. -/
theorem lipschitzWith_gridAffineCoordinate (j : Fin n) :
    LipschitzWith (N : NNReal)
      (fun y : Fin n → ℝ => (N : ℝ) * y j - v j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg N)]
  have hj : |x j - y j| ≤ dist x y := by
    simpa [Real.dist_eq] using (LipschitzWith.eval j).dist_le_mul x y
  exact mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg N)

/-- The lower endpoint of a grid barycentric interval is locally Lipschitz. -/
theorem locallyLipschitz_gridLo :
    LocallyLipschitz (gridLo N v : (Fin n → ℝ) → ℝ) := by
  change LocallyLipschitz fun y : Fin n → ℝ =>
    Finset.univ.fold max 0 fun j => (N : ℝ) * y j - v j
  exact locallyLipschitz_finset_fold_max (α := Fin n → ℝ) Finset.univ (fun _ => 0)
    (fun j y => (N : ℝ) * y j - v j)
    (LocallyLipschitz.const 0)
    (fun j _ =>
      (lipschitzWith_gridAffineCoordinate (N := N) (v := v) j).locallyLipschitz)

/-- The upper endpoint of a grid barycentric interval is locally Lipschitz. -/
theorem locallyLipschitz_gridHi :
    LocallyLipschitz (gridHi N v : (Fin n → ℝ) → ℝ) := by
  change LocallyLipschitz fun y : Fin n → ℝ =>
    Finset.univ.fold min 1 fun j => (N : ℝ) * y j - v j + 1
  exact locallyLipschitz_finset_fold_min (α := Fin n → ℝ) Finset.univ (fun _ => 1)
    (fun j y => (N : ℝ) * y j - v j + 1)
    (LocallyLipschitz.const 1)
    (fun j _ => ((lipschitzWith_gridAffineCoordinate (N := N) (v := v) j).add
      (LipschitzWith.const 1)).locallyLipschitz)

/-- Every Kuhn-grid barycentric coefficient is locally Lipschitz. -/
theorem locallyLipschitz_gridCoeff :
    LocallyLipschitz (gridCoeff N v : (Fin n → ℝ) → ℝ) := by
  exact (locallyLipschitz_gridHi (N := N) (v := v)).sub
    (locallyLipschitz_gridLo (N := N) (v := v)) |>.const_max 0

/-- The coordinatewise coercion from the unit cube to its ambient real coordinate space is an
isometry. -/
theorem isometry_cubeCoe :
    Isometry (fun y : I^ Fin n => fun j => (y j : ℝ)) := by
  apply Isometry.of_dist_eq
  intro x y
  apply le_antisymm
  · rw [dist_pi_le_iff dist_nonneg]
    intro j
    simpa [Subtype.dist_eq] using (LipschitzWith.eval j).dist_le_mul x y
  · rw [dist_pi_le_iff dist_nonneg]
    intro j
    have hj := (LipschitzWith.eval j).dist_le_mul
      (fun i => (x i : ℝ)) (fun i => (y i : ℝ))
    simpa [Subtype.dist_eq] using hj

/-- In particular, the ambient-coordinate map of a cube is locally Lipschitz. -/
theorem locallyLipschitz_cubeCoe :
    LocallyLipschitz (fun y : I^ Fin n => fun j => (y j : ℝ)) :=
  isometry_cubeCoe.lipschitz.locallyLipschitz

/-- Multiplying a fixed vector by a locally Lipschitz real coefficient preserves local
Lipschitz regularity. -/
theorem locallyLipschitz_smul_const
    {β : Type*} [PseudoMetricSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → ℝ} (hf : LocallyLipschitz f) (c : E) :
    LocallyLipschitz fun x => f x • c := by
  intro x
  obtain ⟨K, s, hs, hK⟩ := hf x
  refine ⟨‖c‖₊ * K, s, hs, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
  calc
    |f y - f z| * ‖c‖ = ‖c‖ * dist (f y) (f z) := by
      rw [Real.dist_eq, mul_comm]
    _ ≤ ‖c‖ * ((K : ℝ) * dist y z) :=
      mul_le_mul_of_nonneg_left (hK.dist_le_mul y hy z hz) (norm_nonneg c)
    _ = ((‖c‖₊ * K : NNReal) : ℝ) * dist y z := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- A finite sum of locally Lipschitz maps into a normed additive group is locally Lipschitz. -/
theorem locallyLipschitz_finset_sum
    {β : Type*} [PseudoMetricSpace β]
    [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → β → E)
    (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LocallyLipschitz.const (0 : E))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih fun j hj => hf j (by simp [hj]))

/-- Every finite-dimensional cubical grid approximation is locally Lipschitz. -/
theorem locallyLipschitz_cubeGridAffineApprox
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : C(I^ Fin n, E)) :
    LocallyLipschitz (cubeGridAffineApprox n N g) := by
  change LocallyLipschitz fun y : I^ Fin n =>
    ∑ v ∈ gridVerts n N,
      gridCoeff N v (fun j => (y j : ℝ)) • g (gridVertex N v)
  apply locallyLipschitz_finset_sum (gridVerts n N)
  intro v _
  exact locallyLipschitz_smul_const
    ((locallyLipschitz_gridCoeff (N := N) (v := v)).comp locallyLipschitz_cubeCoe)
    (g (gridVertex N v))

/-- The Hausdorff dimension of an `n`-cube is at most `n`. -/
theorem dimH_univ_cube_le :
    dimH (Set.univ : Set (I^ Fin n)) ≤ n := by
  let e : (I^ Fin n) → (Fin n → ℝ) := fun y j => (y j : ℝ)
  calc
    dimH (Set.univ : Set (I^ Fin n)) = dimH (e '' Set.univ) :=
      (isometry_cubeCoe.dimH_image Set.univ).symm
    _ ≤ dimH (Set.univ : Set (Fin n → ℝ)) :=
      dimH_mono (fun _ _ => Set.mem_univ _)
    _ = n := Real.dimH_univ_pi_fin n

/-- The range of a locally Lipschitz map out of an `n`-cube has Hausdorff dimension at most `n`. -/
theorem dimH_range_locallyLipschitz_cube_le
    {F : Type*} [EMetricSpace F] (f : (I^ Fin n) → F)
    (hf : LocallyLipschitz f) :
    dimH (Set.range f) ≤ n :=
  (dimH_range_le_of_locally_lipschitzOn hf).trans dimH_univ_cube_le

/-- A subset whose Hausdorff dimension is greater than `n` cannot be covered by a locally
Lipschitz image of the `n`-cube. -/
theorem exists_notMem_range_locallyLipschitz_cube_of_dimH
    {F : Type*} [EMetricSpace F]
    (f : (I^ Fin n) → F) (hf : LocallyLipschitz f) {U : Set F}
    (hdim : (n : ENNReal) < dimH U) :
    ∃ z ∈ U, z ∉ Set.range f := by
  by_contra h
  push Not at h
  have hsubset : U ⊆ Set.range f := fun z hz => h z hz
  exact (not_le_of_gt hdim) <|
    (dimH_mono hsubset).trans (dimH_range_locallyLipschitz_cube_le f hf)

/-- A locally Lipschitz image of an `n`-cube cannot cover a nonempty open subset of a
finite-dimensional real normed space of dimension greater than `n`. -/
theorem exists_notMem_range_locallyLipschitz_cube
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : (I^ Fin n) → F) (hf : LocallyLipschitz f)
    (hdim : n < Module.finrank ℝ F) {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, z ∉ Set.range f := by
  by_contra h
  push Not at h
  have hsubset : U ⊆ Set.range f := fun z hz => h z hz
  have hdimU : dimH U = Module.finrank ℝ F := by
    apply Real.dimH_of_nonempty_interior
    rwa [hU.interior_eq]
  have hle : (↑(Module.finrank ℝ F) : ENNReal) ≤ (n : ENNReal) := by
    rw [← hdimU]
    exact (dimH_mono hsubset).trans (dimH_range_locallyLipschitz_cube_le f hf)
  have hleNat : Module.finrank ℝ F ≤ n := by exact_mod_cast hle
  omega

end Submission
