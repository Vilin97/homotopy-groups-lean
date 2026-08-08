/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Estimate
import Submission.Approximation.RegularValue

/-!
# The simplicial structure of the piecewise-affine approximation

The value of `Submission.cubeGridAffineApprox n N g` at a point `y` of the cube is a convex
combination of the values of `g` at the grid vertices `v` with `gridCoeff N v y > 0`.  The
content of the Kuhn (Freudenthal) triangulation is that these vertices are the vertices of a
*single* small simplex, so there are at most `n + 1` of them
(`Submission.card_activeVerts_le`).  Equivalently: the approximation maps each point into the
convex hull of at most `n + 1` of the values of `g` at grid points.

This is exactly the amount of simplicial structure that the general position argument needs in
the low-dimensional case.  Combined with `Submission/Approximation/RegularValue.lean` it gives,
for `n + 1 ≤ finrank ℝ F`:

* `Submission.addHaar_range_cubeGridAffineApprox` — the image of the whole cube under the
  approximation is Haar-null;
* `Submission.exists_notMem_range_cubeGridAffineApprox` — every nonempty open set contains a
  point which the approximation misses;
* `Submission.not_surjective_cubeGridAffineApprox` — the approximation is not surjective.

Taking `F = EuclideanSpace ℝ (Fin m)` with `n < m` this is the analytic input for
`π_n (Sᵐ) = 0`: a map of the `n`-cube into `ℝᵐ` is uniformly approximable by maps that miss a
point.
-/

open scoped unitInterval Topology

open MeasureTheory Module

namespace Submission

variable {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### At most `n + 1` grid vertices contribute at a point -/

theorem activeVerts_nonempty (hN : 1 ≤ N) (y : I^ Fin n) : (activeVerts N y).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hs := sum_gridCoeff_activeVerts (n := n) hN y
  rw [h, Finset.sum_empty] at hs
  exact zero_ne_one hs

/-- **The contributing grid vertices are the vertices of a single Kuhn simplex**, so there are at
most `n + 1` of them. -/
theorem card_activeVerts_le (hN : 1 ≤ N) (y : I^ Fin n) : (activeVerts N y).card ≤ n + 1 := by
  classical
  set yc : Fin n → ℝ := fun j => (y j : ℝ) with hyc
  obtain ⟨w, hw, hwmax⟩ :=
    (activeVerts N y).exists_max_image (fun v => gridLo N v yc) (activeVerts_nonempty hN y)
  -- The contributing vertices are compared coordinatewise with the maximal one.
  have hcmp : ∀ v ∈ activeVerts N y, ∀ j, w j ≤ v j ∧ v j ≤ w j + 1 := fun v hv j =>
    le_of_gridCoeff_pos_of_gridLo_le (mem_activeVerts.mp hv).2 (mem_activeVerts.mp hw).2
      (hwmax v hv) j
  -- Hence the coordinate sums land in an interval of `n + 1` integers …
  have hmaps : Set.MapsTo (fun v : Fin n → ℕ => ∑ j, v j) (activeVerts N y)
      (Finset.Icc (∑ j, w j) (∑ j, w j + n)) := by
    intro v hv
    refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr
      ⟨Finset.sum_le_sum fun j _ => (hcmp v hv j).1, ?_⟩)
    calc ∑ j, v j ≤ ∑ j : Fin n, (w j + 1) := Finset.sum_le_sum fun j _ => (hcmp v hv j).2
      _ = ∑ j, w j + n := by rw [Finset.sum_add_distrib]; simp
  -- … and the coordinate sum is injective on them, because they are totally ordered.
  have hchain : ∀ a ∈ activeVerts N y, ∀ b ∈ activeVerts N y,
      gridLo N a yc ≤ gridLo N b yc → (∑ j, a j) = (∑ j, b j) → a = b := by
    intro a ha b hb hle hsum
    have hba : ∀ j, b j ≤ a j := fun j =>
      (le_of_gridCoeff_pos_of_gridLo_le (mem_activeVerts.mp ha).2 (mem_activeVerts.mp hb).2
        hle j).1
    funext j
    by_contra hne
    have hlt : b j < a j := lt_of_le_of_ne (hba j) (Ne.symm hne)
    have hsum' : ∑ j, b j < ∑ j, a j :=
      Finset.sum_lt_sum (fun i _ => hba i) ⟨j, Finset.mem_univ j, hlt⟩
    omega
  have hinj : Set.InjOn (fun v : Fin n → ℕ => ∑ j, v j) (activeVerts N y) := by
    intro a ha b hb hsum
    rcases le_total (gridLo N a yc) (gridLo N b yc) with h | h
    · exact hchain a ha b hb h hsum
    · exact (hchain b hb a ha h hsum.symm).symm
  calc (activeVerts N y).card
      ≤ (Finset.Icc (∑ j, w j) (∑ j, w j + n)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = n + 1 := by rw [Nat.card_Icc]; omega

/-! ### The value lies in the convex hull of at most `n + 1` values of `g` -/

/-- The finite family of "small simplices" of the grid: subsets of the grid vertices of
cardinality at most `n + 1`. -/
def gridSimplices (n N : ℕ) : Finset (Finset (Fin n → ℕ)) :=
  (gridVerts n N).powerset.filter fun S => S.card ≤ n + 1

theorem activeVerts_mem_gridSimplices (hN : 1 ≤ N) (y : I^ Fin n) :
    activeVerts N y ∈ gridSimplices n N :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), card_activeVerts_le hN y⟩

theorem card_le_of_mem_gridSimplices {S : Finset (Fin n → ℕ)} (hS : S ∈ gridSimplices n N) :
    S.card ≤ n + 1 := (Finset.mem_filter.mp hS).2

/-- The value of the approximation at `y` lies in the convex hull of the values of `g` at the
vertices that contribute at `y` — at most `n + 1` grid points. -/
theorem cubeGridAffineApprox_mem_convexHull (hN : 1 ≤ N) (g : C(I^ Fin n, E)) (y : I^ Fin n) :
    cubeGridAffineApprox n N g y ∈
      convexHull ℝ ((fun v => g (gridVertex N v)) '' (activeVerts N y : Set (Fin n → ℕ))) := by
  have hsum := sum_gridCoeff_activeVerts (n := n) hN y
  rw [cubeGridAffineApprox_eq_sum_activeVerts, ← Finset.centerMass_eq_of_sum_1 _ _ hsum]
  exact Finset.centerMass_mem_convexHull _ (fun i _ => gridCoeff_nonneg)
    (by rw [hsum]; norm_num) fun v hv => Set.mem_image_of_mem _ (Finset.mem_coe.mpr hv)

/-- The image of the cube is covered by the finitely many convex hulls attached to the
simplices of the grid. -/
theorem range_cubeGridAffineApprox_subset (hN : 1 ≤ N) (g : C(I^ Fin n, E)) :
    Set.range (cubeGridAffineApprox n N g) ⊆
      ⋃ S ∈ gridSimplices n N,
        convexHull ℝ ((fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ))) := by
  rintro _ ⟨y, rfl⟩
  exact Set.mem_iUnion₂.mpr
    ⟨activeVerts N y, activeVerts_mem_gridSimplices hN y,
      cubeGridAffineApprox_mem_convexHull hN g y⟩

/-! ### General position in low dimensions -/

section LowDim

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] (μ : Measure F) [μ.IsAddHaarMeasure]

include μ in
/-- The convex hull of the `g`-values at a grid simplex is Haar-null once
`n + 1 ≤ finrank ℝ F`. -/
theorem addHaar_convexHull_image_gridSimplex (hdim : n + 1 ≤ finrank ℝ F) (g : C(I^ Fin n, F))
    {S : Finset (Fin n → ℕ)} (hS : S ∈ gridSimplices n N) :
    μ (convexHull ℝ ((fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ)))) = 0 := by
  classical
  have himg : (fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ))
      = ((S.image fun v => g (gridVertex N v) : Finset F) : Set F) := (Finset.coe_image).symm
  rw [himg]
  refine addHaar_of_finset_card_le μ (convexHull_subset_affineSpan _) ?_
  exact le_trans (le_trans Finset.card_image_le (card_le_of_mem_gridSimplices hS)) hdim

include μ in
/-- The image of the cube under the piecewise-affine approximation is Haar-null whenever
`n + 1 ≤ finrank ℝ F`. -/
theorem addHaar_range_cubeGridAffineApprox (hN : 1 ≤ N) (hdim : n + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) : μ (Set.range (cubeGridAffineApprox n N g)) = 0 := by
  have hsum : ∑ S ∈ gridSimplices n N,
      μ (convexHull ℝ ((fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ)))) = 0 :=
    Finset.sum_eq_zero fun S hS => addHaar_convexHull_image_gridSimplex μ hdim g hS
  refine measure_mono_null (range_cubeGridAffineApprox_subset hN g) (nonpos_iff_eq_zero.mp ?_)
  exact hsum ▸ measure_biUnion_finset_le _ _

include μ in
/-- **General position in low dimensions.**  If the cube has dimension `n` with
`n + 1 ≤ finrank ℝ F`, then every nonempty open subset of `F` contains a point missed by the
piecewise-affine approximation.

With `F = EuclideanSpace ℝ (Fin m)` and `n < m` this says that a piecewise-affine map of the
`n`-cube into `ℝᵐ` misses points of every open set — the analytic input for `π_n (Sᵐ) = 0`. -/
theorem exists_notMem_range_cubeGridAffineApprox (hN : 1 ≤ N) (hdim : n + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, q ∉ Set.range (cubeGridAffineApprox n N g) := by
  have hpos := hU.measure_pos μ hUne
  have hnull := addHaar_range_cubeGridAffineApprox μ hN hdim g
  have hsub : ¬U ⊆ Set.range (cubeGridAffineApprox n N g) := fun h =>
    hpos.ne' (measure_mono_null h hnull)
  exact Set.not_subset.mp hsub

include μ in
/-- A piecewise-affine approximation of a map of the `n`-cube into a space of dimension at least
`n + 1` is never surjective. -/
theorem not_surjective_cubeGridAffineApprox (hN : 1 ≤ N) (hdim : n + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) : ¬Function.Surjective (cubeGridAffineApprox n N g) := by
  intro hsurj
  obtain ⟨q, -, hq⟩ := exists_notMem_range_cubeGridAffineApprox μ hN hdim g isOpen_univ
    Set.univ_nonempty
  exact hq (hsurj q)

end LowDim

end Submission
