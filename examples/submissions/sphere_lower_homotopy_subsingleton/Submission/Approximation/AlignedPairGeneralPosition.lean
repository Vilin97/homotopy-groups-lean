/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Lipschitz
import Submission.Approximation.ProjectedFiberPrism

/-!
# General position for vertically aligned pairs

Two points of an `(n+1)`-cube are vertically aligned when they have the same first `n`
coordinates.  Such a pair is parametrized by an `(n+2)`-cube: the common coordinates and two
independent last coordinates.  For a locally Lipschitz map `g`, the map which evaluates `g` on
the two aligned inputs is again locally Lipschitz.

This gives an efficient dimension-theoretic formulation of the point choice in the cubical
homotopy-excision proof.  A target pair absent from the aligned-pair range consists of a point
`a` which is absent from the image of the entire vertical prism over the projected `b`-fiber.
Thus one dimension comparison supplies exactly the geometric hypothesis consumed by
`ProjectedFiberPrism`.

## Main results

* `Submission.cubeAlignedPairMap`
* `Submission.locallyLipschitz_cubeAlignedPairMap`
* `Submission.not_mem_cubeAlignedPairMap_range_imp_not_mem_prism_image`
* `Submission.exists_aligned_pair_not_mem_range_of_dimH`
* `Submission.exists_pair_not_mem_prism_image_in_open_sets`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {n : ℕ}

/-- Dropping the last coordinate of a cube is `1`-Lipschitz. -/
theorem lipschitzWith_cubeDiscardLast :
    LipschitzWith 1 (Cube.discardLast : (I^ Fin (n + 1)) → I^ Fin n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  let i' : Fin (n + 1) :=
    ⟨i, i.prop.trans (by omega : n < n + 1)⟩
  have hi : i' = i.castSucc := Fin.ext rfl
  change dist (x i') (y i') ≤ dist x y
  rw [hi]
  simpa only [NNReal.coe_one, one_mul] using
    (LipschitzWith.eval i.castSucc).dist_le_mul x y

theorem cubeDiscardLast_eq_splitAtLast_snd (y : I^ Fin (n + 1)) :
    Cube.discardLast y = (Cube.splitAtLast y).2 := by
  funext i
  rw [Cube.splitAtLast_snd_apply_eq]
  rfl

/-- Form a second `(n+1)`-cube by retaining the first `n` coordinates of an `(n+2)`-cube and
using its last coordinate as the new last coordinate. -/
def cubeAlignedSecondInput :
    C(I^ Fin (n + 2), I^ Fin (n + 1)) where
  toFun y i := Fin.lastCases (y (Fin.last (n + 1)))
    (fun j => y j.castSucc.castSucc) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    induction i using Fin.lastCases with
    | last =>
        simpa only [Fin.lastCases_last] using
          (continuous_apply (Fin.last (n + 1)) :
            Continuous fun y : I^ Fin (n + 2) => y (Fin.last (n + 1)))
    | cast j =>
        simpa only [Fin.lastCases_castSucc] using
          (continuous_apply j.castSucc.castSucc :
            Continuous fun y : I^ Fin (n + 2) => y j.castSucc.castSucc)

@[simp] theorem cubeAlignedSecondInput_last (y : I^ Fin (n + 2)) :
    cubeAlignedSecondInput y (Fin.last n) = y (Fin.last (n + 1)) := by
  simp [cubeAlignedSecondInput]

@[simp] theorem cubeAlignedSecondInput_castSucc
    (y : I^ Fin (n + 2)) (i : Fin n) :
    cubeAlignedSecondInput y i.castSucc = y i.castSucc.castSucc := by
  simp [cubeAlignedSecondInput]

/-- The second aligned-input projection is also `1`-Lipschitz. -/
theorem lipschitzWith_cubeAlignedSecondInput :
    LipschitzWith 1 (cubeAlignedSecondInput : (I^ Fin (n + 2)) → I^ Fin (n + 1)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  induction i using Fin.lastCases with
  | last =>
      simpa using (LipschitzWith.eval (Fin.last (n + 1))).dist_le_mul x y
  | cast j =>
      simpa using (LipschitzWith.eval j.castSucc.castSucc).dist_le_mul x y

/-- Splitting the second aligned input exposes the outer last coordinate and the common first
`n` coordinates. -/
theorem cubeAlignedSecondInput_splitAtLast (y : I^ Fin (n + 2)) :
    Cube.splitAtLast (cubeAlignedSecondInput y) =
      ((Cube.splitAtLast y).1,
        (Cube.splitAtLast (Cube.discardLast y)).2) := by
  apply Prod.ext
  · rw [Cube.splitAtLast_fst_eq, Cube.splitAtLast_fst_eq]
    exact cubeAlignedSecondInput_last y
  · funext i
    rw [Cube.splitAtLast_snd_apply_eq, Cube.splitAtLast_snd_apply_eq]
    exact cubeAlignedSecondInput_castSucc y i

/-- Evaluate a map on the two vertically aligned inputs encoded by an `(n+2)`-cube. -/
def cubeAlignedPairMap {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) : C(I^ Fin (n + 2), X × X) where
  toFun y := (g (Cube.discardLast y), g (cubeAlignedSecondInput y))
  continuous_toFun := g.continuous.comp Cube.discardLast.continuous |>.prodMk
    (g.continuous.comp cubeAlignedSecondInput.continuous)

@[simp] theorem cubeAlignedPairMap_apply {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (y : I^ Fin (n + 2)) :
    cubeAlignedPairMap g y =
      (g (Cube.discardLast y), g (cubeAlignedSecondInput y)) :=
  rfl

/-- Aligned-pair evaluation preserves local Lipschitz regularity. -/
theorem locallyLipschitz_cubeAlignedPairMap {X : Type*} [PseudoMetricSpace X]
    (g : C(I^ Fin (n + 1), X)) (hg : LocallyLipschitz g) :
    LocallyLipschitz (cubeAlignedPairMap g) := by
  exact (hg.comp lipschitzWith_cubeDiscardLast.locallyLipschitz).prodMk
    (hg.comp lipschitzWith_cubeAlignedSecondInput.locallyLipschitz)

/-- An aligned target pair is in the aligned-pair range exactly when it is realized on two
points with a common projection.  This direction is the one used below. -/
theorem mem_cubeAlignedPairMap_range_of_common_projection
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (r : I^ Fin n) (s t : I) :
    (g (Cube.splitAtLast.symm (s, r)),
      g (Cube.splitAtLast.symm (t, r))) ∈ Set.range (cubeAlignedPairMap g) := by
  let y : I^ Fin (n + 2) :=
    Cube.splitAtLast.symm (t, Cube.splitAtLast.symm (s, r))
  refine ⟨y, ?_⟩
  have hout : Cube.splitAtLast y =
      (t, Cube.splitAtLast.symm (s, r)) := Cube.splitAtLast.apply_symm_apply _
  have hdrop : Cube.discardLast y = Cube.splitAtLast.symm (s, r) := by
    rw [cubeDiscardLast_eq_splitAtLast_snd, hout]
  have hsecond : cubeAlignedSecondInput y = Cube.splitAtLast.symm (t, r) := by
    apply Cube.splitAtLast.injective
    rw [cubeAlignedSecondInput_splitAtLast, hout, hdrop,
      Cube.splitAtLast.apply_symm_apply]
    simp
  simp only [cubeAlignedPairMap_apply, hdrop, hsecond]

/-- Absence of `(a,b)` from the aligned-pair range is exactly the prism-avoidance condition
needed for the Urysohn compression: `a` is absent from the image of the vertical prism over the
projected `b`-fiber. -/
theorem not_mem_cubeAlignedPairMap_range_imp_not_mem_prism_image
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (hab : (a, b) ∉ Set.range (cubeAlignedPairMap g)) :
    a ∉ g '' cubeLastFiberPrism g b := by
  rintro ⟨y, hyprism, hya⟩
  obtain ⟨t, hyt⟩ := (mem_cubeLastFiberPrism_iff g b y).mp hyprism
  let r := (Cube.splitAtLast y).2
  let s := (Cube.splitAtLast y).1
  have hy : y = Cube.splitAtLast.symm (s, r) :=
    (Cube.splitAtLast.symm_apply_apply y).symm
  have hfirst : g (Cube.splitAtLast.symm (s, r)) = a := by
    rw [← hy]
    exact hya
  have hrange := mem_cubeAlignedPairMap_range_of_common_projection g r s t
  rw [hfirst, hyt] at hrange
  exact hab hrange

/-- If a candidate target subset has Hausdorff dimension greater than `n+2`, it contains a pair
which is not realized by vertically aligned source points. -/
theorem exists_aligned_pair_not_mem_range_of_dimH
    {X : Type*} [MetricSpace X]
    (g : C(I^ Fin (n + 1), X)) (hg : LocallyLipschitz g)
    {W : Set (X × X)} (hdim : (↑(n + 2) : ENNReal) < dimH W) :
    ∃ z ∈ W, z ∉ Set.range (cubeAlignedPairMap g) :=
  exists_notMem_range_locallyLipschitz_cube_of_dimH
    (cubeAlignedPairMap g) (locallyLipschitz_cubeAlignedPairMap g hg) hdim

/-- Dimension-theoretic aligned-pair avoidance, stated directly as the prism hypothesis used by
the compression theorem. -/
theorem exists_pair_not_mem_prism_image_of_dimH
    {X : Type*} [MetricSpace X]
    (g : C(I^ Fin (n + 1), X)) (hg : LocallyLipschitz g)
    {W : Set (X × X)} (hdim : (↑(n + 2) : ENNReal) < dimH W) :
    ∃ a b, (a, b) ∈ W ∧ a ∉ g '' cubeLastFiberPrism g b := by
  obtain ⟨z, hzW, hz⟩ := exists_aligned_pair_not_mem_range_of_dimH g hg hdim
  exact ⟨z.1, z.2, hzW,
    not_mem_cubeAlignedPairMap_range_imp_not_mem_prism_image g z.1 z.2 hz⟩

/-- In a finite-dimensional vector space, two prescribed nonempty open sets contain a pair
which is absent from the aligned-pair range as soon as the aligned parameter cube has smaller
dimension than the product target. -/
theorem exists_pair_not_mem_prism_image_in_open_sets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (g : C(I^ Fin (n + 1), F)) (hg : LocallyLipschitz g)
    (hdim : n + 2 < 2 * Module.finrank ℝ F)
    {U V : Set F} (hU : IsOpen U) (hUne : U.Nonempty)
    (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ a ∈ U, ∃ b ∈ V, a ∉ g '' cubeLastFiberPrism g b := by
  have hdimprod : n + 2 < Module.finrank ℝ (F × F) := by
    rw [Module.finrank_prod]
    omega
  obtain ⟨z, hzUV, hz⟩ := exists_notMem_range_locallyLipschitz_cube
    (cubeAlignedPairMap g) (locallyLipschitz_cubeAlignedPairMap g hg)
    hdimprod (hU.prod hV) (Set.prod_nonempty_iff.mpr ⟨hUne, hVne⟩)
  exact ⟨z.1, hzUV.1, z.2, hzUV.2,
    not_mem_cubeAlignedPairMap_range_imp_not_mem_prism_image g z.1 z.2 hz⟩

/-- The preceding point choice specialized to a Kuhn-grid approximation.  This is the direct
sum-of-dimensions general-position theorem for the vertical-prism step. -/
theorem exists_cubeGridAffineApprox_pair_not_mem_prism_image
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (N : ℕ) (g : C(I^ Fin (n + 1), F))
    (hdim : n + 2 < 2 * Module.finrank ℝ F)
    {U V : Set F} (hU : IsOpen U) (hUne : U.Nonempty)
    (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ a ∈ U, ∃ b ∈ V,
      a ∉ cubeGridAffineApprox (n + 1) N g ''
        cubeLastFiberPrism (cubeGridAffineApprox (n + 1) N g) b := by
  exact exists_pair_not_mem_prism_image_in_open_sets
    (cubeGridAffineApprox (n + 1) N g)
    (locallyLipschitz_cubeGridAffineApprox g) hdim hU hUne hV hVne

end Submission
