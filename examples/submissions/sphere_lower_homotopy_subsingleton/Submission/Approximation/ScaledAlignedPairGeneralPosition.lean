/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.AlignedPairGeneralPosition
import Submission.Model.SphereCompl

/-!
# General position for scaled vertically aligned pairs

Radial projection identifies positive scalar multiples.  To transfer the aligned-pair general
position theorem from a sphere-valued map to a piecewise-affine map in the ambient vector
space, we therefore add two independent scale coordinates.  An `(n+4)`-cube records two
vertically aligned points of an `(n+1)`-cube and one scale for each of their images.

The resulting map is locally Lipschitz whenever the original map is.  Its domain has exactly
the dimension required by the stable homotopy-excision inequality after passing from a sphere
to its one-dimension-larger ambient vector space.

## Main results

* `Submission.cubeScaledAlignedPairMap`
* `Submission.locallyLipschitz_cubeScaledAlignedPairMap`
* `Submission.mem_cubeScaledAlignedPairMap_range_of_common_projection`
* `Submission.exists_scaled_aligned_pair_not_mem_range_in_open_sets`
* `Submission.exists_radial_pair_not_mem_prism_image_in_open_sets`
-/

open Set
open scoped unitInterval Topology

noncomputable section

namespace Submission

variable {n : ℕ}

/-- The aligned-pair parameter obtained by dropping the two final scale coordinates. -/
def cubeScaledAlignedCore : C(I^ Fin (n + 4), I^ Fin (n + 2)) :=
  Cube.discardLast.comp Cube.discardLast

@[simp] theorem cubeScaledAlignedCore_apply (y : I^ Fin (n + 4)) :
    cubeScaledAlignedCore y = Cube.discardLast (Cube.discardLast y) :=
  rfl

/-- The first of the two scale coordinates in a scaled aligned-pair parameter. -/
def cubeScaledAlignedFirstScale : C(I^ Fin (n + 4), ℝ) where
  toFun y := y (Fin.last (n + 2)).castSucc
  continuous_toFun := continuous_subtype_val.comp
    (continuous_apply (Fin.last (n + 2)).castSucc)

/-- The second of the two scale coordinates in a scaled aligned-pair parameter. -/
def cubeScaledAlignedSecondScale : C(I^ Fin (n + 4), ℝ) where
  toFun y := y (Fin.last (n + 3))
  continuous_toFun := continuous_subtype_val.comp
    (continuous_apply (Fin.last (n + 3)))

@[simp] theorem cubeScaledAlignedFirstScale_apply (y : I^ Fin (n + 4)) :
    cubeScaledAlignedFirstScale y = (y (Fin.last (n + 2)).castSucc : ℝ) :=
  rfl

@[simp] theorem cubeScaledAlignedSecondScale_apply (y : I^ Fin (n + 4)) :
    cubeScaledAlignedSecondScale y = (y (Fin.last (n + 3)) : ℝ) :=
  rfl

/-- Evaluate a map on two vertically aligned inputs and independently scale the two outputs by
numbers in `[0,L]`.  Positivity of `L` is not needed for the definition or its regularity. -/
def cubeScaledAlignedPairMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ) (g : C(I^ Fin (n + 1), F)) :
    C(I^ Fin (n + 4), F × F) where
  toFun y :=
    let p := cubeAlignedPairMap g (cubeScaledAlignedCore y)
    ((L * cubeScaledAlignedFirstScale y) • p.1,
      (L * cubeScaledAlignedSecondScale y) • p.2)
  continuous_toFun := by
    fun_prop

@[simp] theorem cubeScaledAlignedPairMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ) (g : C(I^ Fin (n + 1), F)) (y : I^ Fin (n + 4)) :
    cubeScaledAlignedPairMap L g y =
      ((L * cubeScaledAlignedFirstScale y) •
          g (Cube.discardLast (cubeScaledAlignedCore y)),
        (L * cubeScaledAlignedSecondScale y) •
          g (cubeAlignedSecondInput (cubeScaledAlignedCore y))) :=
  rfl

/-- The two-coordinate discard used above is globally `1`-Lipschitz. -/
theorem lipschitzWith_cubeScaledAlignedCore :
    LipschitzWith 1
      (cubeScaledAlignedCore : (I^ Fin (n + 4)) → I^ Fin (n + 2)) := by
  simpa [cubeScaledAlignedCore] using
    (lipschitzWith_cubeDiscardLast (n := n + 2)).comp
      (lipschitzWith_cubeDiscardLast (n := n + 3))

/-- Each real-valued coordinate of a cube is locally Lipschitz. -/
theorem locallyLipschitz_cubeCoordinate {m : ℕ} (i : Fin m) :
    LocallyLipschitz fun y : I^ Fin m => (y i : ℝ) :=
  (LipschitzWith.eval i).locallyLipschitz.comp locallyLipschitz_cubeCoe

/-- Both scale coordinates are locally Lipschitz. -/
theorem locallyLipschitz_cubeScaledAlignedFirstScale :
    LocallyLipschitz
      (cubeScaledAlignedFirstScale : (I^ Fin (n + 4)) → ℝ) :=
  locallyLipschitz_cubeCoordinate (Fin.last (n + 2)).castSucc

theorem locallyLipschitz_cubeScaledAlignedSecondScale :
    LocallyLipschitz
      (cubeScaledAlignedSecondScale : (I^ Fin (n + 4)) → ℝ) :=
  locallyLipschitz_cubeCoordinate (Fin.last (n + 3))

/-- Scaled aligned-pair evaluation preserves local Lipschitz regularity. -/
theorem locallyLipschitz_cubeScaledAlignedPairMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ) (g : C(I^ Fin (n + 1), F)) (hg : LocallyLipschitz g) :
    LocallyLipschitz (cubeScaledAlignedPairMap L g) := by
  have hpair : LocallyLipschitz fun y : I^ Fin (n + 4) =>
      cubeAlignedPairMap g (cubeScaledAlignedCore y) :=
    (locallyLipschitz_cubeAlignedPairMap g hg).comp
      lipschitzWith_cubeScaledAlignedCore.locallyLipschitz
  have hfirst : LocallyLipschitz fun y : I^ Fin (n + 4) =>
      (cubeAlignedPairMap g (cubeScaledAlignedCore y)).1 :=
    LipschitzWith.prod_fst.locallyLipschitz.comp hpair
  have hsecond : LocallyLipschitz fun y : I^ Fin (n + 4) =>
      (cubeAlignedPairMap g (cubeScaledAlignedCore y)).2 :=
    LipschitzWith.prod_snd.locallyLipschitz.comp hpair
  have hscaleFirst : LocallyLipschitz fun y : I^ Fin (n + 4) =>
      L * cubeScaledAlignedFirstScale y := by
    simpa [smul_eq_mul, mul_comm] using locallyLipschitz_smul_const
      locallyLipschitz_cubeScaledAlignedFirstScale L
  have hscaleSecond : LocallyLipschitz fun y : I^ Fin (n + 4) =>
      L * cubeScaledAlignedSecondScale y := by
    simpa [smul_eq_mul, mul_comm] using locallyLipschitz_smul_const
      locallyLipschitz_cubeScaledAlignedSecondScale L
  exact (locallyLipschitz_smul hscaleFirst hfirst).prodMk
    (locallyLipschitz_smul hscaleSecond hsecond)

/-- Any two aligned evaluations with independently chosen unit-interval scales occur in the
range of the scaled aligned-pair map. -/
theorem mem_cubeScaledAlignedPairMap_range_of_common_projection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ) (g : C(I^ Fin (n + 1), F))
    (r : I^ Fin n) (s t u v : I) :
    ((L * (u : ℝ)) • g (Cube.splitAtLast.symm (s, r)),
      (L * (v : ℝ)) • g (Cube.splitAtLast.symm (t, r))) ∈
        Set.range (cubeScaledAlignedPairMap L g) := by
  let y : I^ Fin (n + 2) :=
    Cube.splitAtLast.symm (t, Cube.splitAtLast.symm (s, r))
  let z : I^ Fin (n + 4) :=
    Cube.splitAtLast.symm (v, Cube.splitAtLast.symm (u, y))
  refine ⟨z, ?_⟩
  have hz : Cube.splitAtLast z =
      (v, Cube.splitAtLast.symm (u, y)) := Cube.splitAtLast.apply_symm_apply _
  have hz' : Cube.splitAtLast (Cube.discardLast z) = (u, y) := by
    rw [cubeDiscardLast_eq_splitAtLast_snd, hz]
    exact Cube.splitAtLast.apply_symm_apply _
  have hcore : cubeScaledAlignedCore z = y := by
    rw [cubeScaledAlignedCore_apply, cubeDiscardLast_eq_splitAtLast_snd,
      cubeDiscardLast_eq_splitAtLast_snd, hz, Cube.splitAtLast.apply_symm_apply]
  have hscaleFirst : cubeScaledAlignedFirstScale z = (u : ℝ) := by
    change (z (Fin.last (n + 2)).castSucc : ℝ) = u
    have h := congrArg Prod.fst hz'
    rw [Cube.splitAtLast_fst_eq] at h
    exact congrArg Subtype.val h
  have hscaleSecond : cubeScaledAlignedSecondScale z = (v : ℝ) := by
    change (z (Fin.last (n + 3)) : ℝ) = v
    have h := congrArg Prod.fst hz
    rw [Cube.splitAtLast_fst_eq] at h
    exact congrArg Subtype.val h
  have hdrop : Cube.discardLast y = Cube.splitAtLast.symm (s, r) := by
    rw [cubeDiscardLast_eq_splitAtLast_snd, show Cube.splitAtLast y =
      (t, Cube.splitAtLast.symm (s, r)) from Cube.splitAtLast.apply_symm_apply _]
  have hsecond : cubeAlignedSecondInput y = Cube.splitAtLast.symm (t, r) := by
    apply Cube.splitAtLast.injective
    rw [cubeAlignedSecondInput_splitAtLast,
      show Cube.splitAtLast y = (t, Cube.splitAtLast.symm (s, r)) from
        Cube.splitAtLast.apply_symm_apply _, hdrop, Cube.splitAtLast.apply_symm_apply]
    simp
  simp only [cubeScaledAlignedPairMap_apply, hcore, hscaleFirst, hscaleSecond,
    hdrop, hsecond]

/-- A locally Lipschitz scaled aligned-pair image cannot cover a nonempty open subset of the
ambient product when its parameter cube has smaller dimension. -/
theorem exists_scaled_aligned_pair_not_mem_range_in_open_sets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : ℝ) (g : C(I^ Fin (n + 1), F)) (hg : LocallyLipschitz g)
    (hdim : n + 4 < 2 * Module.finrank ℝ F)
    {U V : Set F} (hU : IsOpen U) (hUne : U.Nonempty)
    (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ a ∈ U, ∃ b ∈ V, (a, b) ∉ Set.range (cubeScaledAlignedPairMap L g) := by
  have hdimprod : n + 4 < Module.finrank ℝ (F × F) := by
    rw [Module.finrank_prod]
    omega
  obtain ⟨z, hzUV, hz⟩ := exists_notMem_range_locallyLipschitz_cube
    (cubeScaledAlignedPairMap L g)
    (locallyLipschitz_cubeScaledAlignedPairMap L g hg)
    hdimprod (hU.prod hV) (Set.prod_nonempty_iff.mpr ⟨hUne, hVne⟩)
  exact ⟨z.1, hzUV.1, z.2, hzUV.2, hz⟩

/-! ### Passage to radial projection -/

/-- Radially project a nowhere-zero ambient cubical map. -/
def radialProjCubeMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : C(I^ Fin (n + 1), F)) (hne : ∀ y, g y ≠ 0) :
    C(I^ Fin (n + 1), F) where
  toFun y := radialProj (g y)
  continuous_toFun := continuous_radialProj g.continuous hne

@[simp] theorem radialProjCubeMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : C(I^ Fin (n + 1), F)) (hne : ∀ y, g y ≠ 0) (y : I^ Fin (n + 1)) :
    radialProjCubeMap g hne y = radialProj (g y) :=
  rfl

/-- Equality of radial projections expresses one nonzero vector as a positive scalar multiple
of the other.  The scalar is the quotient of their norms. -/
theorem eq_norm_div_smul_of_radialProj_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x a : F} (ha : a ≠ 0)
    (h : radialProj x = radialProj a) :
    a = (‖a‖ / ‖x‖) • x := by
  calc
    a = ‖a‖ • radialProj a := (smul_norm_radialProj ha).symm
    _ = ‖a‖ • radialProj x := by rw [h]
    _ = ‖a‖ • (‖x‖⁻¹ • x) := by rw [radialProj]
    _ = (‖a‖ / ‖x‖) • x := by rw [smul_smul, div_eq_mul_inv]

/-- A scalar between `0` and a positive `L` is `L` times a unit-interval coordinate. -/
theorem exists_unitInterval_scale {L c : ℝ} (hL : 0 < L)
    (hc0 : 0 ≤ c) (hcL : c ≤ L) :
    ∃ u : I, L * (u : ℝ) = c := by
  let u : I := ⟨c / L, div_nonneg hc0 hL.le, (div_le_one hL).2 hcL⟩
  refine ⟨u, ?_⟩
  change L * (c / L) = c
  field_simp

/-- If an ambient pair `(a,b)` is absent from the scaled aligned-pair range, then their radial
directions satisfy the prism-avoidance condition, provided every required norm quotient lies
in the available scale interval. -/
theorem not_mem_cubeScaledAlignedPairMap_range_imp_not_mem_radial_prism_image
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ) (hL : 0 < L) (g : C(I^ Fin (n + 1), F))
    (hne : ∀ y, g y ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hscaleA : ∀ y, ‖a‖ / ‖g y‖ ≤ L)
    (hscaleB : ∀ y, ‖b‖ / ‖g y‖ ≤ L)
    (hab : (a, b) ∉ Set.range (cubeScaledAlignedPairMap L g)) :
    radialProj a ∉
      radialProjCubeMap g hne ''
        cubeLastFiberPrism (radialProjCubeMap g hne) (radialProj b) := by
  rintro ⟨y, hyprism, hya⟩
  obtain ⟨t, hyt⟩ :=
    (mem_cubeLastFiberPrism_iff (radialProjCubeMap g hne) (radialProj b) y).mp hyprism
  let r : I^ Fin n := (Cube.splitAtLast y).2
  let s : I := (Cube.splitAtLast y).1
  have hy : y = Cube.splitAtLast.symm (s, r) :=
    (Cube.splitAtLast.symm_apply_apply y).symm
  let cA : ℝ := ‖a‖ / ‖g (Cube.splitAtLast.symm (s, r))‖
  let cB : ℝ := ‖b‖ / ‖g (Cube.splitAtLast.symm (t, r))‖
  have hcA0 : 0 ≤ cA := div_nonneg (norm_nonneg a) (norm_nonneg _)
  have hcB0 : 0 ≤ cB := div_nonneg (norm_nonneg b) (norm_nonneg _)
  have hcAL : cA ≤ L := hscaleA _
  have hcBL : cB ≤ L := hscaleB _
  obtain ⟨u, hu⟩ := exists_unitInterval_scale hL hcA0 hcAL
  obtain ⟨v, hv⟩ := exists_unitInterval_scale hL hcB0 hcBL
  have hradA : radialProj (g (Cube.splitAtLast.symm (s, r))) = radialProj a := by
    rw [← hy]
    exact hya
  have hradB : radialProj (g (Cube.splitAtLast.symm (t, r))) = radialProj b :=
    hyt
  have hambA : a = cA • g (Cube.splitAtLast.symm (s, r)) :=
    eq_norm_div_smul_of_radialProj_eq ha hradA
  have hambB : b = cB • g (Cube.splitAtLast.symm (t, r)) :=
    eq_norm_div_smul_of_radialProj_eq hb hradB
  apply hab
  have hrange := mem_cubeScaledAlignedPairMap_range_of_common_projection
    L g r s t u v
  rwa [hu, hv, ← hambA, ← hambB] at hrange

/-- The norm bounds arising from a `1/2`-close approximation to a unit sphere map fit into the
fixed scale interval `[0,4]` for every ambient candidate of norm at most `2`. -/
theorem norm_div_le_four_of_norm_le_two_of_half_le
    {F : Type*} [NormedAddCommGroup F]
    {a x : F} (ha : ‖a‖ ≤ 2) (hx : 1 / 2 ≤ ‖x‖) :
    ‖a‖ / ‖x‖ ≤ 4 := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx
  rw [div_le_iff₀ hxpos]
  nlinarith

/-- Stable ambient general position for radial projection.  Candidate points are chosen in two
prescribed nonempty open subsets of the punctured radius-two ball.  Their radial directions
then satisfy the vertical-prism avoidance hypothesis needed by the two-point compression. -/
theorem exists_radial_pair_not_mem_prism_image_in_open_sets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (g : C(I^ Fin (n + 1), F)) (hg : LocallyLipschitz g)
    (hne : ∀ y, g y ≠ 0) (hhalf : ∀ y, 1 / 2 ≤ ‖g y‖)
    (hdim : n + 4 < 2 * Module.finrank ℝ F)
    {U V : Set F} (hU : IsOpen U) (hUne : U.Nonempty)
    (hUnorm : ∀ a ∈ U, ‖a‖ ≤ 2) (hUnezero : ∀ a ∈ U, a ≠ 0)
    (hV : IsOpen V) (hVne : V.Nonempty)
    (hVnorm : ∀ b ∈ V, ‖b‖ ≤ 2) (hVnezero : ∀ b ∈ V, b ≠ 0) :
    ∃ a ∈ U, ∃ b ∈ V,
      radialProj a ∉
        radialProjCubeMap g hne ''
          cubeLastFiberPrism (radialProjCubeMap g hne) (radialProj b) := by
  obtain ⟨a, haU, b, hbV, hab⟩ :=
    exists_scaled_aligned_pair_not_mem_range_in_open_sets
      (n := n) 4 g hg hdim hU hUne hV hVne
  refine ⟨a, haU, b, hbV, ?_⟩
  exact not_mem_cubeScaledAlignedPairMap_range_imp_not_mem_radial_prism_image
    4 (by norm_num) g hne a b (hUnezero a haU) (hVnezero b hbV)
    (fun y => norm_div_le_four_of_norm_le_two_of_half_le (hUnorm a haU) (hhalf y))
    (fun y => norm_div_le_four_of_norm_le_two_of_half_le (hVnorm b hbV) (hhalf y)) hab

end Submission
