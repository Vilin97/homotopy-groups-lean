/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.RelativeSphere

/-!
# General position relative to a varying cube boundary

For a collar perturbation which is fixed only setwise on the boundary, the collar starts at a
varying PL boundary value rather than at one constant basepoint. A radial collision then says
that a nonzero scalar multiple of the translation joins the first boundary image to the cone
over the second image.

This file proves that these scaled collision translations are Haar-null. The sharp dimension
count uses the fact that an active Kuhn simplex on a face of an `n`-cube has at most `n`, rather
than `n+1`, vertices. Avoiding the resulting null set extends radial separation already known on
the boundary across the whole cube.

## Main results

* `Submission.card_activeVerts_le_of_mem_boundary`
* `Submission.addHaar_scaledCollisionTranslations_cubeGridBoundaryRange_gridConeSpan`
* `Submission.exists_translation_disjoint_range_gridConeSpan_and_boundaryScaled`
* `Submission.exists_boundaryInteriorTranslate_radial_inter_subset_singleton`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F]
variable (μ : Measure F) [μ.IsAddHaarMeasure]

variable {n m N M : ℕ}

theorem card_activeVerts_le_of_mem_boundary (hN : 1 ≤ N) {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : (activeVerts N y).card ≤ n := by
  classical
  obtain ⟨j, hj⟩ := hy
  set J : Finset (Fin n) := Finset.univ.erase j with hJ
  set yc : Fin n → ℝ := fun i => (y i : ℝ) with hyc
  obtain ⟨w, hw, hwmax⟩ :=
    (activeVerts N y).exists_max_image (fun v => gridLo N v yc) (activeVerts_nonempty hN y)
  have hcmp : ∀ v ∈ activeVerts N y, ∀ i, w i ≤ v i ∧ v i ≤ w i + 1 := fun v hv i =>
    le_of_gridCoeff_pos_of_gridLo_le (mem_activeVerts.mp hv).2 (mem_activeVerts.mp hw).2
      (hwmax v hv) i
  have hfix : ∀ v ∈ activeVerts N y, v j = w j := by
    intro v hv
    have hvmem := (mem_activeVerts.mp hv).1
    have hwmem := (mem_activeVerts.mp hw).1
    have hvface : gridVertex N v j = gridVertex N w j := by
      rcases hj with hj | hj
      · rw [gridVertex_eq_zero_of_gridCoeff_pos hN hj hv,
          gridVertex_eq_zero_of_gridCoeff_pos hN hj hw]
      · rw [gridVertex_eq_one_of_gridCoeff_pos hN hj hv,
          gridVertex_eq_one_of_gridCoeff_pos hN hj hw]
    have hvface' := congrArg Subtype.val hvface
    rw [coe_gridVertex hN hvmem j, coe_gridVertex hN hwmem j] at hvface'
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hmul := (div_eq_div_iff hN0 hN0).mp hvface'
    exact_mod_cast mul_right_cancel₀ hN0 hmul
  have hmaps : Set.MapsTo (fun v : Fin n → ℕ => ∑ i ∈ J, v i) (activeVerts N y)
      (Finset.Icc (∑ i ∈ J, w i) (∑ i ∈ J, w i + J.card)) := by
    intro v hv
    refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr
      ⟨Finset.sum_le_sum fun i hi => (hcmp v hv i).1, ?_⟩)
    calc
      ∑ i ∈ J, v i ≤ ∑ i ∈ J, (w i + 1) :=
        Finset.sum_le_sum fun i hi => (hcmp v hv i).2
      _ = ∑ i ∈ J, w i + J.card := by
        rw [Finset.sum_add_distrib]
        simp
  have hchain : ∀ a ∈ activeVerts N y, ∀ b ∈ activeVerts N y,
      gridLo N a yc ≤ gridLo N b yc →
      (∑ i ∈ J, a i) = (∑ i ∈ J, b i) → a = b := by
    intro a ha b hb hle hsum
    have hba : ∀ i, b i ≤ a i := fun i =>
      (le_of_gridCoeff_pos_of_gridLo_le (mem_activeVerts.mp ha).2
        (mem_activeVerts.mp hb).2 hle i).1
    funext i
    by_cases hij : i = j
    · subst i
      exact (hfix a ha).trans (hfix b hb).symm
    · by_contra hne
      have hlt : b i < a i := lt_of_le_of_ne (hba i) (Ne.symm hne)
      have hiJ : i ∈ J := by simp [J, hij]
      have hsum' : (∑ i ∈ J, b i) < ∑ i ∈ J, a i :=
        Finset.sum_lt_sum (fun r hr => hba r) ⟨i, hiJ, hlt⟩
      omega
  have hinj : Set.InjOn (fun v : Fin n → ℕ => ∑ i ∈ J, v i) (activeVerts N y) := by
    intro a ha b hb hsum
    rcases le_total (gridLo N a yc) (gridLo N b yc) with h | h
    · exact hchain a ha b hb h hsum
    · exact (hchain b hb a ha h hsum.symm).symm
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hJcard : J.card = n - 1 := by
    change (Finset.univ.erase j).card = n - 1
    rw [Finset.card_erase_of_mem hjmem, Finset.card_univ, Fintype.card_fin]
  calc
    (activeVerts N y).card
        ≤ (Finset.Icc (∑ i ∈ J, w i) (∑ i ∈ J, w i + J.card)).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = J.card + 1 := by rw [Nat.card_Icc]; omega
    _ = n := by
      rw [hJcard]
      have : 1 ≤ n := Fin.pos_iff_nonempty.mpr ⟨j⟩
      omega

/-! ### Scaled collision sets -/

/-- Translations whose nonzero scalar multiple moves a point of `A` onto a point of `B`. -/
def scaledCollisionTranslations (A B : Set F) : Set F :=
  {t | ∃ a ∈ A, ∃ b ∈ B, ∃ c : ℝ, c ≠ 0 ∧ a + c • t = b}

theorem addHaar_scaledCollisionTranslations_of_card_le
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (p : ι → F) (q : κ → F) {A B : Set F}
    (hA : A ⊆ affineSpan ℝ (Set.range p))
    (hB : B ⊆ affineSpan ℝ (Set.range q))
    (hcard : Fintype.card ι + Fintype.card κ ≤ finrank ℝ F) :
    μ (scaledCollisionTranslations A B) = 0 := by
  let r : Sum ι κ → F := Sum.elim p q
  let R := affineSpan ℝ (Set.range r)
  let W : AffineSubspace ℝ F := AffineSubspace.mk' 0 R.direction
  have hpr : Set.range p ⊆ Set.range r := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  have hqr : Set.range q ⊆ Set.range r := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inr j, rfl⟩
  have hAR : A ⊆ R := fun _ ha => affineSpan_mono ℝ hpr (hA ha)
  have hBR : B ⊆ R := fun _ hb => affineSpan_mono ℝ hqr (hB hb)
  refine addHaar_of_subset_affineSubspace μ (W := W) ?_ ?_
  · intro hW
    have hdir : R.direction = (⊤ : Submodule ℝ F) := by
      have := congrArg AffineSubspace.direction hW
      simpa [W] using this
    have hrank : finrank ℝ R.direction + 1 ≤ Fintype.card (Sum ι κ) := by
      dsimp only [R]
      rw [direction_affineSpan]
      exact finrank_vectorSpan_range_add_one_le ℝ r
    rw [hdir, finrank_top, Fintype.card_sum] at hrank
    omega
  · rintro t ⟨a, ha, b, hb, c, hc, hab⟩
    change t - 0 ∈ R.direction
    have hdif : b - a ∈ R.direction := R.vsub_mem_direction (hBR hb) (hAR ha)
    have heq : t = c⁻¹ • (b - a) := by
      have hct : c • t = b - a := by rw [← hab]; module
      rw [← hct, smul_smul]
      simp [hc]
    simpa [heq] using R.direction.smul_mem c⁻¹ hdif

/-! ### Boundary pieces of a grid approximation -/

/-- Grid simplices small enough to occur on a boundary face of an `n`-cube. -/
def gridBoundarySimplices (n N : ℕ) : Finset (Finset (Fin n → ℕ)) :=
  (gridSimplices n N).filter fun S => S.Nonempty ∧ S.card ≤ n

theorem activeVerts_mem_gridBoundarySimplices (hN : 1 ≤ N) {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) :
    activeVerts N y ∈ gridBoundarySimplices n N := by
  exact Finset.mem_filter.mpr
    ⟨activeVerts_mem_gridSimplices hN y, activeVerts_nonempty hN y,
      card_activeVerts_le_of_mem_boundary hN hy⟩

/-- The image of the cube boundary under a grid approximation. -/
def cubeGridAffineApproxBoundaryRange
    (n N : ℕ) (g : C(I^ Fin n, F)) : Set F :=
  cubeGridAffineApprox n N g '' Cube.boundary (Fin n)

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem cubeGridAffineApproxBoundaryRange_subset_hulls (hN : 1 ≤ N)
    (g : C(I^ Fin n, F)) :
    cubeGridAffineApproxBoundaryRange n N g ⊆
      ⋃ S ∈ gridBoundarySimplices n N, gridSimplexHull N g S := by
  rintro _ ⟨y, hy, rfl⟩
  exact Set.mem_iUnion₂.mpr
    ⟨activeVerts N y, activeVerts_mem_gridBoundarySimplices hN hy,
      cubeGridAffineApprox_mem_convexHull hN g y⟩

include μ in
/-- Scaled collisions between the boundary of one grid approximation and the cone over a
second grid approximation form a Haar-null set in the expected dimension range. -/
theorem addHaar_scaledCollisionTranslations_cubeGridBoundaryRange_gridConeSpan
    (hN : 1 ≤ N) (hdim : n + m + 2 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) :
    μ (scaledCollisionTranslations (cubeGridAffineApproxBoundaryRange n N g)
      (gridConeSpan m M h)) = 0 := by
  classical
  let D := gridBoundarySimplices n N
  let E := gridSimplices m M
  let C : Finset (Fin n → ℕ) → Finset (Fin m → ℕ) → Set F := fun S T =>
    scaledCollisionTranslations (gridSimplexHull N g S)
      (affineSpan ℝ (Set.range (gridConePoints M h T)) : Set F)
  have hnull : ∀ S ∈ D, ∀ T ∈ E, μ (C S T) = 0 := by
    intro S hS T hT
    have hSdata := Finset.mem_filter.mp hS
    letI : Nonempty (gridSimplexValues N g S) :=
      (gridSimplexValues_nonempty g hSdata.2.1).to_subtype
    apply addHaar_scaledCollisionTranslations_of_card_le μ
      (p := fun x : gridSimplexValues N g S => (x : F))
      (q := gridConePoints M h T)
    · simpa [Subtype.range_coe_subtype, Finset.setOf_mem] using
        (gridSimplexHull_subset_affineSpan_values (N := N) g S)
    · exact Set.Subset.rfl
    · rw [Fintype.card_coe, Fintype.card_option, Fintype.card_coe]
      have hSvalues := card_gridSimplexValues_le (N := N) g S
      have hTcard := card_le_of_mem_gridSimplices hT
      omega
  have hUnionNull : μ (⋃ S ∈ D, ⋃ T ∈ E, C S T) = 0 := by
    have hInner : ∀ S ∈ D, μ (⋃ T ∈ E, C S T) = 0 := by
      intro S hS
      have hsum : ∑ T ∈ E, μ (C S T) = 0 := Finset.sum_eq_zero (hnull S hS)
      exact nonpos_iff_eq_zero.mp (hsum ▸ measure_biUnion_finset_le E (C S))
    have hsum : ∑ S ∈ D, μ (⋃ T ∈ E, C S T) = 0 := Finset.sum_eq_zero hInner
    exact nonpos_iff_eq_zero.mp
      (hsum ▸ measure_biUnion_finset_le D fun S => ⋃ T ∈ E, C S T)
  refine measure_mono_null ?_ hUnionNull
  rintro t ⟨a, ha, b, hb, c, hc, hab⟩
  have ha' := cubeGridAffineApproxBoundaryRange_subset_hulls hN g ha
  obtain ⟨S, hS, haS⟩ := Set.mem_iUnion₂.mp ha'
  obtain ⟨T, hT, hbT⟩ := Set.mem_iUnion₂.mp hb
  exact Set.mem_iUnion₂.mpr ⟨S, hS,
    Set.mem_iUnion₂.mpr ⟨T, hT, ⟨a, haS, b, hbT, c, hc, hab⟩⟩⟩

include μ in
/-- Choose a small translation which separates the core of one grid approximation from every
ray through a second one and simultaneously avoids every scaled collision generated by the
first grid boundary. -/
theorem exists_translation_disjoint_range_gridConeSpan_and_boundaryScaled
    (hN : 1 ≤ N) (hdim : n + m + 2 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F))
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U,
      Disjoint ((fun x => x + t) '' Set.range (cubeGridAffineApprox n N g))
        (gridConeSpan m M h) ∧
      t ∉ scaledCollisionTranslations (cubeGridAffineApproxBoundaryRange n N g)
        (gridConeSpan m M h) := by
  let Z := collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (gridConeSpan m M h) ∪
    scaledCollisionTranslations (cubeGridAffineApproxBoundaryRange n N g)
      (gridConeSpan m M h)
  have hcore : μ (collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (gridConeSpan m M h)) = 0 :=
    addHaar_collisionTranslations_cubeGridAffineApprox_range_gridConeSpan μ hN hdim g h
  have hboundary : μ (scaledCollisionTranslations
      (cubeGridAffineApproxBoundaryRange n N g) (gridConeSpan m M h)) = 0 :=
    addHaar_scaledCollisionTranslations_cubeGridBoundaryRange_gridConeSpan μ hN hdim g h
  have hZ : μ Z = 0 := measure_union_null hcore hboundary
  obtain ⟨t, htU, ht⟩ := exists_notMem_of_measure_zero μ ({()} : Finset Unit)
    (fun _ => Z) (fun _ _ => hZ) hU hUne
  have htZ : t ∉ Z := ht () (Finset.mem_singleton_self ())
  have htCore : t ∉ collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (gridConeSpan m M h) := fun htmem => htZ (Or.inl htmem)
  exact ⟨t, htU, not_mem_collisionTranslations_iff_disjoint.mp htCore,
    fun htmem => htZ (Or.inr htmem)⟩

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- If the radial boundary image already meets the second radial PL image only at `b`, a collar
translation avoiding the core and scaled-boundary collision sets extends this separation over
the whole first cube. -/
theorem radialProj_boundaryInteriorTranslate_inter_subset_singleton
    (hM : 1 ≤ M)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) {b t : F}
    (hne : ∀ y, basedInteriorTranslate N g t y ≠ 0)
    (hboundary : radialProj '' cubeGridAffineApproxBoundaryRange n N g ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b})
    (hcore : Disjoint
      ((fun x => x + t) '' Set.range (cubeGridAffineApprox n N g))
      (gridConeSpan m M h))
    (hscaled : t ∉ scaledCollisionTranslations
      (cubeGridAffineApproxBoundaryRange n N g) (gridConeSpan m M h)) :
    Set.range (fun y => radialProj (basedInteriorTranslate N g t y)) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  rintro q ⟨hqfirst, hqsecond⟩
  obtain ⟨y, hy⟩ := hqfirst
  obtain ⟨z, hz⟩ := hqsecond
  have heq : radialProj (basedInteriorTranslate N g t y) =
      radialProj (cubeGridAffineApprox m M h z) := hy.trans hz.symm
  have hxcone : basedInteriorTranslate N g t y ∈ gridConeSpan m M h :=
    mem_gridConeSpan_of_radialProj_eq_cubeGridAffineApprox hM h (hne y) z heq
  by_cases hw : cubeCollarWeight y = 1
  · have hxcore : basedInteriorTranslate N g t y ∈
        (fun x => x + t) '' Set.range (cubeGridAffineApprox n N g) := by
      refine ⟨cubeGridAffineApprox n N g (cubeCollarRetraction y),
        ⟨cubeCollarRetraction y, rfl⟩, ?_⟩
      simp [basedInteriorTranslate_apply, hw]
    exact (Set.disjoint_left.mp hcore hxcore hxcone).elim
  · have hRboundary := cubeCollarRetraction_mem_boundary_of_weight_ne_one hw
    let a := cubeGridAffineApprox n N g (cubeCollarRetraction y)
    have ha : a ∈ cubeGridAffineApproxBoundaryRange n N g :=
      ⟨cubeCollarRetraction y, hRboundary, rfl⟩
    by_cases hw0 : cubeCollarWeight y = 0
    · apply hboundary
      constructor
      · refine ⟨a, ha, ?_⟩
        rw [← hy]
        simp [basedInteriorTranslate_apply, a, hw0]
      · exact ⟨z, hz⟩
    · exfalso
      apply hscaled
      refine ⟨a, ha, basedInteriorTranslate N g t y, hxcone,
        cubeCollarWeight y, hw0, ?_⟩
      exact basedInteriorTranslate_apply g t y

include μ in
/-- Boundary-relative radial PL general position. Provided the unperturbed radial boundary is
already separated from the second radial image, an arbitrarily small collar translation extends
that separation to the whole first cube without changing its radial boundary image as a set. -/
theorem exists_boundaryInteriorTranslate_radial_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hdim : n + m + 2 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) {b : F}
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox n N g y) (g y) ≤ 1 / 2)
    (hboundary : radialProj '' cubeGridAffineApproxBoundaryRange n N g ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b}) :
    ∃ t : F, ‖t‖ < 1 / 2 ∧
      (∀ y, basedInteriorTranslate N g t y ≠ 0) ∧
      Set.range (fun y => radialProj (basedInteriorTranslate N g t y)) ∩
        Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  obtain ⟨t, htball, hcore, hscaled⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_boundaryScaled μ hN hdim g h
      Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)⟩
  have ht : ‖t‖ < 1 / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  have hHne : ∀ p, basedInteriorTranslateRadialHomotopyAmbient N g t p ≠ 0 :=
    basedInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
      g hgnorm hdist ht
  have hne : ∀ y, basedInteriorTranslate N g t y ≠ 0 := by
    intro y
    simpa using hHne (1, y)
  exact ⟨t, ht, hne,
    radialProj_boundaryInteriorTranslate_inter_subset_singleton hM g h hne
      hboundary hcore hscaled⟩

end Submission
