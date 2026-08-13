/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.PairwiseGeneralPosition
import Submission.Model.SphereConnected

/-!
# Boundary-preserving pairwise general position

The translation argument in `Submission.Approximation.PairwiseGeneralPosition` separates two PL
images, but an ordinary translation changes the value on the boundary of a based cube.  This file
constructs an explicit cubical collar which tapers the translation back to zero on every boundary
face.  The perturbed image is contained in the translated core together with the line segment
joining its translated boundary value to the original basepoint.

The translated core is controlled by the pairwise collision-null theorem.  The collar segment is
controlled by the cone-null theorem from `Submission.Model.SphereConnected`.  Consequently the
whole boundary-preserving perturbation meets the second PL image only at the common basepoint.

## Main results

* `Submission.exists_translation_disjoint_ranges_and_segment_off_base`
* `Submission.basedInteriorTranslate`
* `Submission.exists_basedInteriorTranslate_inter_subset_singleton`
* `Submission.exists_homotopic_genLoops_range_inter_subset_singleton`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F] (μ : Measure F) [μ.IsAddHaarMeasure]

variable {n m N M : ℕ}

/-! ### Collision and collar null sets -/

/-- The translations making two entire grid-approximation ranges collide form a Haar-null set. -/
theorem addHaar_collisionTranslations_cubeGridAffineApprox_ranges
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) :
    μ (collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (Set.range (cubeGridAffineApprox m M h))) = 0 := by
  classical
  let D := (gridSimplices n N).filter Finset.Nonempty
  let E := (gridSimplices m M).filter Finset.Nonempty
  let C : Finset (Fin n → ℕ) → Finset (Fin m → ℕ) → Set F := fun S T =>
    collisionTranslations (gridSimplexHull N g S) (gridSimplexHull M h T)
  have hnull : ∀ S ∈ D, ∀ T ∈ E, μ (C S T) = 0 := by
    intro S hS T hT
    apply addHaar_collisionTranslations_of_finset_card_le μ
      (gridSimplexValues_nonempty g (Finset.mem_filter.mp hS).2)
      (gridSimplexValues_nonempty h (Finset.mem_filter.mp hT).2)
      (gridSimplexHull_subset_affineSpan_values g S)
      (gridSimplexHull_subset_affineSpan_values h T)
    have hScard := card_le_of_mem_gridSimplices (Finset.mem_filter.mp hS).1
    have hTcard := card_le_of_mem_gridSimplices (Finset.mem_filter.mp hT).1
    have hSvalues := card_gridSimplexValues_le (N := N) g S
    have hTvalues := card_gridSimplexValues_le (N := M) h T
    omega
  have hUnionNull : μ (⋃ S ∈ D, ⋃ T ∈ E, C S T) = 0 := by
    have hInner : ∀ S ∈ D, μ (⋃ T ∈ E, C S T) = 0 := by
      intro S hS
      have hsum : ∑ T ∈ E, μ (C S T) = 0 := Finset.sum_eq_zero (hnull S hS)
      exact nonpos_iff_eq_zero.mp (hsum ▸ measure_biUnion_finset_le E (C S))
    have hsum : ∑ S ∈ D, μ (⋃ T ∈ E, C S T) = 0 := Finset.sum_eq_zero hInner
    exact nonpos_iff_eq_zero.mp (hsum ▸ measure_biUnion_finset_le D fun S => ⋃ T ∈ E, C S T)
  refine measure_mono_null ?_ hUnionNull
  rintro t ⟨a, ha, b, hb, hab⟩
  have ha' := range_cubeGridAffineApprox_subset_nonempty_hulls hN g ha
  obtain ⟨S, hS, haS⟩ := Set.mem_iUnion₂.mp ha'
  have hb' := range_cubeGridAffineApprox_subset_nonempty_hulls hM h hb
  obtain ⟨T, hT, hbT⟩ := Set.mem_iUnion₂.mp hb'
  exact Set.mem_iUnion₂.mpr ⟨S, hS, Set.mem_iUnion₂.mpr ⟨T, hT, ⟨a, haS, b, hbT, hab⟩⟩⟩

/-- Translate a continuous map so that the chosen target point becomes zero. -/
def subConstContinuousMap (g : C(I^ Fin n, F)) (b : F) : C(I^ Fin n, F) :=
  ⟨fun y => g y - b, g.continuous.sub continuous_const⟩

omit [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
@[simp] theorem subConstContinuousMap_apply (g : C(I^ Fin n, F)) (b : F) (y : I^ Fin n) :
    subConstContinuousMap g b y = g y - b := rfl

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem cubeGridAffineApprox_subConst (hN : 1 ≤ N) (g : C(I^ Fin n, F)) (b : F)
    (y : I^ Fin n) :
    cubeGridAffineApprox n N (subConstContinuousMap g b) y =
      cubeGridAffineApprox n N g y - b := by
  rw [cubeGridAffineApprox_apply, cubeGridAffineApprox_apply]
  simp_rw [subConstContinuousMap_apply, smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, sum_gridCoeff_cube hN, one_smul]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem segment_vadd_eq (b t : F) :
    segment ℝ b (b + t) = (fun c : ℝ => b + c • t) '' Set.Icc 0 1 := by
  rw [segment_eq_image_lineMap]
  apply Set.image_congr
  intro c _
  simp [AffineMap.lineMap_apply, add_comm]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Avoiding the cone over the second grid image makes the open collar segment disjoint from
that image. -/
theorem disjoint_segment_sdiff_base_range_of_not_mem_gridConeSpan
    {h : C(I^ Fin m, F)} {b t : F}
    (hM : 1 ≤ M) (havoid : t ∉ gridConeSpan m M (subConstContinuousMap h b)) :
    Disjoint ((segment ℝ b (b + t)) \ {b})
      (Set.range (cubeGridAffineApprox m M h)) := by
  rw [Set.disjoint_left]
  intro x hxseg hxrange
  rcases hxseg with ⟨hxseg, hxb⟩
  rw [segment_vadd_eq] at hxseg
  obtain ⟨c, hc, rfl⟩ := hxseg
  obtain ⟨z, hz⟩ := hxrange
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hxb
    simp [hc0]
  have hcone := cubeGridAffineApprox_mem_gridConeSpan hM (subConstContinuousMap h b) z
  rw [cubeGridAffineApprox_subConst hM h b z, hz] at hcone
  have hct : c • t ∈ gridConeSpan m M (subConstContinuousMap h b) := by
    simpa using hcone
  have := smul_mem_gridConeSpan hct c⁻¹
  apply havoid
  simpa [hc0] using this

include μ in
/-- An arbitrarily small translation simultaneously separates the translated core from the
second PL image and separates the open collar segment from that image. -/
theorem exists_translation_disjoint_ranges_and_segment_off_base
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hn : 1 ≤ n)
    (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) (b : F)
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U,
      Disjoint ((fun x => x + t) '' Set.range (cubeGridAffineApprox n N g))
        (Set.range (cubeGridAffineApprox m M h)) ∧
      Disjoint ((segment ℝ b (b + t)) \ {b})
        (Set.range (cubeGridAffineApprox m M h)) := by
  let Z := collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (Set.range (cubeGridAffineApprox m M h)) ∪
    gridConeSpan m M (subConstContinuousMap h b)
  have hcollision : μ (collisionTranslations (Set.range (cubeGridAffineApprox n N g))
      (Set.range (cubeGridAffineApprox m M h))) = 0 :=
    addHaar_collisionTranslations_cubeGridAffineApprox_ranges μ hN hM hdim g h
  have hcone : μ (gridConeSpan m M (subConstContinuousMap h b)) = 0 :=
    addHaar_gridConeSpan μ (by omega) (subConstContinuousMap h b)
  have hZ : μ Z = 0 := measure_union_null hcollision hcone
  obtain ⟨t, htU, ht⟩ := exists_notMem_of_measure_zero μ ({()} : Finset Unit)
    (fun _ => Z) (fun _ _ => hZ) hU hUne
  have htZ : t ∉ Z := ht () (Finset.mem_singleton_self ())
  have htCollision : t ∉ collisionTranslations
      (Set.range (cubeGridAffineApprox n N g))
      (Set.range (cubeGridAffineApprox m M h)) := fun htmem => htZ (Or.inl htmem)
  have htCone : t ∉ gridConeSpan m M (subConstContinuousMap h b) :=
    fun htmem => htZ (Or.inr htmem)
  exact ⟨t, htU, not_mem_collisionTranslations_iff_disjoint.mp htCollision,
    disjoint_segment_sdiff_base_range_of_not_mem_gridConeSpan hM htCone⟩

/-- The image traced by translating `A` by `t` and joining its translated boundary value back
to `b`.  This is the set-level model for a boundary-preserving interior perturbation. -/
def basedTranslationTrace (A : Set F) (b t : F) : Set F :=
  ((fun x => x + t) '' A) ∪ segment ℝ b (b + t)

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem basedTranslationTrace_inter_subset_singleton
    {A B : Set F} {b t : F}
    (htrans : Disjoint ((fun x => x + t) '' A) B)
    (hseg : Disjoint ((segment ℝ b (b + t)) \ {b}) B) :
    basedTranslationTrace A b t ∩ B ⊆ {b} := by
  rintro x ⟨hxtrace, hxB⟩
  rcases hxtrace with hxtrans | hxsegmem
  · exact (Set.disjoint_left.mp htrans hxtrans hxB).elim
  · by_cases hxb : x = b
    · simp [hxb]
    · exact (Set.disjoint_left.mp hseg ⟨hxsegmem, by simpa⟩ hxB).elim

include μ in
theorem exists_basedTranslationTrace_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hn : 1 ≤ n)
    (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) (b : F)
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U,
      basedTranslationTrace (Set.range (cubeGridAffineApprox n N g)) b t ∩
        Set.range (cubeGridAffineApprox m M h) ⊆ {b} := by
  obtain ⟨t, htU, htrans, hseg⟩ :=
    exists_translation_disjoint_ranges_and_segment_off_base μ hN hM hn hdim g h b hU hUne
  exact ⟨t, htU, basedTranslationTrace_inter_subset_singleton htrans hseg⟩

/-! ### A boundary-preserving realization of the translation trace -/

/-- Rescale the middle third of the unit interval onto the whole interval, clamping the two
outer thirds to the endpoints. -/
noncomputable def collarCoord (x : I) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one (3 * (x : ℝ) - 1)

/-- A tent function which is zero at the endpoints and one throughout the middle third. -/
def collarWeightCoord (x : I) : ℝ :=
  min (min (3 * (x : ℝ)) (3 * (1 - (x : ℝ)))) 1

theorem continuous_collarCoord : Continuous collarCoord := by
  change Continuous (fun x : I => Set.projIcc (0 : ℝ) 1 zero_le_one (3 * (x : ℝ) - 1))
  fun_prop

theorem continuous_collarWeightCoord : Continuous collarWeightCoord := by
  change Continuous (fun x : I => min (min (3 * (x : ℝ)) (3 * (1 - (x : ℝ)))) 1)
  fun_prop

theorem collarWeightCoord_nonneg (x : I) : 0 ≤ collarWeightCoord x := by
  simp only [collarWeightCoord]
  exact le_min (le_min (mul_nonneg (by norm_num) x.2.1)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr x.2.2))) zero_le_one

theorem collarWeightCoord_le_one (x : I) : collarWeightCoord x ≤ 1 :=
  min_le_right _ _

@[simp] theorem collarWeightCoord_zero : collarWeightCoord (0 : I) = 0 := by
  norm_num [collarWeightCoord]

@[simp] theorem collarWeightCoord_one : collarWeightCoord (1 : I) = 0 := by
  norm_num [collarWeightCoord]

@[simp] theorem collarCoord_zero : collarCoord (0 : I) = 0 := by
  apply Subtype.ext
  norm_num [collarCoord, Set.coe_projIcc]

@[simp] theorem collarCoord_one : collarCoord (1 : I) = 1 := by
  apply Subtype.ext
  norm_num [collarCoord, Set.coe_projIcc]

theorem collarWeightCoord_eq_one_of_collarCoord_ne_endpoints {x : I}
    (h0 : collarCoord x ≠ 0) (h1 : collarCoord x ≠ 1) : collarWeightCoord x = 1 := by
  have hxlo : (1 / 3 : ℝ) < (x : ℝ) := by
    by_contra h
    have hx : 3 * (x : ℝ) - 1 ≤ 0 := by
      have := le_of_not_gt h
      linarith
    apply h0
    exact Set.projIcc_of_le_left zero_le_one hx
  have hxhi : (x : ℝ) < 2 / 3 := by
    by_contra h
    have hx : 1 ≤ 3 * (x : ℝ) - 1 := by
      have := le_of_not_gt h
      linarith
    apply h1
    exact Set.projIcc_of_right_le zero_le_one hx
  rw [collarWeightCoord, min_eq_right]
  exact le_min (by linarith) (by linarith)

/-- Coordinatewise collar retraction of the cube. -/
noncomputable def cubeCollarRetraction (y : I^ Fin n) : I^ Fin n :=
  fun j => collarCoord (y j)

/-- Product of the coordinate tent functions. -/
def cubeCollarWeight (y : I^ Fin n) : ℝ :=
  ∏ j, collarWeightCoord (y j)

theorem continuous_cubeCollarRetraction :
    Continuous (cubeCollarRetraction : (I^ Fin n) → (I^ Fin n)) :=
  by
    apply continuous_pi
    intro j
    have hj : Continuous (fun y : I^ Fin n => y j) := continuous_apply j
    exact continuous_collarCoord.comp hj

theorem continuous_cubeCollarWeight : Continuous (cubeCollarWeight : (I^ Fin n) → ℝ) :=
  by
    apply continuous_finsetProd
    intro j _
    have hj : Continuous (fun y : I^ Fin n => y j) := continuous_apply j
    exact continuous_collarWeightCoord.comp hj

theorem cubeCollarWeight_mem_Icc (y : I^ Fin n) : cubeCollarWeight y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Finset.prod_nonneg fun j _ => collarWeightCoord_nonneg (y j),
    Finset.prod_le_one (fun j _ => collarWeightCoord_nonneg (y j))
      (fun j _ => collarWeightCoord_le_one (y j))⟩

theorem cubeCollarWeight_eq_zero_of_mem_boundary {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : cubeCollarWeight y = 0 := by
  obtain ⟨j, hj⟩ := hy
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rcases hj with hj | hj <;> simp [hj]

theorem cubeCollarRetraction_mem_boundary_of_mem_boundary {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : cubeCollarRetraction y ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j, hj.elim (fun h => Or.inl (by simp [cubeCollarRetraction, h]))
    (fun h => Or.inr (by simp [cubeCollarRetraction, h]))⟩

theorem cubeCollarRetraction_mem_boundary_of_weight_ne_one {y : I^ Fin n}
    (hy : cubeCollarWeight y ≠ 1) : cubeCollarRetraction y ∈ Cube.boundary (Fin n) := by
  by_contra hboundary
  apply hy
  apply Finset.prod_eq_one
  intro j _
  apply collarWeightCoord_eq_one_of_collarCoord_ne_endpoints
  · intro hj
    apply hboundary
    exact ⟨j, Or.inl hj⟩
  · intro hj
    apply hboundary
    exact ⟨j, Or.inr hj⟩

/-- Translate the PL approximation on the core of the cube and taper the translation to zero
through the collar. -/
noncomputable def basedInteriorTranslate (N : ℕ) (g : C(I^ Fin n, F)) (t : F) :
    C(I^ Fin n, F) where
  toFun y := cubeGridAffineApprox n N g (cubeCollarRetraction y) + cubeCollarWeight y • t
  continuous_toFun :=
    ((cubeGridAffineApprox n N g).continuous.comp continuous_cubeCollarRetraction).add
      (continuous_cubeCollarWeight.smul continuous_const)

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
@[simp] theorem basedInteriorTranslate_apply (g : C(I^ Fin n, F)) (t : F) (y : I^ Fin n) :
    basedInteriorTranslate N g t y =
      cubeGridAffineApprox n N g (cubeCollarRetraction y) + cubeCollarWeight y • t := rfl

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem basedInteriorTranslate_eq_of_mem_boundary (hN : 1 ≤ N)
    (g : C(I^ Fin n, F)) {b t : F}
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b) {y : I^ Fin n}
    (hy : y ∈ Cube.boundary (Fin n)) : basedInteriorTranslate N g t y = b := by
  rw [basedInteriorTranslate_apply,
    cubeGridAffineApprox_eq_of_mem_boundary hN g hg
      (cubeCollarRetraction_mem_boundary_of_mem_boundary hy),
    cubeCollarWeight_eq_zero_of_mem_boundary hy, zero_smul, add_zero]

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem range_basedInteriorTranslate_subset_trace (hN : 1 ≤ N)
    (g : C(I^ Fin n, F)) {b t : F}
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b) :
    Set.range (basedInteriorTranslate N g t) ⊆
      basedTranslationTrace (Set.range (cubeGridAffineApprox n N g)) b t := by
  rintro _ ⟨y, rfl⟩
  by_cases hw : cubeCollarWeight y = 1
  · apply Or.inl
    refine ⟨cubeGridAffineApprox n N g (cubeCollarRetraction y),
      ⟨cubeCollarRetraction y, rfl⟩, ?_⟩
    simp [basedInteriorTranslate_apply, hw]
  · apply Or.inr
    rw [basedInteriorTranslate_apply,
      cubeGridAffineApprox_eq_of_mem_boundary hN g hg
        (cubeCollarRetraction_mem_boundary_of_weight_ne_one hw)]
    rw [segment_vadd_eq]
    exact ⟨cubeCollarWeight y, cubeCollarWeight_mem_Icc y, rfl⟩

include μ in
/-- The collar perturbation realizes the trace separation while remaining exactly based. -/
theorem exists_basedInteriorTranslate_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hn : 1 ≤ n)
    (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) (b : F)
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b)
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U,
      (∀ y ∈ Cube.boundary (Fin n), basedInteriorTranslate N g t y = b) ∧
      Set.range (basedInteriorTranslate N g t) ∩
        Set.range (cubeGridAffineApprox m M h) ⊆ {b} := by
  obtain ⟨t, htU, ht⟩ :=
    exists_basedTranslationTrace_inter_subset_singleton μ hN hM hn hdim g h b hU hUne
  refine ⟨t, htU, fun y hy => basedInteriorTranslate_eq_of_mem_boundary hN g hg hy, ?_⟩
  exact fun _ hx => ht ⟨range_basedInteriorTranslate_subset_trace hN g hg hx.1, hx.2⟩

/-! ### Based homotopy representatives -/

/-- The straight-line homotopy from a based cube map to its boundary-preserving interior
translation. -/
noncomputable def basedInteriorTranslateHomotopy (hN : 1 ≤ N)
    (g : C(I^ Fin n, F)) {b : F}
    (hg : ∀ z ∈ Cube.boundary (Fin n), g z = b) (t : F) :
    ContinuousMap.HomotopyRel g (basedInteriorTranslate N g t) (Cube.boundary (Fin n)) where
  toFun p := (1 - (p.1 : ℝ)) • g p.2 + (p.1 : ℝ) • basedInteriorTranslate N g t p.2
  continuous_toFun := by fun_prop
  map_zero_left y := by simp
  map_one_left y := by simp
  prop' s y hy := by
    change (1 - (s : ℝ)) • g y + (s : ℝ) • basedInteriorTranslate N g t y = g y
    rw [hg y hy, basedInteriorTranslate_eq_of_mem_boundary hN g hg hy]
    module

/-- The grid approximation of a generalized loop, bundled again as a generalized loop. -/
noncomputable def cubeGridAffineApproxGenLoop (N : ℕ) (hN : 1 ≤ N)
    {b : F} (g : Ω^ (Fin n) F b) : Ω^ (Fin n) F b :=
  ⟨cubeGridAffineApprox n N g.1,
    fun _ hy => cubeGridAffineApprox_eq_of_mem_boundary hN g.1
      (_root_.GenLoop.boundary g) hy⟩

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Grid approximation does not change the based homotopy class in a vector space. -/
theorem genLoopHomotopic_cubeGridAffineApprox (N : ℕ) (hN : 1 ≤ N)
    {b : F} (g : Ω^ (Fin n) F b) :
    _root_.GenLoop.Homotopic g (cubeGridAffineApproxGenLoop N hN g) := by
  refine ⟨{
    toFun := cubeGridAffineApproxHomotopy n N g.1
    continuous_toFun := (cubeGridAffineApproxHomotopy n N g.1).continuous
    map_zero_left := cubeGridAffineApproxHomotopy_zero g.1
    map_one_left := cubeGridAffineApproxHomotopy_one g.1
    prop' := ?_ }⟩
  intro s y hy
  change (1 - (s : ℝ)) • g y + (s : ℝ) • cubeGridAffineApprox n N g.1 y = g y
  rw [_root_.GenLoop.boundary g y hy,
    cubeGridAffineApprox_eq_of_mem_boundary hN g.1 (_root_.GenLoop.boundary g) hy]
  module

/-- Boundary-preserving interior translation of a generalized loop. -/
noncomputable def basedInteriorTranslateGenLoop (N : ℕ) (hN : 1 ≤ N)
    {b : F} (g : Ω^ (Fin n) F b) (t : F) : Ω^ (Fin n) F b :=
  ⟨basedInteriorTranslate N g.1 t,
    fun _ hy => basedInteriorTranslate_eq_of_mem_boundary hN g.1
      (_root_.GenLoop.boundary g) hy⟩

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Boundary-preserving interior translation does not change the based homotopy class. -/
theorem genLoopHomotopic_basedInteriorTranslate (N : ℕ) (hN : 1 ≤ N)
    {b : F} (g : Ω^ (Fin n) F b) (t : F) :
    _root_.GenLoop.Homotopic g (basedInteriorTranslateGenLoop N hN g t) :=
  ⟨basedInteriorTranslateHomotopy hN g.1 (_root_.GenLoop.boundary g) t⟩

include μ in
/-- **Based pairwise general position in a vector space.**  If two positive-dimensional based
cube maps have source dimensions whose sum is smaller than the ambient dimension, they have
based-homotopic representatives whose images meet only at the basepoint. -/
theorem exists_homotopic_genLoops_range_inter_subset_singleton
    (hn : 1 ≤ n) (hdim : n + m + 1 ≤ finrank ℝ F) {b : F}
    (f : Ω^ (Fin n) F b) (g : Ω^ (Fin m) F b) :
    ∃ (f' : Ω^ (Fin n) F b) (g' : Ω^ (Fin m) F b),
      _root_.GenLoop.Homotopic f f' ∧ _root_.GenLoop.Homotopic g g' ∧
      Set.range f' ∩ Set.range g' ⊆ {b} := by
  have hmesh : 1 ≤ 1 := le_rfl
  obtain ⟨t, -, -, hinter⟩ := exists_basedInteriorTranslate_inter_subset_singleton μ
    hmesh hmesh hn hdim f.1 g.1 b (_root_.GenLoop.boundary f) isOpen_univ
      Set.univ_nonempty
  let f' := basedInteriorTranslateGenLoop 1 hmesh f t
  let g' := cubeGridAffineApproxGenLoop 1 hmesh g
  refine ⟨f', g', genLoopHomotopic_basedInteriorTranslate 1 hmesh f t,
    genLoopHomotopic_cubeGridAffineApprox 1 hmesh g, ?_⟩
  simpa [f', g', basedInteriorTranslateGenLoop, cubeGridAffineApproxGenLoop] using hinter

end Submission
