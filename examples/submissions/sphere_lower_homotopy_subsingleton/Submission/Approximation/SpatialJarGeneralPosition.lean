/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.VaryingJarGeneralPosition

/-!
# Stable general position for a whole relative sphere homotopy

A time-first relative homotopy has a constant jar only in its spatial coordinates; its two time
faces are the varying endpoint maps. We therefore construct a collar which retracts and tapers
only the spatial coordinates while leaving homotopy time unchanged.

Away from that spatial jar the full finite PL homotopy image is translated. In the collar the
retracted PL value is the sphere basepoint, so the only additional radial obstruction is the
usual basepoint segment. Both obstruction sets are Haar-null in the exact stable dimension
range. A translation of norm below `1/8` separates the entire homotopy while radial projection
preserves the upper-cap condition and fixes its spatial jar.

## Main results

* `Submission.exists_spatialJarInteriorTranslate_radial_inter_subset_singleton`
* `Submission.relativeSpherePLHomotopyApproximation_approxSlice_homotopic_spatialJarTranslate`
* `Submission.exists_relativeSphereSpatialJarGeneralPositionHomotopy`
* `Submission.exists_homotopic_relativeSphereHomotopy_avoiding_sphereGenLoop`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {k m N M : ℕ}

/-! ### A collar only in the spatial coordinates of a homotopy cube -/

/-- Retract only the spatial coordinates of a time-first homotopy cube. -/
noncomputable def spatialCubeCollarRetraction (y : I^ Fin (k + 2)) : I^ Fin (k + 2) :=
  Fin.cons (y 0) (cubeCollarRetraction fun i => y i.succ)

theorem continuous_spatialCubeCollarRetraction :
    Continuous (spatialCubeCollarRetraction : (I^ Fin (k + 2)) → I^ Fin (k + 2)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [spatialCubeCollarRetraction] using
      (continuous_apply (0 : Fin (k + 2)))
  · intro j
    change Continuous fun y : I^ Fin (k + 2) =>
      collarCoord (y j.succ)
    exact continuous_collarCoord.comp (continuous_apply j.succ)

@[simp] theorem spatialCubeCollarRetraction_apply_zero (y : I^ Fin (k + 2)) :
    spatialCubeCollarRetraction y 0 = y 0 :=
  rfl

theorem spatialCubeCollarRetraction_tail (y : I^ Fin (k + 2)) :
    (fun i : Fin (k + 1) => spatialCubeCollarRetraction y i.succ) =
      cubeCollarRetraction (fun i => y i.succ) :=
  rfl

/-- The one-sided spatial jar collar weight, leaving the time coordinate out of the product. -/
def spatialCubeJarCollarWeight (y : I^ Fin (k + 2)) : ℝ :=
  cubeJarCollarWeight (fun i : Fin (k + 1) => y i.succ)

theorem continuous_spatialCubeJarCollarWeight :
    Continuous (spatialCubeJarCollarWeight : (I^ Fin (k + 2)) → ℝ) :=
  continuous_cubeJarCollarWeight.comp (by fun_prop)

theorem spatialCubeJarCollarWeight_mem_Icc (y : I^ Fin (k + 2)) :
    spatialCubeJarCollarWeight y ∈ Set.Icc (0 : ℝ) 1 :=
  cubeJarCollarWeight_mem_Icc _

theorem spatialCubeJarCollarWeight_eq_zero_of_tail_mem_boundaryJar
    {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ⊔I^(k + 1)) :
    spatialCubeJarCollarWeight y = 0 :=
  cubeJarCollarWeight_eq_zero_of_mem_boundaryJar hy

theorem spatialCubeCollarRetraction_tail_mem_boundaryJar_of_weight_ne_one
    {y : I^ Fin (k + 2)} (hy : spatialCubeJarCollarWeight y ≠ 1) :
    (fun i : Fin (k + 1) => spatialCubeCollarRetraction y i.succ) ∈
      ⊔I^(k + 1) :=
  cubeCollarRetraction_mem_boundaryJar_of_jarWeight_ne_one hy

/-! ### The spatial-jar translation trace -/

/-- Translate the PL core of a homotopy cube while tapering only along its spatial jar. -/
noncomputable def spatialJarInteriorTranslate
    (N : ℕ) (g : C(I^ Fin (k + 2), F)) (t : F) : C(I^ Fin (k + 2), F) where
  toFun y := cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y) +
    spatialCubeJarCollarWeight y • t
  continuous_toFun :=
    ((cubeGridAffineApprox (k + 2) N g).continuous.comp
      continuous_spatialCubeCollarRetraction).add
      (continuous_spatialCubeJarCollarWeight.smul continuous_const)

theorem spatialJarInteriorTranslate_apply
    (g : C(I^ Fin (k + 2), F)) (t : F) (y : I^ Fin (k + 2)) :
    spatialJarInteriorTranslate N g t y =
      cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y) +
        spatialCubeJarCollarWeight y • t :=
  rfl

theorem range_spatialJarInteriorTranslate_subset_trace
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 2), F)) {b t : F}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b) :
    Set.range (spatialJarInteriorTranslate N g t) ⊆
      basedTranslationTrace
        (Set.range (cubeGridAffineApprox (k + 2) N g)) b t := by
  rintro _ ⟨y, rfl⟩
  by_cases hw : spatialCubeJarCollarWeight y = 1
  · apply Or.inl
    refine ⟨cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y),
      ⟨spatialCubeCollarRetraction y, rfl⟩, ?_⟩
    rw [spatialJarInteriorTranslate_apply, hw, one_smul]
  · apply Or.inr
    rw [spatialJarInteriorTranslate_apply,
      cubeGridAffineApprox_eq_of_tail_mem_boundaryJar hN g hg
        (spatialCubeCollarRetraction_tail_mem_boundaryJar_of_weight_ne_one hw)]
    rw [segment_vadd_eq]
    exact ⟨spatialCubeJarCollarWeight y,
      spatialCubeJarCollarWeight_mem_Icc y, rfl⟩

/-- A sufficiently small spatial-jar translation stays nonzero. -/
theorem spatialJarInteriorTranslate_ne_zero_of_dist_le_half
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 2), F)) {b t : F}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b)
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 2) N g y) (g y) ≤ 1 / 2)
    (hb : ‖b‖ = 1) (ht : ‖t‖ < 1 / 2) :
    ∀ y, spatialJarInteriorTranslate N g t y ≠ 0 := by
  intro y hyzero
  by_cases hw : spatialCubeJarCollarWeight y = 1
  · have hclose : dist (spatialJarInteriorTranslate N g t y)
        (g (spatialCubeCollarRetraction y)) < 1 := by
      calc
        dist (spatialJarInteriorTranslate N g t y)
              (g (spatialCubeCollarRetraction y)) ≤
            dist (spatialJarInteriorTranslate N g t y)
                (cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y)) +
              dist (cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y))
                (g (spatialCubeCollarRetraction y)) := dist_triangle _ _ _
        _ = ‖t‖ + dist
              (cubeGridAffineApprox (k + 2) N g (spatialCubeCollarRetraction y))
              (g (spatialCubeCollarRetraction y)) := by
            rw [spatialJarInteriorTranslate_apply, hw, one_smul, dist_eq_norm]
            simp
        _ < 1 := by linarith [hdist (spatialCubeCollarRetraction y)]
    rw [hyzero, dist_zero_left, hgnorm] at hclose
    exact (lt_irrefl 1 hclose)
  · have hjar := spatialCubeCollarRetraction_tail_mem_boundaryJar_of_weight_ne_one hw
    have hclose : dist (spatialJarInteriorTranslate N g t y) b < 1 := by
      have hwI := spatialCubeJarCollarWeight_mem_Icc y
      have hwabs : |spatialCubeJarCollarWeight y| ≤ 1 := by
        rw [abs_of_nonneg hwI.1]
        exact hwI.2
      calc
        dist (spatialJarInteriorTranslate N g t y) b =
            ‖spatialCubeJarCollarWeight y • t‖ := by
          rw [spatialJarInteriorTranslate_apply,
            cubeGridAffineApprox_eq_of_tail_mem_boundaryJar hN g hg hjar, dist_eq_norm]
          simp
        _ = |spatialCubeJarCollarWeight y| * ‖t‖ := norm_smul _ _
        _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hwabs (norm_nonneg t)
        _ < 1 := by linarith
    rw [hyzero, dist_zero_left, hb] at hclose
    exact (lt_irrefl 1 hclose)

/-- Radial separation for the spatial-jar translation follows from the same translated-core and
basepoint-segment obstructions as for one relative loop. -/
theorem radialProj_spatialJarInteriorTranslate_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (g : C(I^ Fin (k + 2), F)) (h : C(I^ Fin m, F)) {b t : F}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b)
    (hb : ‖b‖ = 1)
    (hne : ∀ y, spatialJarInteriorTranslate N g t y ≠ 0)
    (hcore : Disjoint
      ((fun x => x + t) '' Set.range (cubeGridAffineApprox (k + 2) N g))
      (gridConeSpan m M h))
    (hcollar : t ∉ gridBaseConeSpan m M h b) :
    Set.range (fun y => radialProj (spatialJarInteriorTranslate N g t y)) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  rintro q ⟨hqfirst, hqsecond⟩
  obtain ⟨y, hy⟩ := hqfirst
  obtain ⟨z, hz⟩ := hqsecond
  have heq : radialProj (spatialJarInteriorTranslate N g t y) =
      radialProj (cubeGridAffineApprox m M h z) := hy.trans hz.symm
  have hxcone : spatialJarInteriorTranslate N g t y ∈ gridConeSpan m M h :=
    mem_gridConeSpan_of_radialProj_eq_cubeGridAffineApprox hM h (hne y) z heq
  have hxtrace : spatialJarInteriorTranslate N g t y ∈
      basedTranslationTrace (Set.range (cubeGridAffineApprox (k + 2) N g)) b t :=
    range_spatialJarInteriorTranslate_subset_trace hN g hg (Set.mem_range_self y)
  rcases hxtrace with hxcore | hxsegment
  · exact (Set.disjoint_left.mp hcore hxcore hxcone).elim
  · by_cases hxb : spatialJarInteriorTranslate N g t y = b
    · apply Set.mem_singleton_iff.mpr
      calc
        q = radialProj (spatialJarInteriorTranslate N g t y) := hy.symm
        _ = b := by rw [hxb, radialProj_of_norm_eq_one hb]
    · exfalso
      apply hcollar
      rw [segment_vadd_eq] at hxsegment
      obtain ⟨c, hc, hxc⟩ := hxsegment
      change b + c • t = spatialJarInteriorTranslate N g t y at hxc
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hxb
        calc
          spatialJarInteriorTranslate N g t y = b + c • t := hxc.symm
          _ = b := by simp [hc0]
      have htmem := smul_sub_mem_gridBaseConeSpan (M := M) (b := b) hxcone c⁻¹
      have heq' : c⁻¹ • (spatialJarInteriorTranslate N g t y - b) = t := by
        rw [← hxc]
        simp [hc0, smul_smul]
      rwa [heq'] at htmem

section Measure

variable [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
variable (μ : Measure F) [μ.IsAddHaarMeasure]

include μ in
/-- Stable radial general position for a homotopy cube relative only to its constant spatial
jar. One small translation separates the entire homotopy at once. -/
theorem exists_spatialJarInteriorTranslate_radial_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hdim : (k + 2) + m + 2 ≤ finrank ℝ F)
    (g : C(I^ Fin (k + 2), F)) (h : C(I^ Fin m, F)) {b : F}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b)
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 2) N g y) (g y) ≤ 1 / 2)
    (hb : ‖b‖ = 1) :
    ∃ t : F, ‖t‖ < 1 / 8 ∧
      (∀ y, spatialJarInteriorTranslate N g t y ≠ 0) ∧
      Set.range (fun y => radialProj (spatialJarInteriorTranslate N g t y)) ∩
        Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  obtain ⟨t, htball, hcore, hcollar⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_notMem_gridBaseConeSpan
      μ hN (by omega) hdim g h b Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)⟩
  have ht : ‖t‖ < 1 / 8 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  have hne : ∀ y, spatialJarInteriorTranslate N g t y ≠ 0 :=
    spatialJarInteriorTranslate_ne_zero_of_dist_le_half hN g hg hgnorm hdist hb
      (by linarith)
  exact ⟨t, ht, hne,
    radialProj_spatialJarInteriorTranslate_inter_subset_singleton
      hN hM g h hg hb hne hcore hcollar⟩

end Measure

/-! ### Deformation from the grid homotopy to its spatial-jar translation -/

/-- Switch on the spatial cubical collar retraction while leaving time unchanged. -/
noncomputable def spatialCubeCollarRetractionHomotopyPoint
    (p : I × I^ Fin (k + 2)) : I^ Fin (k + 2) :=
  Fin.cons (p.2 0)
    (cubeCollarRetractionHomotopyPoint (p.1, fun i => p.2 i.succ))

theorem continuous_spatialCubeCollarRetractionHomotopyPoint :
    Continuous (spatialCubeCollarRetractionHomotopyPoint :
      (I × I^ Fin (k + 2)) → I^ Fin (k + 2)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ ?_ i
  · change Continuous fun p : I × I^ Fin (k + 2) => p.2 0
    fun_prop
  · intro j
    change Continuous fun p : I × I^ Fin (k + 2) =>
      cubeCollarRetractionHomotopyPoint
        (p.1, fun i : Fin (k + 1) => p.2 i.succ) j
    exact (continuous_apply j).comp
      (continuous_cubeCollarRetractionHomotopyPoint.comp (by fun_prop))

@[simp] theorem spatialCubeCollarRetractionHomotopyPoint_zero
    (y : I^ Fin (k + 2)) :
    spatialCubeCollarRetractionHomotopyPoint (0, y) = y := by
  ext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [spatialCubeCollarRetractionHomotopyPoint]

@[simp] theorem spatialCubeCollarRetractionHomotopyPoint_one
    (y : I^ Fin (k + 2)) :
    spatialCubeCollarRetractionHomotopyPoint (1, y) =
      spatialCubeCollarRetraction y := by
  ext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [spatialCubeCollarRetractionHomotopyPoint,
      spatialCubeCollarRetraction]

theorem spatialCubeCollarRetractionHomotopyPoint_tail_mem_boundary
    (u : I) {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ∂I^(k + 1)) :
    (fun i : Fin (k + 1) =>
      spatialCubeCollarRetractionHomotopyPoint (u, y) i.succ) ∈
        ∂I^(k + 1) :=
  cubeCollarRetractionHomotopyPoint_mem_boundary u hy

theorem spatialCubeCollarRetractionHomotopyPoint_tail_mem_boundaryJar
    (u : I) {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ⊔I^(k + 1)) :
    (fun i : Fin (k + 1) =>
      spatialCubeCollarRetractionHomotopyPoint (u, y) i.succ) ∈
        ⊔I^(k + 1) :=
  cubeCollarRetractionHomotopyPoint_mem_boundaryJar u hy

/-- Ambient deformation from the full grid approximation to its spatial-jar translation. -/
noncomputable def spatialJarInteriorTranslateRadialHomotopyAmbient
    (N : ℕ) (g : C(I^ Fin (k + 2), F)) (t : F) :
    C(I × I^ Fin (k + 2), F) where
  toFun p := cubeGridAffineApprox (k + 2) N g
      (spatialCubeCollarRetractionHomotopyPoint p) +
    ((p.1 : ℝ) * spatialCubeJarCollarWeight p.2) • t
  continuous_toFun :=
    ((cubeGridAffineApprox (k + 2) N g).continuous.comp
      continuous_spatialCubeCollarRetractionHomotopyPoint).add
      (((continuous_subtype_val.comp continuous_fst).mul
        (continuous_spatialCubeJarCollarWeight.comp continuous_snd)).smul
          continuous_const)

@[simp] theorem spatialJarInteriorTranslateRadialHomotopyAmbient_zero
    (g : C(I^ Fin (k + 2), F)) (t : F) (y : I^ Fin (k + 2)) :
    spatialJarInteriorTranslateRadialHomotopyAmbient N g t (0, y) =
      cubeGridAffineApprox (k + 2) N g y := by
  simp [spatialJarInteriorTranslateRadialHomotopyAmbient]

@[simp] theorem spatialJarInteriorTranslateRadialHomotopyAmbient_one
    (g : C(I^ Fin (k + 2), F)) (t : F) (y : I^ Fin (k + 2)) :
    spatialJarInteriorTranslateRadialHomotopyAmbient N g t (1, y) =
      spatialJarInteriorTranslate N g t y := by
  simp [spatialJarInteriorTranslateRadialHomotopyAmbient,
    spatialJarInteriorTranslate_apply]

theorem spatialJarInteriorTranslateRadialHomotopyAmbient_eq_of_tail_mem_boundaryJar
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 2), F)) {b t : F}
    (hg : ∀ z, (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) → g z = b)
    (u : I) {y : I^ Fin (k + 2)}
    (hy : (fun i : Fin (k + 1) => y i.succ) ∈ ⊔I^(k + 1)) :
    spatialJarInteriorTranslateRadialHomotopyAmbient N g t (u, y) = b := by
  change cubeGridAffineApprox (k + 2) N g
      (spatialCubeCollarRetractionHomotopyPoint (u, y)) +
    ((u : ℝ) * spatialCubeJarCollarWeight y) • t = b
  rw [cubeGridAffineApprox_eq_of_tail_mem_boundaryJar hN g hg
      (spatialCubeCollarRetractionHomotopyPoint_tail_mem_boundaryJar u hy),
    spatialCubeJarCollarWeight_eq_zero_of_tail_mem_boundaryJar hy]
  simp

/-- The whole deformation to a small spatial-jar translation stays nonzero. -/
theorem spatialJarInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
    (g : C(I^ Fin (k + 2), F))
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 2) N g y) (g y) ≤ 1 / 2)
    {t : F} (ht : ‖t‖ < 1 / 2) :
    ∀ p, spatialJarInteriorTranslateRadialHomotopyAmbient N g t p ≠ 0 := by
  rintro ⟨u, y⟩ hzero
  let z := spatialCubeCollarRetractionHomotopyPoint (u, y)
  have hwI := spatialCubeJarCollarWeight_mem_Icc y
  have huI : (u : ℝ) ∈ Set.Icc 0 1 := u.2
  have hcoef_nonneg : 0 ≤ (u : ℝ) * spatialCubeJarCollarWeight y :=
    mul_nonneg huI.1 hwI.1
  have hcoef_le : (u : ℝ) * spatialCubeJarCollarWeight y ≤ 1 := by
    calc
      (u : ℝ) * spatialCubeJarCollarWeight y ≤
          1 * spatialCubeJarCollarWeight y :=
        mul_le_mul_of_nonneg_right huI.2 hwI.1
      _ ≤ 1 := by simpa using hwI.2
  have hclose : dist
      (spatialJarInteriorTranslateRadialHomotopyAmbient N g t (u, y))
      (g z) < 1 := by
    calc
      dist (spatialJarInteriorTranslateRadialHomotopyAmbient N g t (u, y))
          (g z) ≤
        dist (spatialJarInteriorTranslateRadialHomotopyAmbient N g t (u, y))
            (cubeGridAffineApprox (k + 2) N g z) +
          dist (cubeGridAffineApprox (k + 2) N g z) (g z) := dist_triangle _ _ _
      _ = ‖((u : ℝ) * spatialCubeJarCollarWeight y) • t‖ +
          dist (cubeGridAffineApprox (k + 2) N g z) (g z) := by
        rw [spatialJarInteriorTranslateRadialHomotopyAmbient, dist_eq_norm]
        simp [z]
      _ ≤ ‖t‖ + dist (cubeGridAffineApprox (k + 2) N g z) (g z) := by
        gcongr
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
        exact mul_le_of_le_one_left (norm_nonneg t) hcoef_le
      _ < 1 := by linarith [hdist z]
  rw [hzero, dist_zero_left, hgnorm] at hclose
  exact (lt_irrefl 1 hclose)

/-! ### Cap-safe sphere-valued spatial-jar deformation -/

variable {d : ℕ}

/-- A spatial-jar perturbation of norm below `1/8` stays in the upper cap throughout its radial
deformation, uniformly in the original homotopy time. -/
theorem spatialJarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
    (hN : 1 ≤ N)
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 2) N
      (relativeSphereHomotopyToEuclidean H) y)
        (relativeSphereHomotopyToEuclidean H y) ≤ 1 / 2)
    {t : EuclideanSpace ℝ (Fin (d + 2))} (ht : ‖t‖ < 1 / 8)
    (u s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    -(1 / 3 : ℝ) ≤
      radialProj
        (spatialJarInteriorTranslateRadialHomotopyAmbient N
          (relativeSphereHomotopyToEuclidean H) t (u, Fin.cons s y))
          (Fin.last (d + 1)) := by
  let z := spatialCubeCollarRetractionHomotopyPoint (u, Fin.cons s y)
  let v := cubeGridAffineApprox (k + 2) N
    (relativeSphereHomotopyToEuclidean H) z
  let c : ℝ := (u : ℝ) * spatialCubeJarCollarWeight (Fin.cons s y)
  have hvnorm : 1 / 2 ≤ ‖v‖ :=
    cubeGridAffineApprox_norm_ge_half (relativeSphereHomotopyToEuclidean H)
      (fun q => norm_coe_sph (H (q 0, fun i => q i.succ))) hdist z
  have hvlast : 0 ≤ v (Fin.last (d + 1)) := by
    have htail : (fun i : Fin (k + 1) => z i.succ) ∈ ∂I^(k + 1) :=
      spatialCubeCollarRetractionHomotopyPoint_tail_mem_boundary u hy
    have htime : z 0 = s := rfl
    dsimp only [v]
    rw [show z = Fin.cons s (fun i => z i.succ) from by
      rw [← htime]; exact (Fin.cons_self_tail z).symm]
    exact cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
      hN H hheight s htail
  have hwI := spatialCubeJarCollarWeight_mem_Icc (Fin.cons s y)
  have hc0 : 0 ≤ c := mul_nonneg u.2.1 hwI.1
  have hc1 : c ≤ 1 := by
    calc
      c ≤ 1 * spatialCubeJarCollarWeight (Fin.cons s y) :=
        mul_le_mul_of_nonneg_right u.2.2 hwI.1
      _ ≤ 1 := by simpa using hwI.2
  change -(1 / 3 : ℝ) ≤ radialProj (v + c • t) (Fin.last (d + 1))
  exact radialProj_add_smul_last_ge_neg_third
    v t c hvnorm hvlast hc0 hc1 ht

/-- A time slice of the spatial-jar perturbation, bundled as a cap-safe relative sphere loop. -/
noncomputable def radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (spatialJarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)),
        mem_sphere_zero_iff_norm.mpr
          (norm_radialProj (hne (Fin.cons s y)))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        ((spatialJarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous.comp (by fun_prop))
        (fun y => hne (Fin.cons s y))) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤ radialProj
          (spatialJarInteriorTranslate A.mesh
            (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y))
              (Fin.last (d + 1))
        simpa only [spatialJarInteriorTranslateRadialHomotopyAmbient_one] using
          (spatialJarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
            A.mesh_pos H hheight A.dist_le_half ht (1 : I) s hy),
      fun y hy => Subtype.ext (by
        change radialProj (spatialJarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) =
            ((sphereBasepoint (d + 1) : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2)))
        rw [← spatialJarInteriorTranslateRadialHomotopyAmbient_one,
          spatialJarInteriorTranslateRadialHomotopyAmbient_eq_of_tail_mem_boundaryJar
            A.mesh_pos (relativeSphereHomotopyToEuclidean H)
            (fun z hz => congrArg Subtype.val (hjar (z 0) (fun i => z i.succ) hz))
            (1 : I) hy]
        exact radialProj_of_norm_eq_one
          (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) (y : I^ Fin (k + 1)) :
    (((radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (spatialJarInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) :=
  rfl

/-- Every original radial PL slice is relatively homotopic to its spatial-jar perturbation. -/
theorem relativeSpherePLHomotopyApproximation_approxSlice_homotopic_spatialJarTranslate
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) :
    RelGenLoop.Homotopic (A.approxSlice s)
      (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
        A t ht hne s) := by
  let F := relativeSphereHomotopyToEuclidean H
  have hHne : ∀ p, spatialJarInteriorTranslateRadialHomotopyAmbient
      A.mesh F t p ≠ 0 :=
    spatialJarInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
      F (fun y => norm_coe_sph (H (y 0, fun i => y i.succ)))
      A.dist_le_half (by linarith)
  let G : C(I × I^ Fin (k + 1), EuclideanSpace ℝ (Fin (d + 2))) :=
    ⟨fun uy => spatialJarInteriorTranslateRadialHomotopyAmbient
        A.mesh F t (uy.1, Fin.cons s uy.2),
      (spatialJarInteriorTranslateRadialHomotopyAmbient
        A.mesh F t).continuous.comp (by fun_prop)⟩
  have hGne : ∀ uy, G uy ≠ 0 :=
    fun uy => hHne (uy.1, Fin.cons s uy.2)
  refine ⟨⟨⟨fun uy =>
      ⟨radialProj (G uy),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hGne uy))⟩,
      Continuous.subtype_mk (continuous_radialProj G.continuous hGne) _⟩,
    fun y => ?_, fun y => ?_⟩, fun u => ?_⟩
  · apply Subtype.ext
    change radialProj (spatialJarInteriorTranslateRadialHomotopyAmbient
      A.mesh F t (0, Fin.cons s y)) =
        (((A.approxSlice s).val y : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))
    rw [spatialJarInteriorTranslateRadialHomotopyAmbient_zero]
    rfl
  · apply Subtype.ext
    change radialProj (spatialJarInteriorTranslateRadialHomotopyAmbient
      A.mesh F t (1, Fin.cons s y)) =
        (((radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
          A t ht hne s).val y : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))
    rw [spatialJarInteriorTranslateRadialHomotopyAmbient_one]
    rfl
  · constructor
    · intro y hy
      rw [mem_sphUpperCap]
      change -(1 / 3 : ℝ) ≤ radialProj
        (spatialJarInteriorTranslateRadialHomotopyAmbient
          A.mesh F t (u, Fin.cons s y)) (Fin.last (d + 1))
      exact spatialJarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
        A.mesh_pos H hheight A.dist_le_half ht u s hy
    · intro y hy
      apply Subtype.ext
      change radialProj (spatialJarInteriorTranslateRadialHomotopyAmbient
        A.mesh F t (u, Fin.cons s y)) =
          ((sphereBasepoint (d + 1) : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))
      rw [spatialJarInteriorTranslateRadialHomotopyAmbient_eq_of_tail_mem_boundaryJar
        A.mesh_pos F
        (fun z hz => congrArg Subtype.val (hjar (z 0) (fun i => z i.succ) hz))
        u hy]
      exact radialProj_of_norm_eq_one
        (norm_coe_sph (sphereBasepoint (d + 1)))

/-- The spatial-jar perturbed slices themselves form a relative sphere homotopy. -/
theorem radialSpatialJarInteriorTranslateRelativeSphereHomotopy_homotopic
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic
      (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 0)
      (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 1) := by
  let G := spatialJarInteriorTranslate A.mesh
    (relativeSphereHomotopyToEuclidean H) t
  have hGcont : Continuous fun sy : I × I^ Fin (k + 1) =>
      G (Fin.cons sy.1 sy.2) := G.continuous.comp (by fun_prop)
  have hGne : ∀ sy : I × I^ Fin (k + 1), G (Fin.cons sy.1 sy.2) ≠ 0 :=
    fun sy => hne (Fin.cons sy.1 sy.2)
  refine ⟨⟨⟨fun sy =>
      ⟨radialProj (G (Fin.cons sy.1 sy.2)),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hGne sy))⟩,
      Continuous.subtype_mk (continuous_radialProj hGcont hGne) _⟩,
    fun _ => rfl, fun _ => rfl⟩, fun s => ?_⟩
  constructor
  · intro y hy
    exact (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).property.1 y hy
  · intro y hy
    exact (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).property.2 y hy

/-! ### Unconditional stable general position for a relative sphere homotopy -/

/-- The sphere-valued spatial-jar perturbation on the entire time-first cube. -/
noncomputable def radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    C(I^ Fin (k + 2), Sph (d + 1)) :=
  ⟨fun y =>
      ⟨radialProj (spatialJarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t y),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne y))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        (spatialJarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous hne) _⟩

@[simp] theorem coe_radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (y : I^ Fin (k + 2)) :
    ((radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube A t hne y :
      Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (spatialJarInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t y) :=
  rfl

/-- Stable general-position data for an entire relative sphere homotopy, with no prior
separation hypothesis on its boundary or endpoints. -/
structure RelativeSphereSpatialJarGeneralPositionHomotopy
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g) where
  translation : EuclideanSpace ℝ (Fin (d + 2))
  translation_norm_lt_eighth : ‖translation‖ < 1 / 8
  perturbed_ne_zero : ∀ y, spatialJarInteriorTranslate A.mesh
    (relativeSphereHomotopyToEuclidean H) translation y ≠ 0
  range_inter_subset_singleton :
    Set.range (radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube
      A translation perturbed_ne_zero) ∩ Set.range B.approx ⊆
        {sphereBasepoint (d + 1)}

namespace RelativeSphereSpatialJarGeneralPositionHomotopy

noncomputable def start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice A D.translation
    D.translation_norm_lt_eighth D.perturbed_ne_zero 0

noncomputable def finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice A D.translation
    D.translation_norm_lt_eighth D.perturbed_ne_zero 1

theorem approxStart_homotopic_start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 0) D.start :=
  relativeSpherePLHomotopyApproximation_approxSlice_homotopic_spatialJarTranslate
    A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero 0

theorem approxFinish_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 1) D.finish :=
  relativeSpherePLHomotopyApproximation_approxSlice_homotopic_spatialJarTranslate
    A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero 1

theorem start_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic D.start D.finish :=
  radialSpatialJarInteriorTranslateRelativeSphereHomotopy_homotopic
    A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero

/-- The selected sphere-valued homotopy underlying the general-position data. -/
noncomputable def homotopy
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    ContinuousMap.HomotopyWith D.start.val D.finish.val
      (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)) where
  toFun sy := radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube
    A D.translation D.perturbed_ne_zero (Fin.cons sy.1 sy.2)
  continuous_toFun :=
    (radialSpatialJarInteriorTranslateRelativeSphereHomotopyCube
      A D.translation D.perturbed_ne_zero).continuous.comp (by fun_prop)
  map_zero_left _ := rfl
  map_one_left _ := rfl
  prop' s :=
    (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
      A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero s).property

/-- The entire selected homotopy, not merely each endpoint, avoids the second PL sphere image
away from the basepoint. -/
theorem homotopy_range_inter_subset_singleton
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    Set.range D.homotopy.toHomotopy.toContinuousMap ∩ Set.range B.approx ⊆
      {sphereBasepoint (d + 1)} := by
  rintro x ⟨hxfirst, hxsecond⟩
  apply D.range_inter_subset_singleton
  constructor
  · obtain ⟨⟨s, y⟩, hy⟩ := hxfirst
    exact ⟨Fin.cons s y, hy⟩
  · exact hxsecond

theorem originalStart_homotopic_start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (relativeSphereHomotopySlice H hheight hjar 0) D.start :=
  (A.originalSlice_homotopic_approxSlice 0).trans D.approxStart_homotopic_start

theorem originalFinish_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (relativeSphereHomotopySlice H hheight hjar 1) D.finish :=
  (A.originalSlice_homotopic_approxSlice 1).trans D.approxFinish_homotopic_finish

theorem slice_range_inter_subset_singleton
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereSpatialJarGeneralPositionHomotopy A g B) (s : I) :
    Set.range (radialSpatialJarInteriorTranslateRelativeSphereHomotopySlice
      A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero s).val ∩
        Set.range B.approx ⊆ {sphereBasepoint (d + 1)} := by
  rintro x ⟨hxfirst, hxsecond⟩
  apply D.range_inter_subset_singleton
  constructor
  · obtain ⟨y, hy⟩ := hxfirst
    refine ⟨Fin.cons s y, ?_⟩
    apply Subtype.ext
    change radialProj (spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) D.translation (Fin.cons s y)) =
        ((x : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [← hy]
    rfl
  · exact hxsecond

end RelativeSphereSpatialJarGeneralPositionHomotopy

/-- **Unconditional stable general position for relative sphere homotopies.** In the stable
dimension range, every cap-safe PL relative homotopy can be perturbed, through cap-safe relative
homotopies and without changing either endpoint class, so that its entire image meets a fixed
based sphere PL image only at the distinguished basepoint. -/
theorem exists_relativeSphereSpatialJarGeneralPositionHomotopy
    (hdim : k + m + 2 ≤ d)
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g) :
    Nonempty (RelativeSphereSpatialJarGeneralPositionHomotopy A g B) := by
  let E := EuclideanSpace ℝ (Fin (d + 2))
  have hdimE : (k + 2) + m + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hjarE : ∀ z,
      (fun i : Fin (k + 1) => z i.succ) ∈ (⊔I^(k + 1)) →
      relativeSphereHomotopyToEuclidean H z =
        ((sphereBasepoint (d + 1) : Sph (d + 1)) : E) := by
    intro z hz
    exact congrArg Subtype.val (hjar (z 0) (fun i => z i.succ) hz)
  obtain ⟨t, ht, hne, hinter⟩ :=
    exists_spatialJarInteriorTranslate_radial_inter_subset_singleton
      (volume : Measure E) A.mesh_pos B.mesh_pos hdimE
      (relativeSphereHomotopyToEuclidean H) (genLoopToEuclidean g) hjarE
      (fun y => norm_coe_sph (H (y 0, fun i => y i.succ))) A.dist_le_half
      (norm_coe_sph (sphereBasepoint (d + 1)))
  refine ⟨⟨t, ht, hne, ?_⟩⟩
  rintro x ⟨hxfirst, hxsecond⟩
  obtain ⟨y, hy⟩ := hxfirst
  obtain ⟨z, hz⟩ := hxsecond
  apply Set.mem_singleton_iff.mpr
  apply Subtype.ext
  apply Set.mem_singleton_iff.mp
  apply hinter
  constructor
  · refine ⟨y, ?_⟩
    change radialProj (spatialJarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y) = ((x : Sph (d + 1)) : E)
    rw [← hy]
    rfl
  · refine ⟨z, ?_⟩
    change radialProj (cubeGridAffineApprox m B.mesh
      (genLoopToEuclidean g) z) = ((x : Sph (d + 1)) : E)
    rw [← hz]
    exact (B.coe_approx z).symm

/-- **Representative-level stable homotopy avoidance.** Given any relative homotopy and any
based sphere loop in the stable dimension range, all three maps can be replaced within their
homotopy classes so that a selected relative homotopy between the first two misses the third
map everywhere except at the common basepoint. -/
theorem exists_homotopic_relativeSphereHomotopy_avoiding_sphereGenLoop
    (hdim : k + m + 2 ≤ d)
    {p q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)}
    (hpq : RelGenLoop.Homotopic p q)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))) :
    ∃ (p' q' : RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))
      (g' : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
      (K : ContinuousMap.HomotopyWith p'.val q'.val
        (fun f => f ∈ RelGenLoop (k + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d))),
      RelGenLoop.Homotopic p p' ∧ RelGenLoop.Homotopic q q' ∧
      _root_.GenLoop.Homotopic g g' ∧
      Set.range K.toHomotopy.toContinuousMap ∩ Set.range g' ⊆
        {sphereBasepoint (d + 1)} := by
  obtain ⟨H, hheight, hjar, A, hpA, hqA⟩ :=
    exists_relativeSpherePLHomotopyRepresentatives_of_homotopic hpq
  obtain ⟨B⟩ := exists_spherePLApproximation g
  obtain ⟨D⟩ := exists_relativeSphereSpatialJarGeneralPositionHomotopy
    hdim A g B
  exact ⟨D.start, D.finish, B.approx, D.homotopy,
    hpA.trans D.approxStart_homotopic_start,
    hqA.trans D.approxFinish_homotopic_finish,
    B.homotopic, D.homotopy_range_inter_subset_singleton⟩

end Submission
