/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.RelativeSphere

/-!
# Jar-relative general position for sphere-cap loops

The full cubical collar used for based sphere maps fixes every boundary face. A relative loop
must instead fix only the boundary jar while its top lid remains free inside the upper cap. This
file constructs the corresponding one-sided collar, proves that its radial perturbation stays
inside the cap throughout the relative homotopy, and combines it with finite PL general position.

The resulting theorem separates a relative sphere-cap representative from an absolute based
sphere representative in the stable dimension range while preserving both homotopy classes.

## Main results

* `Submission.jarInteriorTranslate`
* `Submission.relativeSpherePLApproximation_approx_homotopic_radialJarInteriorTranslate`
* `Submission.exists_homotopic_relativeSphereLoop_sphereGenLoop_range_inter_subset_singleton`
* `Submission.relHomotopyGroup_homotopyGroup_exists_generalPositionRepresentatives`
* `Submission.exists_homotopic_relativeSphereLoops_range_inter_subset_singleton`
* `Submission.relHomotopyGroups_exists_generalPositionRepresentatives`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {k n m N M : ℕ}

/-! ### A collar relative to the cubical boundary jar -/

/-- A one-sided collar weight: zero at the bottom and one from the middle third upward. -/
def bottomCollarWeightCoord (x : I) : ℝ :=
  min (3 * (x : ℝ)) 1

theorem continuous_bottomCollarWeightCoord : Continuous bottomCollarWeightCoord := by
  change Continuous (fun x : I => min (3 * (x : ℝ)) 1)
  fun_prop

theorem bottomCollarWeightCoord_nonneg (x : I) : 0 ≤ bottomCollarWeightCoord x := by
  exact le_min (mul_nonneg (by norm_num) x.2.1) zero_le_one

theorem bottomCollarWeightCoord_le_one (x : I) : bottomCollarWeightCoord x ≤ 1 :=
  min_le_right _ _

@[simp] theorem bottomCollarWeightCoord_zero : bottomCollarWeightCoord (0 : I) = 0 := by
  norm_num [bottomCollarWeightCoord]

@[simp] theorem bottomCollarWeightCoord_one : bottomCollarWeightCoord (1 : I) = 1 := by
  norm_num [bottomCollarWeightCoord]

theorem bottomCollarWeightCoord_eq_one_of_collarCoord_ne_zero {x : I}
    (h0 : collarCoord x ≠ 0) : bottomCollarWeightCoord x = 1 := by
  have hxlo : (1 / 3 : ℝ) < (x : ℝ) := by
    by_contra h
    have hx : 3 * (x : ℝ) - 1 ≤ 0 := by
      have := le_of_not_gt h
      linarith
    apply h0
    exact Set.projIcc_of_le_left zero_le_one hx
  rw [bottomCollarWeightCoord, min_eq_right]
  linarith

/-- The product collar weight which vanishes on the bottom and side faces but not on the lid. -/
def cubeJarCollarWeight (y : I^ Fin (k + 1)) : ℝ :=
  bottomCollarWeightCoord (y (Fin.last k)) *
    ∏ i : Fin k, collarWeightCoord (y i.castSucc)

theorem continuous_cubeJarCollarWeight :
    Continuous (cubeJarCollarWeight : (I^ Fin (k + 1)) → ℝ) := by
  apply Continuous.mul
  · exact continuous_bottomCollarWeightCoord.comp (continuous_apply (Fin.last k))
  · apply continuous_finsetProd
    intro i _
    exact continuous_collarWeightCoord.comp (continuous_apply i.castSucc)

theorem cubeJarCollarWeight_mem_Icc (y : I^ Fin (k + 1)) :
    cubeJarCollarWeight y ∈ Set.Icc (0 : ℝ) 1 := by
  have hbot : bottomCollarWeightCoord (y (Fin.last k)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨bottomCollarWeightCoord_nonneg _, bottomCollarWeightCoord_le_one _⟩
  have hside : (∏ i : Fin k, collarWeightCoord (y i.castSucc)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Finset.prod_nonneg fun i _ => collarWeightCoord_nonneg _,
      Finset.prod_le_one (fun i _ => collarWeightCoord_nonneg _)
        (fun i _ => collarWeightCoord_le_one _)⟩
  exact ⟨mul_nonneg hbot.1 hside.1,
    (mul_le_mul hbot.2 hside.2 hside.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem cubeJarCollarWeight_eq_zero_of_mem_boundaryJar {y : I^ Fin (k + 1)}
    (hy : y ∈ ⊔I^(k + 1)) : cubeJarCollarWeight y = 0 := by
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hside
  · rw [Cube.splitAtLast_fst_eq] at hbot
    simp [cubeJarCollarWeight, hbot]
  · obtain ⟨i, hi⟩ := hside
    rw [Cube.splitAtLast_snd_apply_eq] at hi
    have hfactor : collarWeightCoord (y i.castSucc) = 0 := by
      rcases hi with hi | hi
      · simp [hi]
      · simp [hi]
    have hprod : (∏ j : Fin k, collarWeightCoord (y j.castSucc)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    simp [cubeJarCollarWeight, hprod]

theorem cubeCollarRetraction_mem_boundaryJar_of_mem_boundaryJar
    {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeCollarRetraction y ∈ ⊔I^(k + 1) := by
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hside
  · apply Cube.mem_boundaryJar_of_exists_eq_zero
    refine ⟨Fin.last k, ?_⟩
    rw [Cube.splitAtLast_fst_eq] at hbot
    simp [cubeCollarRetraction, hbot]
  · obtain ⟨i, hi⟩ := hside
    apply Cube.mem_boundaryJar_of_lt_last
    refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
    rw [Cube.splitAtLast_snd_apply_eq] at hi
    rcases hi with hi | hi
    · exact Or.inl (by simp [cubeCollarRetraction, hi])
    · exact Or.inr (by simp [cubeCollarRetraction, hi])

theorem cubeCollarRetraction_mem_boundaryJar_of_jarWeight_ne_one
    {y : I^ Fin (k + 1)} (hy : cubeJarCollarWeight y ≠ 1) :
    cubeCollarRetraction y ∈ ⊔I^(k + 1) := by
  by_contra hjar
  apply hy
  have hlast : collarCoord (y (Fin.last k)) ≠ 0 := by
    intro hzero
    apply hjar
    exact Cube.mem_boundaryJar_of_exists_eq_zero _ ⟨Fin.last k, hzero⟩
  have hbot : bottomCollarWeightCoord (y (Fin.last k)) = 1 :=
    bottomCollarWeightCoord_eq_one_of_collarCoord_ne_zero hlast
  have hside : ∀ i : Fin k, collarWeightCoord (y i.castSucc) = 1 := by
    intro i
    apply collarWeightCoord_eq_one_of_collarCoord_ne_endpoints
    · intro hzero
      apply hjar
      apply Cube.mem_boundaryJar_of_lt_last
      exact ⟨i.castSucc, Fin.castSucc_lt_last i, Or.inl hzero⟩
    · intro hone
      apply hjar
      apply Cube.mem_boundaryJar_of_lt_last
      exact ⟨i.castSucc, Fin.castSucc_lt_last i, Or.inr hone⟩
  simp [cubeJarCollarWeight, hbot, hside]

theorem cubeCollarRetractionHomotopyPoint_mem_boundaryJar
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeCollarRetractionHomotopyPoint (s, y) ∈ ⊔I^(k + 1) := by
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hside
  · apply Cube.mem_boundaryJar_of_exists_eq_zero
    refine ⟨Fin.last k, ?_⟩
    rw [Cube.splitAtLast_fst_eq] at hbot
    change Set.Icc.convexComb (y (Fin.last k)) (collarCoord (y (Fin.last k))) s = 0
    rw [hbot, collarCoord_zero, Set.Icc.convexComb_eq]
  · obtain ⟨i, hi⟩ := hside
    apply Cube.mem_boundaryJar_of_lt_last
    refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
    rw [Cube.splitAtLast_snd_apply_eq] at hi
    rcases hi with hi | hi
    · left
      change Set.Icc.convexComb (y i.castSucc) (collarCoord (y i.castSucc)) s = 0
      rw [hi, collarCoord_zero, Set.Icc.convexComb_eq]
    · right
      change Set.Icc.convexComb (y i.castSucc) (collarCoord (y i.castSucc)) s = 1
      rw [hi, collarCoord_one, Set.Icc.convexComb_eq]

/-! ### Jar-relative interior translation -/

/-- Translate the grid approximation in the core, tapering only on the cubical boundary jar. -/
noncomputable def jarInteriorTranslate (N : ℕ) (g : C(I^ Fin (k + 1), F)) (t : F) :
    C(I^ Fin (k + 1), F) where
  toFun y := cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y) +
    cubeJarCollarWeight y • t
  continuous_toFun :=
    ((cubeGridAffineApprox (k + 1) N g).continuous.comp
      continuous_cubeCollarRetraction).add
      (continuous_cubeJarCollarWeight.smul continuous_const)

@[simp] theorem jarInteriorTranslate_apply (g : C(I^ Fin (k + 1), F)) (t : F)
    (y : I^ Fin (k + 1)) :
    jarInteriorTranslate N g t y =
      cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y) +
        cubeJarCollarWeight y • t :=
  rfl

theorem jarInteriorTranslate_eq_of_mem_boundaryJar (hN : 1 ≤ N)
    (g : C(I^ Fin (k + 1), F)) {b t : F}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b) {y : I^ Fin (k + 1)}
    (hy : y ∈ ⊔I^(k + 1)) : jarInteriorTranslate N g t y = b := by
  rw [jarInteriorTranslate_apply,
    cubeGridAffineApprox_eq_of_mem_boundaryJar hN g hg
      (cubeCollarRetraction_mem_boundaryJar_of_mem_boundaryJar hy),
    cubeJarCollarWeight_eq_zero_of_mem_boundaryJar hy, zero_smul, add_zero]

theorem range_jarInteriorTranslate_subset_trace (hN : 1 ≤ N)
    (g : C(I^ Fin (k + 1), F)) {b t : F}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b) :
    Set.range (jarInteriorTranslate N g t) ⊆
      basedTranslationTrace
        (Set.range (cubeGridAffineApprox (k + 1) N g)) b t := by
  rintro _ ⟨y, rfl⟩
  by_cases hw : cubeJarCollarWeight y = 1
  · apply Or.inl
    refine ⟨cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y),
      ⟨cubeCollarRetraction y, rfl⟩, ?_⟩
    simp [jarInteriorTranslate_apply, hw]
  · apply Or.inr
    rw [jarInteriorTranslate_apply,
      cubeGridAffineApprox_eq_of_mem_boundaryJar hN g hg
        (cubeCollarRetraction_mem_boundaryJar_of_jarWeight_ne_one hw)]
    rw [segment_vadd_eq]
    exact ⟨cubeJarCollarWeight y, cubeJarCollarWeight_mem_Icc y, rfl⟩

theorem radialProj_jarInteriorTranslate_inter_subset_singleton
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (g : C(I^ Fin (k + 1), F)) (h : C(I^ Fin m, F)) {b t : F}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b) (hb : ‖b‖ = 1)
    (hne : ∀ y, jarInteriorTranslate N g t y ≠ 0)
    (hcore : Disjoint
      ((fun x => x + t) '' Set.range (cubeGridAffineApprox (k + 1) N g))
      (gridConeSpan m M h))
    (hcollar : t ∉ gridBaseConeSpan m M h b) :
    Set.range (fun y => radialProj (jarInteriorTranslate N g t y)) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  rintro q ⟨hqfirst, hqsecond⟩
  obtain ⟨y, hy⟩ := hqfirst
  obtain ⟨z, hz⟩ := hqsecond
  have heq : radialProj (jarInteriorTranslate N g t y) =
      radialProj (cubeGridAffineApprox m M h z) := hy.trans hz.symm
  have hxcone : jarInteriorTranslate N g t y ∈ gridConeSpan m M h :=
    mem_gridConeSpan_of_radialProj_eq_cubeGridAffineApprox hM h (hne y) z heq
  have hxtrace : jarInteriorTranslate N g t y ∈
      basedTranslationTrace (Set.range (cubeGridAffineApprox (k + 1) N g)) b t :=
    range_jarInteriorTranslate_subset_trace (t := t) hN g hg (Set.mem_range_self y)
  rcases hxtrace with hxcore | hxsegment
  · exact (Set.disjoint_left.mp hcore hxcore hxcone).elim
  · by_cases hxb : jarInteriorTranslate N g t y = b
    · apply Set.mem_singleton_iff.mpr
      calc
        q = radialProj (jarInteriorTranslate N g t y) := hy.symm
        _ = b := by rw [hxb, radialProj_of_norm_eq_one hb]
    · exfalso
      apply hcollar
      rw [segment_vadd_eq] at hxsegment
      obtain ⟨c, hc, hxc⟩ := hxsegment
      change b + c • t = jarInteriorTranslate N g t y at hxc
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hxb
        calc
          jarInteriorTranslate N g t y = b + c • t := hxc.symm
          _ = b := by simp [hc0]
      have htmem := smul_sub_mem_gridBaseConeSpan (M := M) (b := b) hxcone c⁻¹
      have heq' : c⁻¹ • (jarInteriorTranslate N g t y - b) = t := by
        rw [← hxc]
        simp [hc0, smul_smul]
      rwa [heq'] at htmem

theorem jarInteriorTranslate_ne_zero_of_dist_le_half
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 1), F)) {b t : F}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b)
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 1) N g y) (g y) ≤ 1 / 2)
    (hb : ‖b‖ = 1) (ht : ‖t‖ < 1 / 2) :
    ∀ y, jarInteriorTranslate N g t y ≠ 0 := by
  intro y hyzero
  by_cases hw : cubeJarCollarWeight y = 1
  · have hclose : dist (jarInteriorTranslate N g t y)
        (g (cubeCollarRetraction y)) < 1 := by
      calc
        dist (jarInteriorTranslate N g t y) (g (cubeCollarRetraction y))
            ≤ dist (jarInteriorTranslate N g t y)
                (cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y)) +
              dist (cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y))
                (g (cubeCollarRetraction y)) := dist_triangle _ _ _
        _ = ‖t‖ + dist (cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y))
                (g (cubeCollarRetraction y)) := by
              rw [jarInteriorTranslate_apply, hw, one_smul, dist_eq_norm]
              simp
        _ < 1 := by linarith [hdist (cubeCollarRetraction y)]
    rw [hyzero, dist_zero_left, hgnorm] at hclose
    exact (lt_irrefl 1 hclose)
  · have hjar := cubeCollarRetraction_mem_boundaryJar_of_jarWeight_ne_one hw
    have hclose : dist (jarInteriorTranslate N g t y) b < 1 := by
      have hwI := cubeJarCollarWeight_mem_Icc y
      have hwabs : |cubeJarCollarWeight y| ≤ 1 := by
        rw [abs_of_nonneg hwI.1]
        exact hwI.2
      calc
        dist (jarInteriorTranslate N g t y) b = ‖cubeJarCollarWeight y • t‖ := by
          rw [jarInteriorTranslate_apply,
            cubeGridAffineApprox_eq_of_mem_boundaryJar hN g hg hjar, dist_eq_norm]
          simp
        _ = |cubeJarCollarWeight y| * ‖t‖ := norm_smul _ _
        _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hwabs (norm_nonneg t)
        _ < 1 := by linarith
    rw [hyzero, dist_zero_left, hb] at hclose
    exact (lt_irrefl 1 hclose)

/-- Ambient straight-line deformation from the grid approximation to its jar-relative
translation. -/
noncomputable def jarInteriorTranslateRadialHomotopyAmbient
    (N : ℕ) (g : C(I^ Fin (k + 1), F)) (t : F) :
    C(I × I^ Fin (k + 1), F) where
  toFun p := cubeGridAffineApprox (k + 1) N g
      (cubeCollarRetractionHomotopyPoint p) +
    ((p.1 : ℝ) * cubeJarCollarWeight p.2) • t
  continuous_toFun :=
    ((cubeGridAffineApprox (k + 1) N g).continuous.comp
      continuous_cubeCollarRetractionHomotopyPoint).add
      (((continuous_subtype_val.comp continuous_fst).mul
        (continuous_cubeJarCollarWeight.comp continuous_snd)).smul continuous_const)

@[simp] theorem jarInteriorTranslateRadialHomotopyAmbient_zero
    (g : C(I^ Fin (k + 1), F)) (t : F) (y : I^ Fin (k + 1)) :
    jarInteriorTranslateRadialHomotopyAmbient N g t (0, y) =
      cubeGridAffineApprox (k + 1) N g y := by
  simp [jarInteriorTranslateRadialHomotopyAmbient]

@[simp] theorem jarInteriorTranslateRadialHomotopyAmbient_one
    (g : C(I^ Fin (k + 1), F)) (t : F) (y : I^ Fin (k + 1)) :
    jarInteriorTranslateRadialHomotopyAmbient N g t (1, y) =
      jarInteriorTranslate N g t y := by
  simp [jarInteriorTranslateRadialHomotopyAmbient, jarInteriorTranslate_apply]

theorem jarInteriorTranslateRadialHomotopyAmbient_eq_of_mem_boundaryJar
    (hN : 1 ≤ N) (g : C(I^ Fin (k + 1), F)) {b t : F}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b)
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    jarInteriorTranslateRadialHomotopyAmbient N g t (s, y) = b := by
  change cubeGridAffineApprox (k + 1) N g
      (cubeCollarRetractionHomotopyPoint (s, y)) +
    ((s : ℝ) * cubeJarCollarWeight y) • t = b
  rw [cubeGridAffineApprox_eq_of_mem_boundaryJar hN g hg
      (cubeCollarRetractionHomotopyPoint_mem_boundaryJar s hy),
    cubeJarCollarWeight_eq_zero_of_mem_boundaryJar hy]
  simp

theorem jarInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
    (g : C(I^ Fin (k + 1), F))
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y,
      dist (cubeGridAffineApprox (k + 1) N g y) (g y) ≤ 1 / 2)
    {t : F} (ht : ‖t‖ < 1 / 2) :
    ∀ p, jarInteriorTranslateRadialHomotopyAmbient N g t p ≠ 0 := by
  rintro ⟨s, y⟩ hzero
  let z := cubeCollarRetractionHomotopyPoint (s, y)
  have hwI := cubeJarCollarWeight_mem_Icc y
  have hsI : (s : ℝ) ∈ Set.Icc 0 1 := s.2
  have hcoef_nonneg : 0 ≤ (s : ℝ) * cubeJarCollarWeight y :=
    mul_nonneg hsI.1 hwI.1
  have hcoef_le : (s : ℝ) * cubeJarCollarWeight y ≤ 1 := by
    calc
      (s : ℝ) * cubeJarCollarWeight y ≤ 1 * cubeJarCollarWeight y :=
        mul_le_mul_of_nonneg_right hsI.2 hwI.1
      _ ≤ 1 := by simpa using hwI.2
  have hclose : dist (jarInteriorTranslateRadialHomotopyAmbient N g t (s, y))
      (g z) < 1 := by
    calc
      dist (jarInteriorTranslateRadialHomotopyAmbient N g t (s, y)) (g z)
          ≤ dist (jarInteriorTranslateRadialHomotopyAmbient N g t (s, y))
              (cubeGridAffineApprox (k + 1) N g z) +
            dist (cubeGridAffineApprox (k + 1) N g z) (g z) := dist_triangle _ _ _
      _ = ‖((s : ℝ) * cubeJarCollarWeight y) • t‖ +
            dist (cubeGridAffineApprox (k + 1) N g z) (g z) := by
          rw [jarInteriorTranslateRadialHomotopyAmbient, dist_eq_norm]
          simp [z]
      _ ≤ ‖t‖ + dist (cubeGridAffineApprox (k + 1) N g z) (g z) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
          exact mul_le_of_le_one_left (norm_nonneg t) hcoef_le
      _ < 1 := by linarith [hdist z]
  rw [hzero, dist_zero_left, hgnorm] at hclose
  exact (lt_irrefl 1 hclose)

/-! ### Quantitative preservation of the upper cap -/

variable {d : ℕ}

/-- A perturbation of norm below `1/8` cannot move a vector of norm at least `1/2` with
nonnegative last coordinate below height `-1/3` after radial projection. -/
theorem radialProj_add_smul_last_ge_neg_third
    (v t : EuclideanSpace ℝ (Fin (d + 2))) (c : ℝ)
    (hvnorm : 1 / 2 ≤ ‖v‖) (hvlast : 0 ≤ v (Fin.last (d + 1)))
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht : ‖t‖ < 1 / 8) :
    -(1 / 3 : ℝ) ≤ radialProj (v + c • t) (Fin.last (d + 1)) := by
  have hcabs : |c| ≤ 1 := by simpa [abs_of_nonneg hc0] using hc1
  have hct : ‖c • t‖ < 1 / 8 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |c| * ‖t‖ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hcabs (norm_nonneg t)
      _ < 1 / 8 := by simpa using ht
  have hnorm : 3 / 8 < ‖v + c • t‖ := by
    have htri : ‖v‖ ≤ ‖v + c • t‖ + ‖c • t‖ := by
      calc
        ‖v‖ = ‖(v + c • t) - c • t‖ := by
          congr 1
          module
        _ ≤ ‖v + c • t‖ + ‖c • t‖ := norm_sub_le _ _
    linarith
  have hcoordNorm : ‖(c • t) (Fin.last (d + 1))‖ ≤ ‖c • t‖ :=
    PiLp.norm_apply_le (c • t) (Fin.last (d + 1))
  have hcoord : -(1 / 8 : ℝ) < (c • t) (Fin.last (d + 1)) := by
    have habs : |(c • t) (Fin.last (d + 1))| < 1 / 8 := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt hcoordNorm hct
    exact (abs_lt.mp habs).1
  have hlast : -(1 / 8 : ℝ) < (v + c • t) (Fin.last (d + 1)) := by
    rw [PiLp.add_apply]
    linarith
  have hnorm_pos : 0 < ‖v + c • t‖ := lt_trans (by norm_num) hnorm
  rw [radialProj, PiLp.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div, le_div_iff₀ hnorm_pos]
  linarith

theorem cubeGridAffineApprox_norm_ge_half
    (g : C(I^ Fin (k + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y,
      dist (cubeGridAffineApprox (k + 1) N g y) (g y) ≤ 1 / 2)
    (y : I^ Fin (k + 1)) :
    1 / 2 ≤ ‖cubeGridAffineApprox (k + 1) N g y‖ := by
  have hreverse := norm_sub_norm_le (g y) (cubeGridAffineApprox (k + 1) N g y)
  rw [hgnorm] at hreverse
  have hdist' : ‖g y - cubeGridAffineApprox (k + 1) N g y‖ ≤ 1 / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist y
  linarith

theorem jarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
    (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (hdist : ∀ y,
      dist (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y)
        (relGenLoopToEuclidean p y) ≤ 1 / 2)
    {t : EuclideanSpace ℝ (Fin (d + 2))} (ht : ‖t‖ < 1 / 8)
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    -(1 / 3 : ℝ) ≤
      radialProj
          (jarInteriorTranslateRadialHomotopyAmbient N
            (relGenLoopToEuclidean p) t (s, y))
        (Fin.last (d + 1)) := by
  let z := cubeCollarRetractionHomotopyPoint (s, y)
  let v := cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) z
  let c : ℝ := (s : ℝ) * cubeJarCollarWeight y
  have hz : z ∈ ∂I^(k + 1) :=
    cubeCollarRetractionHomotopyPoint_mem_boundary s hy
  have hvnorm : 1 / 2 ≤ ‖v‖ :=
    cubeGridAffineApprox_norm_ge_half (relGenLoopToEuclidean p)
      (fun q => norm_coe_sph (p.val q)) hdist z
  have hvlast : 0 ≤ v (Fin.last (d + 1)) :=
    cubeGridAffineApprox_relGenLoop_last_nonneg hN p hp hz
  have hwI := cubeJarCollarWeight_mem_Icc y
  have hc0 : 0 ≤ c := mul_nonneg s.2.1 hwI.1
  have hc1 : c ≤ 1 := by
    calc
      c ≤ 1 * cubeJarCollarWeight y :=
        mul_le_mul_of_nonneg_right s.2.2 hwI.1
      _ ≤ 1 := by simpa using hwI.2
  change -(1 / 3 : ℝ) ≤ radialProj (v + c • t) (Fin.last (d + 1))
  exact radialProj_add_smul_last_ge_neg_third v t c hvnorm hvlast hc0 hc1 ht

/-! ### Relative sphere representatives -/

/-- Radial projection of the jar-relative translation, bundled as a relative loop of the
sphere/upper-cap pair. -/
noncomputable def radialJarInteriorTranslateRelGenLoop
    (N : ℕ) (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (hdist : ∀ y,
      dist (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y)
        (relGenLoopToEuclidean p y) ≤ 1 / 2)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate N (relGenLoopToEuclidean p) t y ≠ 0) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (jarInteriorTranslate N (relGenLoopToEuclidean p) t y),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne y))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        (jarInteriorTranslate N (relGenLoopToEuclidean p) t).continuous hne) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤
          radialProj (jarInteriorTranslate N (relGenLoopToEuclidean p) t y)
            (Fin.last (d + 1))
        simpa using
          (jarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
            hN p hp hdist ht (1 : I) hy),
      fun y hy => Subtype.ext (by
        change radialProj (jarInteriorTranslate N (relGenLoopToEuclidean p) t y) =
          ((sphereBasepoint (d + 1) : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))
        rw [jarInteriorTranslate_eq_of_mem_boundaryJar hN
          (relGenLoopToEuclidean p)
          (fun z hz => by
            simpa [sphUpperCapBase] using congrArg Subtype.val (p.property.2 z hz)) hy]
        exact radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialJarInteriorTranslateRelGenLoop
    (N : ℕ) (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (hdist : ∀ y,
      dist (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y)
        (relGenLoopToEuclidean p y) ≤ 1 / 2)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate N (relGenLoopToEuclidean p) t y ≠ 0)
    (y : I^ Fin (k + 1)) :
    (((radialJarInteriorTranslateRelGenLoop N hN p hp hdist t ht hne).val y :
        Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (jarInteriorTranslate N (relGenLoopToEuclidean p) t y) :=
  rfl

/-- A cap-safe relative PL representative remains in the same relative homotopy class after a
sufficiently small jar-relative radial perturbation. -/
theorem relativeSpherePLApproximation_approx_homotopic_radialJarInteriorTranslate
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (A : RelativeSpherePLApproximation p hp)
    {t : EuclideanSpace ℝ (Fin (d + 2))} (ht : ‖t‖ < 1 / 8) :
    let hne : ∀ y,
        jarInteriorTranslate A.mesh (relGenLoopToEuclidean p) t y ≠ 0 :=
      jarInteriorTranslate_ne_zero_of_dist_le_half A.mesh_pos
        (relGenLoopToEuclidean p)
        (fun z hz => by
          simpa [sphUpperCapBase] using congrArg Subtype.val (p.property.2 z hz))
        (fun y => norm_coe_sph (p.val y)) A.dist_le_half
        (norm_coe_sph (sphereBasepoint (d + 1))) (by linarith)
    RelGenLoop.Homotopic A.approx
      (radialJarInteriorTranslateRelGenLoop A.mesh A.mesh_pos p hp A.dist_le_half
        t ht hne) := by
  dsimp only
  let hne : ∀ y,
      jarInteriorTranslate A.mesh (relGenLoopToEuclidean p) t y ≠ 0 :=
    jarInteriorTranslate_ne_zero_of_dist_le_half A.mesh_pos
      (relGenLoopToEuclidean p)
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (p.property.2 z hz))
      (fun y => norm_coe_sph (p.val y)) A.dist_le_half
      (norm_coe_sph (sphereBasepoint (d + 1))) (by linarith)
  let p' := radialJarInteriorTranslateRelGenLoop A.mesh A.mesh_pos p hp A.dist_le_half
    t ht hne
  have hHne : ∀ q,
      jarInteriorTranslateRadialHomotopyAmbient A.mesh
        (relGenLoopToEuclidean p) t q ≠ 0 :=
    jarInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
      (relGenLoopToEuclidean p) (fun y => norm_coe_sph (p.val y))
      A.dist_le_half (by linarith)
  refine ⟨⟨⟨fun sy =>
      ⟨radialProj (jarInteriorTranslateRadialHomotopyAmbient A.mesh
          (relGenLoopToEuclidean p) t sy),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hHne sy))⟩,
      Continuous.subtype_mk
        (continuous_radialProj
          (jarInteriorTranslateRadialHomotopyAmbient A.mesh
            (relGenLoopToEuclidean p) t).continuous hHne) _⟩,
    fun y => ?_, fun y => ?_⟩, fun s => ?_⟩
  · apply Subtype.ext
    change radialProj (jarInteriorTranslateRadialHomotopyAmbient A.mesh
      (relGenLoopToEuclidean p) t (0, y)) =
        ((A.approx.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [jarInteriorTranslateRadialHomotopyAmbient_zero]
    exact (A.coe_approx y).symm
  · apply Subtype.ext
    change radialProj (jarInteriorTranslateRadialHomotopyAmbient A.mesh
      (relGenLoopToEuclidean p) t (1, y)) =
        ((p'.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [jarInteriorTranslateRadialHomotopyAmbient_one]
    rfl
  · constructor
    · intro y hy
      rw [mem_sphUpperCap]
      change -(1 / 3 : ℝ) ≤
        radialProj (jarInteriorTranslateRadialHomotopyAmbient A.mesh
          (relGenLoopToEuclidean p) t (s, y)) (Fin.last (d + 1))
      exact jarInteriorTranslateRadialHomotopyAmbient_last_ge_neg_third
        A.mesh_pos p hp A.dist_le_half ht s hy
    · intro y hy
      apply Subtype.ext
      change radialProj (jarInteriorTranslateRadialHomotopyAmbient A.mesh
        (relGenLoopToEuclidean p) t (s, y)) =
          ((sphereBasepoint (d + 1) : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))
      rw [jarInteriorTranslateRadialHomotopyAmbient_eq_of_mem_boundaryJar
        A.mesh_pos (relGenLoopToEuclidean p)
        (fun z hz => by
          simpa [sphUpperCapBase] using congrArg Subtype.val (p.property.2 z hz)) s hy]
      exact radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1)))

/-! ### Stable relative-versus-absolute general position -/

/-- **Jar-relative pairwise general position in a sphere.** In the stable dimension range, a
relative sphere loop and a based sphere loop have homotopic representatives whose images meet
only at the distinguished basepoint. The homotopy of the relative loop preserves the upper-cap
condition on the full boundary and fixes the cubical boundary jar. -/
theorem exists_homotopic_relativeSphereLoop_sphereGenLoop_range_inter_subset_singleton
    (hdim : k + m + 1 ≤ d)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))) :
    ∃ (p' : RelGenLoop (k + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d))
      (g' : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))),
      RelGenLoop.Homotopic p p' ∧ _root_.GenLoop.Homotopic g g' ∧
      Set.range p'.val ∩ Set.range g' ⊆ {sphereBasepoint (d + 1)} := by
  obtain ⟨q, hq, A, hA⟩ := exists_homotopic_relativeSpherePLApproximation p
  obtain ⟨B⟩ := exists_spherePLApproximation g
  let E := EuclideanSpace ℝ (Fin (d + 2))
  have hdimE : (k + 1) + m + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨t, htball, hcore, hcollar⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_notMem_gridBaseConeSpan
      (volume : Measure E) A.mesh_pos (by omega) hdimE
      (relGenLoopToEuclidean q) (genLoopToEuclidean g)
      ((sphereBasepoint (d + 1) : Sph (d + 1)) : E) Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)⟩
  have ht : ‖t‖ < 1 / 8 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  let hne : ∀ y,
      jarInteriorTranslate A.mesh (relGenLoopToEuclidean q) t y ≠ 0 :=
    jarInteriorTranslate_ne_zero_of_dist_le_half A.mesh_pos
      (relGenLoopToEuclidean q)
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (q.property.2 z hz))
      (fun y => norm_coe_sph (q.val y)) A.dist_le_half
      (norm_coe_sph (sphereBasepoint (d + 1))) (by linarith)
  let p' := radialJarInteriorTranslateRelGenLoop A.mesh A.mesh_pos q hq A.dist_le_half
    t ht hne
  refine ⟨p', B.approx, hA.trans ?_, B.homotopic, ?_⟩
  · exact relativeSpherePLApproximation_approx_homotopic_radialJarInteriorTranslate
      q hq A ht
  · have hinter := radialProj_jarInteriorTranslate_inter_subset_singleton
      A.mesh_pos B.mesh_pos (relGenLoopToEuclidean q) (genLoopToEuclidean g)
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (q.property.2 z hz))
      (norm_coe_sph (sphereBasepoint (d + 1))) hne hcore hcollar
    rintro x ⟨hxp, hxg⟩
    obtain ⟨y, hy⟩ := hxp
    obtain ⟨z, hz⟩ := hxg
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    apply Set.mem_singleton_iff.mp
    apply hinter
    constructor
    · refine ⟨y, ?_⟩
      change radialProj (jarInteriorTranslate A.mesh (relGenLoopToEuclidean q) t y) =
        ((x : Sph (d + 1)) : E)
      rw [← hy]
      rfl
    · refine ⟨z, ?_⟩
      change radialProj (cubeGridAffineApprox m B.mesh (genLoopToEuclidean g) z) =
        ((x : Sph (d + 1)) : E)
      rw [← hz]
      exact (B.coe_approx z).symm

/-- Quotient-level form of jar-relative pairwise general position: every relative class and
absolute class in the stable dimension range have representatives meeting only at the sphere
basepoint. -/
theorem relHomotopyGroup_homotopyGroup_exists_generalPositionRepresentatives
    (hdim : k + m + 1 ≤ d)
    (a : π_rel (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (b : π_ m (Sph (d + 1)) (sphereBasepoint (d + 1))) :
    ∃ (p : RelGenLoop (k + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d))
      (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))),
      a = ⟦p⟧ ∧ b = ⟦g⟧ ∧
      Set.range p.val ∩ Set.range g ⊆ {sphereBasepoint (d + 1)} := by
  induction a using Quotient.inductionOn with
  | h p =>
      induction b using Quotient.inductionOn with
      | h g =>
          obtain ⟨p', g', hp, hg, hinter⟩ :=
            exists_homotopic_relativeSphereLoop_sphereGenLoop_range_inter_subset_singleton
              hdim p g
          exact ⟨p', g', Quotient.sound hp, Quotient.sound hg, hinter⟩

/-- **Pairwise general position for relative sphere-cap loops.** If the sum of the two source
dimensions is smaller than the target-sphere dimension, both relative classes have homotopic
representatives whose images meet only at the distinguished basepoint. -/
theorem exists_homotopic_relativeSphereLoops_range_inter_subset_singleton
    {l : ℕ} (hdim : k + l + 2 ≤ d)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (r : RelGenLoop (l + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ (p' : RelGenLoop (k + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d))
      (r' : RelGenLoop (l + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d)),
      RelGenLoop.Homotopic p p' ∧ RelGenLoop.Homotopic r r' ∧
      Set.range p'.val ∩ Set.range r'.val ⊆ {sphereBasepoint (d + 1)} := by
  obtain ⟨q, hq, A, hA⟩ := exists_homotopic_relativeSpherePLApproximation p
  obtain ⟨s, hs, B, hB⟩ := exists_homotopic_relativeSpherePLApproximation r
  let E := EuclideanSpace ℝ (Fin (d + 2))
  have hdimE : (k + 1) + (l + 1) + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨t, htball, hcore, hcollar⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_notMem_gridBaseConeSpan
      (volume : Measure E) A.mesh_pos (by omega) hdimE
      (relGenLoopToEuclidean q) (relGenLoopToEuclidean s)
      ((sphereBasepoint (d + 1) : Sph (d + 1)) : E) Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)⟩
  have ht : ‖t‖ < 1 / 8 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  let hne : ∀ y,
      jarInteriorTranslate A.mesh (relGenLoopToEuclidean q) t y ≠ 0 :=
    jarInteriorTranslate_ne_zero_of_dist_le_half A.mesh_pos
      (relGenLoopToEuclidean q)
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (q.property.2 z hz))
      (fun y => norm_coe_sph (q.val y)) A.dist_le_half
      (norm_coe_sph (sphereBasepoint (d + 1))) (by linarith)
  let p' := radialJarInteriorTranslateRelGenLoop A.mesh A.mesh_pos q hq A.dist_le_half
    t ht hne
  refine ⟨p', B.approx, hA.trans ?_, hB, ?_⟩
  · exact relativeSpherePLApproximation_approx_homotopic_radialJarInteriorTranslate
      q hq A ht
  · have hinter := radialProj_jarInteriorTranslate_inter_subset_singleton
      A.mesh_pos B.mesh_pos (relGenLoopToEuclidean q) (relGenLoopToEuclidean s)
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (q.property.2 z hz))
      (norm_coe_sph (sphereBasepoint (d + 1))) hne hcore hcollar
    rintro x ⟨hxp, hxr⟩
    obtain ⟨y, hy⟩ := hxp
    obtain ⟨z, hz⟩ := hxr
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    apply Set.mem_singleton_iff.mp
    apply hinter
    constructor
    · refine ⟨y, ?_⟩
      change radialProj (jarInteriorTranslate A.mesh (relGenLoopToEuclidean q) t y) =
        ((x : Sph (d + 1)) : E)
      rw [← hy]
      rfl
    · refine ⟨z, ?_⟩
      change radialProj
          (cubeGridAffineApprox (l + 1) B.mesh (relGenLoopToEuclidean s) z) =
        ((x : Sph (d + 1)) : E)
      rw [← hz]
      exact (B.coe_approx z).symm

/-- Quotient-level pairwise general position for two relative sphere-cap classes. -/
theorem relHomotopyGroups_exists_generalPositionRepresentatives
    {l : ℕ} (hdim : k + l + 2 ≤ d)
    (a : π_rel (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (b : π_rel (l + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ (p : RelGenLoop (k + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d))
      (r : RelGenLoop (l + 1) (Sph (d + 1))
          (sphUpperCap d) (sphUpperCapBase d)),
      a = ⟦p⟧ ∧ b = ⟦r⟧ ∧
      Set.range p.val ∩ Set.range r.val ⊆ {sphereBasepoint (d + 1)} := by
  induction a using Quotient.inductionOn with
  | h p =>
      induction b using Quotient.inductionOn with
      | h r =>
          obtain ⟨p', r', hp, hr, hinter⟩ :=
            exists_homotopic_relativeSphereLoops_range_inter_subset_singleton hdim p r
          exact ⟨p', r', Quotient.sound hp, Quotient.sound hr, hinter⟩

end Submission
