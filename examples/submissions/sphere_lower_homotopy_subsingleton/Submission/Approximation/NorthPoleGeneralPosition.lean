/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.CapExcisionClamp

/-!
# Relative general position against the north pole

A zero-dimensional generalized loop may select an arbitrary point because its cubical boundary
is empty.  We use the north pole as such a loop.  Every PL approximation of this constant
zero-cube is exactly the north pole, so the pairwise general-position theorem genuinely moves
only the relative representative and does not lose the distinguished point behind an existential
homotopic replacement.

Combining this observation with the punctured-sphere cap clamp gives an unconditional geometric
surjectivity theorem for cap excision in the ordinary point-avoidance range.  Besides validating
the clamp bridge, the result isolates why the stable range needs a stronger two-piece argument:
ordinary point avoidance accounts for one source dimension at a time.

## Main results

* `Submission.spherePLApproximation_northPoleGenLoopZero_approx_eq`
* `Submission.exists_homotopic_relativeSphereLoop_avoiding_sphNorthPole`
* `Submission.sphereSuspensionExcisionHomAt_surjective_of_dimension`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n N : ℕ}

theorem cubeGridAffineApprox_const (hN : 1 ≤ N) (b : F) (y : I^ Fin n) :
    cubeGridAffineApprox n N (ContinuousMap.const (I^ Fin n) b) y = b := by
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  simp only [ContinuousMap.const_apply]
  rw [← Finset.sum_smul, sum_gridCoeff_activeVerts hN, one_smul]

variable {d : ℕ}

/-- The zero-dimensional generalized loop selecting the north pole.  In dimension zero the cube
boundary is empty, so the nominal sphere basepoint imposes no restriction. -/
noncomputable def northPoleGenLoopZero (d : ℕ) :
    Ω^ (Fin 0) (Sph (d + 1)) (sphereBasepoint (d + 1)) :=
  ⟨ContinuousMap.const (I^ Fin 0) (sphNorthPole d), fun y hy =>
    isEmptyElim (⟨y, hy⟩ : ∂I^0)⟩

@[simp] theorem northPoleGenLoopZero_apply (d : ℕ) (y : I^ Fin 0) :
    northPoleGenLoopZero d y = sphNorthPole d :=
  rfl

theorem spherePLApproximation_northPoleGenLoopZero_approx_eq
    (B : SpherePLApproximation (northPoleGenLoopZero d)) (y : I^ Fin 0) :
    B.approx y = sphNorthPole d := by
  apply Subtype.ext
  rw [B.coe_approx]
  change radialProj (cubeGridAffineApprox 0 B.mesh
      (ContinuousMap.const (I^ Fin 0)
        ((sphNorthPole d : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))) y) =
    ((sphNorthPole d : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
  rw [cubeGridAffineApprox_const B.mesh_pos,
    radialProj_of_norm_eq_one (norm_coe_sph (sphNorthPole d))]

theorem sphNorthPole_mem_range_spherePLApproximation_northPoleGenLoopZero
    (B : SpherePLApproximation (northPoleGenLoopZero d)) :
    sphNorthPole d ∈ Set.range B.approx := by
  exact ⟨default, spherePLApproximation_northPoleGenLoopZero_approx_eq B default⟩

variable {k : ℕ}

/-- Ordinary relative general position against the zero-dimensional north-pole loop.  A relative
`(k+1)`-cube can be moved off the north pole whenever its dimension is strictly smaller than the
ambient sphere dimension. -/
theorem exists_homotopic_relativeSphereLoop_avoiding_sphNorthPole
    (hdim : k + 1 ≤ d)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ p' : RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d),
      RelGenLoop.Homotopic p p' ∧ ∀ y, p'.val y ≠ sphNorthPole d := by
  obtain ⟨q, hq, A, hA⟩ := exists_homotopic_relativeSpherePLApproximation p
  obtain ⟨B⟩ := exists_spherePLApproximation (northPoleGenLoopZero d)
  let E := EuclideanSpace ℝ (Fin (d + 2))
  have hdimE : (k + 1) + 0 + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨t, htball, hcore, hcollar⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_notMem_gridBaseConeSpan
      (n := k + 1) (m := 0) (N := A.mesh) (M := B.mesh)
      (volume : Measure E) A.mesh_pos (by omega) hdimE
      (relGenLoopToEuclidean q) (genLoopToEuclidean (northPoleGenLoopZero d))
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
  refine ⟨p', hA.trans ?_, ?_⟩
  · exact relativeSpherePLApproximation_approx_homotopic_radialJarInteriorTranslate
      q hq A ht
  · have hinter := radialProj_jarInteriorTranslate_inter_subset_singleton
      A.mesh_pos B.mesh_pos (relGenLoopToEuclidean q)
      (genLoopToEuclidean (northPoleGenLoopZero d))
      (fun z hz => by
        simpa [sphUpperCapBase] using congrArg Subtype.val (q.property.2 z hz))
      (norm_coe_sph (sphereBasepoint (d + 1))) hne hcore hcollar
    have hsphere : Set.range p'.val ∩ Set.range B.approx ⊆
        {sphereBasepoint (d + 1)} := by
      rintro x ⟨hxp, hxB⟩
      obtain ⟨y, hy⟩ := hxp
      obtain ⟨z, hz⟩ := hxB
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      apply Set.mem_singleton_iff.mp
      apply hinter
      constructor
      · refine ⟨y, ?_⟩
        change radialProj (jarInteriorTranslate A.mesh
          (relGenLoopToEuclidean q) t y) = ((x : Sph (d + 1)) : E)
        rw [← hy]
        rfl
      · refine ⟨z, ?_⟩
        change radialProj (cubeGridAffineApprox 0 B.mesh
          (genLoopToEuclidean (northPoleGenLoopZero d)) z) =
            ((x : Sph (d + 1)) : E)
        rw [← hz]
        exact (B.coe_approx z).symm
    intro y hy
    have hnorth : sphNorthPole d ∈ Set.range p'.val := ⟨y, hy⟩
    have hbase := Set.mem_singleton_iff.mp
      (hsphere ⟨hnorth,
        sphNorthPole_mem_range_spherePLApproximation_northPoleGenLoopZero B⟩)
    exact sphereBasepoint_ne_sphNorthPole d hbase.symm

/-- Every relative class in the ordinary point-avoidance range has a north-avoiding
representative. -/
theorem relHomotopyGroup_exists_representative_avoiding_sphNorthPole
    (hdim : k + 1 ≤ d)
    (a : π_rel (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ p : RelGenLoop (k + 1) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d),
      a = ⟦p⟧ ∧ ∀ y, p.val y ≠ sphNorthPole d := by
  induction a using Quotient.inductionOn with
  | _ p =>
      obtain ⟨p', hpp', hp'avoid⟩ :=
        exists_homotopic_relativeSphereLoop_avoiding_sphNorthPole hdim p
      exact ⟨p', Quotient.sound hpp', hp'avoid⟩

/-- Geometric cap-excision surjectivity in the ordinary point-avoidance range. -/
theorem sphereSuspensionExcisionHomAt_surjective_of_dimension
    (d q : ℕ) (hdim : q + 2 ≤ d) :
    Function.Surjective (sphereSuspensionExcisionHomAt d q) := by
  apply sphereSuspensionExcisionHomAt_surjective_of_avoiding_north q
  intro p
  exact exists_homotopic_relativeSphereLoop_avoiding_sphNorthPole
    (k := q + 1) (by omega) p

end Submission
