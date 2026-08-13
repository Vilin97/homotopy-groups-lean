/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.RelativeSphereHomotopyGeneralPosition

/-!
# General position relative to a varying cubical jar

The one-sided collar used for a relative loop usually starts at one constant value on its
boundary jar. For a time-first homotopy cube, however, the full jar also contains the two varying
endpoint maps. This file replaces the constant-jar obstruction by scaled collision sets over the
finite PL jar image.

For relative sphere homotopies the remaining spatial part of that jar is still the basepoint.
Consequently separation on the whole homotopy jar reduces to separation of the two endpoint PL
representatives. A small one-sided perturbation then extends this separation over every time
slice while preserving the upper-cap and spatial-jar conditions.

## Main results

* `Submission.exists_jarInteriorTranslate_radial_inter_subset_singleton_of_boundaryJar`
* `Submission.radial_cubeGridAffineApproxBoundaryJarRange_inter_subset_of_endpoints`
* `Submission.radialJarInteriorTranslateRelativeSphereHomotopy_homotopic`
* `Submission.exists_relativeSphereJarGeneralPositionHomotopy`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F]
variable (μ : Measure F) [μ.IsAddHaarMeasure]

variable {k m N M : ℕ}

/-! ### The varying PL image on a boundary jar -/

/-- The image of a cubical boundary jar under a grid approximation. -/
def cubeGridAffineApproxBoundaryJarRange
    (n N : ℕ) (g : C(I^ Fin n, F)) : Set F :=
  cubeGridAffineApprox n N g '' Cube.boundaryJar n

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
theorem cubeGridAffineApproxBoundaryJarRange_subset_boundaryRange
    (g : C(I^ Fin (k + 1), F)) :
    cubeGridAffineApproxBoundaryJarRange (k + 1) N g ⊆
      cubeGridAffineApproxBoundaryRange (k + 1) N g := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, Cube.boundaryJar_subset_boundary (k + 1) hy, rfl⟩

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- A jar-relative collar perturbation with a varying PL jar satisfies radial separation when
its core translation and all scaled collisions from the jar have been avoided. -/
theorem radialProj_jarInteriorTranslate_inter_subset_singleton_of_boundaryJar
    (hM : 1 ≤ M)
    (g : C(I^ Fin (k + 1), F)) (h : C(I^ Fin m, F)) {b t : F}
    (hne : ∀ y, jarInteriorTranslate N g t y ≠ 0)
    (hboundaryJar : radialProj ''
        cubeGridAffineApproxBoundaryJarRange (k + 1) N g ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b})
    (hcore : Disjoint
      ((fun x => x + t) '' Set.range (cubeGridAffineApprox (k + 1) N g))
      (gridConeSpan m M h))
    (hscaled : t ∉ scaledCollisionTranslations
      (cubeGridAffineApproxBoundaryRange (k + 1) N g) (gridConeSpan m M h)) :
    Set.range (fun y => radialProj (jarInteriorTranslate N g t y)) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  rintro q ⟨hqfirst, hqsecond⟩
  obtain ⟨y, hy⟩ := hqfirst
  obtain ⟨z, hz⟩ := hqsecond
  have heq : radialProj (jarInteriorTranslate N g t y) =
      radialProj (cubeGridAffineApprox m M h z) := hy.trans hz.symm
  have hxcone : jarInteriorTranslate N g t y ∈ gridConeSpan m M h :=
    mem_gridConeSpan_of_radialProj_eq_cubeGridAffineApprox hM h (hne y) z heq
  by_cases hw : cubeJarCollarWeight y = 1
  · have hxcore : jarInteriorTranslate N g t y ∈
        (fun x => x + t) '' Set.range (cubeGridAffineApprox (k + 1) N g) := by
      refine ⟨cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y),
        ⟨cubeCollarRetraction y, rfl⟩, ?_⟩
      simp [jarInteriorTranslate_apply, hw]
    exact (Set.disjoint_left.mp hcore hxcore hxcone).elim
  · have hRjar := cubeCollarRetraction_mem_boundaryJar_of_jarWeight_ne_one hw
    let a := cubeGridAffineApprox (k + 1) N g (cubeCollarRetraction y)
    have haJar : a ∈ cubeGridAffineApproxBoundaryJarRange (k + 1) N g :=
      ⟨cubeCollarRetraction y, hRjar, rfl⟩
    have haBoundary : a ∈ cubeGridAffineApproxBoundaryRange (k + 1) N g :=
      cubeGridAffineApproxBoundaryJarRange_subset_boundaryRange g haJar
    by_cases hw0 : cubeJarCollarWeight y = 0
    · apply hboundaryJar
      constructor
      · refine ⟨a, haJar, ?_⟩
        rw [← hy]
        simp [jarInteriorTranslate_apply, a, hw0]
      · exact ⟨z, hz⟩
    · exfalso
      apply hscaled
      refine ⟨a, haBoundary, jarInteriorTranslate N g t y, hxcone,
        cubeJarCollarWeight y, hw0, ?_⟩
      exact jarInteriorTranslate_apply g t y

include μ in
/-- **Jar-relative radial PL general position with a varying jar.** If the unperturbed radial
jar is already separated from a second radial PL image, an arbitrarily small one-sided collar
translation extends the separation over the whole cube. -/
theorem exists_jarInteriorTranslate_radial_inter_subset_singleton_of_boundaryJar
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hdim : (k + 1) + m + 2 ≤ finrank ℝ F)
    (g : C(I^ Fin (k + 1), F)) (h : C(I^ Fin m, F)) {b : F}
    (hgnorm : ∀ y, ‖g y‖ = 1)
    (hdist : ∀ y, dist (cubeGridAffineApprox (k + 1) N g y) (g y) ≤ 1 / 2)
    (hboundaryJar : radialProj ''
        cubeGridAffineApproxBoundaryJarRange (k + 1) N g ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b}) :
    ∃ t : F, ‖t‖ < 1 / 8 ∧
      (∀ y, jarInteriorTranslate N g t y ≠ 0) ∧
      Set.range (fun y => radialProj (jarInteriorTranslate N g t y)) ∩
        Set.range (fun z => radialProj (cubeGridAffineApprox m M h z)) ⊆ {b} := by
  obtain ⟨t, htball, hcore, hscaled⟩ :=
    exists_translation_disjoint_range_gridConeSpan_and_boundaryScaled
      μ hN hdim g h Metric.isOpen_ball
      ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)⟩
  have ht : ‖t‖ < 1 / 8 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  have hHne : ∀ p, jarInteriorTranslateRadialHomotopyAmbient N g t p ≠ 0 :=
    jarInteriorTranslateRadialHomotopyAmbient_ne_zero_of_dist_le_half
      g hgnorm hdist (by linarith)
  have hne : ∀ y, jarInteriorTranslate N g t y ≠ 0 := by
    intro y
    simpa using hHne (1, y)
  exact ⟨t, ht, hne,
    radialProj_jarInteriorTranslate_inter_subset_singleton_of_boundaryJar
      hM g h hne hboundaryJar hcore hscaled⟩

/-! ### Cap-safe application to a relative sphere homotopy -/

variable {d : ℕ}

/-- A time slice of a one-sided jar perturbation of a finite PL relative sphere homotopy. -/
noncomputable def radialJarInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (jarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)),
        mem_sphere_zero_iff_norm.mpr
          (norm_radialProj (hne (Fin.cons s y)))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        ((jarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous.comp (by fun_prop))
        (fun y => hne (Fin.cons s y))) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        let z := cubeCollarRetraction (Fin.cons s y)
        let v := cubeGridAffineApprox (k + 2) A.mesh
          (relativeSphereHomotopyToEuclidean H) z
        let c := cubeJarCollarWeight (Fin.cons s y)
        have hvnorm : 1 / 2 ≤ ‖v‖ :=
          cubeGridAffineApprox_norm_ge_half
            (relativeSphereHomotopyToEuclidean H)
            (fun q => norm_coe_sph (H (q 0, fun i => q i.succ)))
            A.dist_le_half z
        have hvlast : 0 ≤ v (Fin.last (d + 1)) := by
          dsimp only [v, z]
          rw [cubeCollarRetraction_cons]
          exact cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
            A.mesh_pos H hheight (collarCoord s)
              (cubeCollarRetraction_tail_mem_boundary hy)
        have hcI : c ∈ Set.Icc (0 : ℝ) 1 :=
          cubeJarCollarWeight_mem_Icc (Fin.cons s y)
        change -(1 / 3 : ℝ) ≤ radialProj (v + c • t) (Fin.last (d + 1))
        exact radialProj_add_smul_last_ge_neg_third
          v t c hvnorm hvlast hcI.1 hcI.2 ht,
      fun y hy => Subtype.ext (by
        have hfullJar : (Fin.cons s y : I^ Fin (k + 2)) ∈ ⊔I^(k + 2) :=
          Cube.mem_boundaryJar_cons s hy
        change radialProj (jarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) =
            ((sphereBasepoint (d + 1) : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2)))
        rw [jarInteriorTranslate_apply,
          cubeJarCollarWeight_eq_zero_of_mem_boundaryJar hfullJar,
          zero_smul, add_zero, cubeCollarRetraction_cons,
          cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar
            A.mesh_pos H hjar (collarCoord s)
              (cubeCollarRetraction_tail_mem_boundaryJar hy)]
        exact radialProj_of_norm_eq_one
          (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialJarInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) (y : I^ Fin (k + 1)) :
    (((radialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (jarInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) :=
  rfl

/-- The one-sided jar-perturbed slices form a homotopy through relative sphere loops. -/
theorem radialJarInteriorTranslateRelativeSphereHomotopy_homotopic
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic
      (radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 0)
      (radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 1) := by
  let G := jarInteriorTranslate A.mesh (relativeSphereHomotopyToEuclidean H) t
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
    exact (radialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).property.1 y hy
  · intro y hy
    exact (radialJarInteriorTranslateRelativeSphereHomotopySlice
      A t ht hne s).property.2 y hy

theorem radialJarInteriorTranslateRelativeSphereHomotopySlice_zero
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 0 =
      cubeCollarRetractionRelGenLoop (A.approxSlice 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  change radialProj (jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t (Fin.cons 0 y)) =
    radialProj (cubeGridAffineApprox (k + 2) A.mesh
      (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 0 (cubeCollarRetraction y)))
  rw [jarInteriorTranslate_apply,
    cubeJarCollarWeight_eq_zero_of_mem_boundaryJar (Cube.mem_boundaryJar_cons_zero y),
    zero_smul, add_zero, cubeCollarRetraction_cons, collarCoord_zero]

theorem radialJarInteriorTranslateRelativeSphereHomotopySlice_one
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 1 =
      cubeCollarRetractionRelGenLoop (A.approxSlice 1) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  change radialProj (jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t (Fin.cons 1 y)) =
    radialProj (cubeGridAffineApprox (k + 2) A.mesh
      (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 1 (cubeCollarRetraction y)))
  rw [jarInteriorTranslate_apply,
    cubeJarCollarWeight_eq_zero_of_mem_boundaryJar (Cube.mem_boundaryJar_cons_one y),
    zero_smul, add_zero, cubeCollarRetraction_cons, collarCoord_one]

theorem relativeSpherePLHomotopyApproximation_approxSlice_zero_homotopic_jarTranslate
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic (A.approxSlice 0)
      (radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 0) := by
  rw [radialJarInteriorTranslateRelativeSphereHomotopySlice_zero]
  exact relGenLoopHomotopic_cubeCollarRetraction (A.approxSlice 0)

theorem relativeSpherePLHomotopyApproximation_approxSlice_one_homotopic_jarTranslate
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2))) (ht : ‖t‖ < 1 / 8)
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic (A.approxSlice 1)
      (radialJarInteriorTranslateRelativeSphereHomotopySlice A t ht hne 1) := by
  rw [radialJarInteriorTranslateRelativeSphereHomotopySlice_one]
  exact relGenLoopHomotopic_cubeCollarRetraction (A.approxSlice 1)

/-- For a jar-based relative sphere homotopy, radial separation on the full time-first jar
reduces to separation on its two endpoint slices: the remaining spatial jar is the basepoint. -/
theorem radial_cubeGridAffineApproxBoundaryJarRange_inter_subset_of_endpoints
    (hN : 1 ≤ N)
    {R : Set (EuclideanSpace ℝ (Fin (d + 2)))}
    (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hzero : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) N
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 0 y))) ∩ R ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2)))})
    (hone : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) N
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 1 y))) ∩ R ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2)))}) :
    radialProj '' cubeGridAffineApproxBoundaryJarRange (k + 2) N
      (relativeSphereHomotopyToEuclidean H) ∩ R ⊆
        {((sphereBasepoint (d + 1) : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))} := by
  rintro x ⟨hxjar, hxR⟩
  obtain ⟨v, hv, hvx⟩ := hxjar
  obtain ⟨y, hy, hyv⟩ := hv
  have hcons : Fin.cons (y 0) (fun i => y i.succ) = y := Fin.cons_self_tail y
  rcases Cube.mem_boundaryJar_iff_splitAtFirst.mp hy with (hzeroTime | honeTime) | htail
  · apply hzero
    constructor
    · refine ⟨(fun i => y i.succ), ?_⟩
      calc
        radialProj (cubeGridAffineApprox (k + 2) N
            (relativeSphereHomotopyToEuclidean H)
              (Fin.cons 0 fun i => y i.succ)) = radialProj v := by
                rw [show (Fin.cons 0 fun i => y i.succ) = y from
                  (by simpa [hzeroTime] using hcons), hyv]
        _ = x := hvx
    · exact hxR
  · apply hone
    constructor
    · refine ⟨(fun i => y i.succ), ?_⟩
      calc
        radialProj (cubeGridAffineApprox (k + 2) N
            (relativeSphereHomotopyToEuclidean H)
              (Fin.cons 1 fun i => y i.succ)) = radialProj v := by
                rw [show (Fin.cons 1 fun i => y i.succ) = y from
                  (by simpa [honeTime] using hcons), hyv]
        _ = x := hvx
    · exact hxR
  · apply Set.mem_singleton_iff.mpr
    calc
      x = radialProj v := hvx.symm
      _ = radialProj (cubeGridAffineApprox (k + 2) N
          (relativeSphereHomotopyToEuclidean H)
            (Fin.cons (y 0) fun i => y i.succ)) := by rw [hcons, hyv]
      _ = radialProj
          (((sphereBasepoint (d + 1) : Sph (d + 1)) :
            EuclideanSpace ℝ (Fin (d + 2)))) := by
              rw [cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar
                hN H hjar (y 0) htail]
      _ = ((sphereBasepoint (d + 1) : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2))) :=
            radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1)))

/-- Sphere-valued separation of one PL homotopy slice from a sphere PL approximation implies
the corresponding ambient radial separation statement. -/
theorem radial_relativeSpherePLHomotopyApproximation_slice_inter_subset_singleton
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g) (s : I)
    (hsep : Set.range (A.approxSlice s).val ∩ Set.range B.approx ⊆
      {sphereBasepoint (d + 1)}) :
    Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) A.mesh
        (relativeSphereHomotopyToEuclidean H) (Fin.cons s y))) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m B.mesh
        (genLoopToEuclidean g) z)) ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2)))} := by
  rintro v ⟨hvfirst, hvsecond⟩
  obtain ⟨y, hy⟩ := hvfirst
  obtain ⟨z, hz⟩ := hvsecond
  have hyz : (A.approxSlice s).val y = B.approx z := by
    apply Subtype.ext
    calc
      (((A.approxSlice s).val y : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2))) =
          radialProj (cubeGridAffineApprox (k + 2) A.mesh
            (relativeSphereHomotopyToEuclidean H) (Fin.cons s y)) := rfl
      _ = v := hy
      _ = radialProj (cubeGridAffineApprox m B.mesh
          (genLoopToEuclidean g) z) := hz.symm
      _ = (((B.approx z : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))) := (B.coe_approx z).symm
  have hybase : (A.approxSlice s).val y = sphereBasepoint (d + 1) :=
    Set.mem_singleton_iff.mp (hsep ⟨⟨y, rfl⟩, ⟨z, hyz.symm⟩⟩)
  apply Set.mem_singleton_iff.mpr
  calc
    v = (((A.approxSlice s).val y : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := by
          rw [show (((A.approxSlice s).val y : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2))) =
              radialProj (cubeGridAffineApprox (k + 2) A.mesh
                (relativeSphereHomotopyToEuclidean H) (Fin.cons s y)) from rfl]
          exact hy.symm
    _ = ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := congrArg Subtype.val hybase

/-- Radial projection of the one-sided jar perturbation on the whole homotopy cube. -/
noncomputable def radialJarInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    C(I^ Fin (k + 2), Sph (d + 1)) :=
  ⟨fun y =>
      ⟨radialProj (jarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t y),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne y))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        (jarInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous hne) _⟩

@[simp] theorem coe_radialJarInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (y : I^ Fin (k + 2)) :
    ((radialJarInteriorTranslateRelativeSphereHomotopyCube A t hne y :
      Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (jarInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t y) :=
  rfl

/-- Stable general-position data for an entire relative sphere homotopy, obtained by a
one-sided collar perturbation relative to its varying full jar. -/
structure RelativeSphereJarGeneralPositionHomotopy
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g) where
  translation : EuclideanSpace ℝ (Fin (d + 2))
  translation_norm_lt_eighth : ‖translation‖ < 1 / 8
  perturbed_ne_zero : ∀ y, jarInteriorTranslate A.mesh
    (relativeSphereHomotopyToEuclidean H) translation y ≠ 0
  range_inter_subset_singleton :
    Set.range (radialJarInteriorTranslateRelativeSphereHomotopyCube
      A translation perturbed_ne_zero) ∩ Set.range B.approx ⊆
        {sphereBasepoint (d + 1)}

namespace RelativeSphereJarGeneralPositionHomotopy

noncomputable def start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialJarInteriorTranslateRelativeSphereHomotopySlice A D.translation
    D.translation_norm_lt_eighth D.perturbed_ne_zero 0

noncomputable def finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialJarInteriorTranslateRelativeSphereHomotopySlice A D.translation
    D.translation_norm_lt_eighth D.perturbed_ne_zero 1

theorem approxStart_homotopic_start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 0) D.start :=
  relativeSpherePLHomotopyApproximation_approxSlice_zero_homotopic_jarTranslate
    A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero

theorem approxFinish_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 1) D.finish :=
  relativeSpherePLHomotopyApproximation_approxSlice_one_homotopic_jarTranslate
    A D.translation D.translation_norm_lt_eighth D.perturbed_ne_zero

theorem start_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic D.start D.finish :=
  radialJarInteriorTranslateRelativeSphereHomotopy_homotopic A D.translation
    D.translation_norm_lt_eighth D.perturbed_ne_zero

theorem slice_range_inter_subset_singleton
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereJarGeneralPositionHomotopy A g B) (s : I) :
    Set.range (radialJarInteriorTranslateRelativeSphereHomotopySlice A D.translation
      D.translation_norm_lt_eighth D.perturbed_ne_zero s).val ∩
        Set.range B.approx ⊆ {sphereBasepoint (d + 1)} := by
  rintro x ⟨hxfirst, hxsecond⟩
  apply D.range_inter_subset_singleton
  constructor
  · obtain ⟨y, hy⟩ := hxfirst
    refine ⟨Fin.cons s y, ?_⟩
    apply Subtype.ext
    change radialProj (jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) D.translation (Fin.cons s y)) =
        ((x : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [← hy]
    rfl
  · exact hxsecond

end RelativeSphereJarGeneralPositionHomotopy

/-- **Stable relative-homotopy general position.** If both endpoint PL representatives of a
relative sphere homotopy are separated from a fixed based sphere PL map, one cap-safe homotopy
between collar-reparametrized endpoints can be chosen so that every slice remains separated. -/
theorem exists_relativeSphereJarGeneralPositionHomotopy
    (hdim : k + m + 2 ≤ d)
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g)
    (hzero : Set.range (A.approxSlice 0).val ∩ Set.range B.approx ⊆
      {sphereBasepoint (d + 1)})
    (hone : Set.range (A.approxSlice 1).val ∩ Set.range B.approx ⊆
      {sphereBasepoint (d + 1)}) :
    Nonempty (RelativeSphereJarGeneralPositionHomotopy A g B) := by
  let E := EuclideanSpace ℝ (Fin (d + 2))
  let R : Set E := Set.range (fun z => radialProj (cubeGridAffineApprox m B.mesh
    (genLoopToEuclidean g) z))
  have hdimE : (k + 2) + m + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hzeroE : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) A.mesh
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 0 y))) ∩ R ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) : E)} :=
    radial_relativeSpherePLHomotopyApproximation_slice_inter_subset_singleton
      A g B 0 hzero
  have honeE : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) A.mesh
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 1 y))) ∩ R ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) : E)} :=
    radial_relativeSpherePLHomotopyApproximation_slice_inter_subset_singleton
      A g B 1 hone
  have hboundaryJar : radialProj '' cubeGridAffineApproxBoundaryJarRange
        (k + 2) A.mesh (relativeSphereHomotopyToEuclidean H) ∩ R ⊆
      {((sphereBasepoint (d + 1) : Sph (d + 1)) : E)} :=
    radial_cubeGridAffineApproxBoundaryJarRange_inter_subset_of_endpoints
      A.mesh_pos H hjar hzeroE honeE
  obtain ⟨t, ht, hne, hinter⟩ :=
    exists_jarInteriorTranslate_radial_inter_subset_singleton_of_boundaryJar
      (volume : Measure E) A.mesh_pos B.mesh_pos hdimE
      (relativeSphereHomotopyToEuclidean H) (genLoopToEuclidean g)
      (fun y => norm_coe_sph (H (y 0, fun i => y i.succ)))
      A.dist_le_half hboundaryJar
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
    change radialProj (jarInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y) = ((x : Sph (d + 1)) : E)
    rw [← hy]
    rfl
  · refine ⟨z, ?_⟩
    change radialProj (cubeGridAffineApprox m B.mesh
      (genLoopToEuclidean g) z) = ((x : Sph (d + 1)) : E)
    rw [← hz]
    exact (B.coe_approx z).symm

end Submission
