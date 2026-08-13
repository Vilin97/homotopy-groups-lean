/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.RelativeSphereGeneralPosition
import Submission.Approximation.RelativeSphereHomotopy

/-!
# Stable general position for relative sphere homotopies

This file combines simultaneous finite PL approximation of a relative sphere homotopy with
general position relative to a varying cubical boundary. A full cubical collar perturbation
vanishes on every spatial face. Consequently its radial projection remains inside the upper cap
on the spatial boundary, fixes the boundary jar, and gives a homotopy through relative loops.

When the unperturbed radial PL boundary is already separated from a second based PL sphere map,
the stable dimension inequality lets one extend the separation over the entire homotopy cube.
Both endpoint relative homotopy classes are unchanged.

## Main results

* `Submission.relGenLoopHomotopic_cubeCollarRetraction`
* `Submission.radialBoundaryInteriorTranslateRelativeSphereHomotopy_homotopic`
* `Submission.radial_cubeGridAffineApproxBoundaryRange_inter_subset_of_endpoints_and_spatial`
* `Submission.exists_relativeSphereBoundaryGeneralPositionHomotopy`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {k m N d : ℕ}

/-! ### Collar retraction on a time-first cube -/

@[simp] theorem cubeCollarRetraction_cons (s : I) (y : I^ Fin (k + 1)) :
    cubeCollarRetraction (Fin.cons s y) =
      Fin.cons (collarCoord s) (cubeCollarRetraction y) := by
  ext i
  refine Fin.cases ?_ ?_ i <;> simp [cubeCollarRetraction]

theorem cubeCollarRetraction_tail_mem_boundary
    {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    cubeCollarRetraction y ∈ ∂I^(k + 1) :=
  cubeCollarRetraction_mem_boundary_of_mem_boundary hy

theorem cubeCollarRetraction_tail_mem_boundaryJar
    {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeCollarRetraction y ∈ ⊔I^(k + 1) :=
  cubeCollarRetraction_mem_boundaryJar_of_mem_boundaryJar hy

/-! ### Relative loops under the cubical collar retraction -/

/-- Precompose a relative generalized loop with the coordinatewise cubical collar retraction. -/
noncomputable def cubeCollarRetractionRelGenLoop
    {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (k + 1) X A a) : RelGenLoop (k + 1) X A a :=
  ⟨p.val.comp ⟨cubeCollarRetraction, continuous_cubeCollarRetraction⟩,
    ⟨fun _ hy => p.property.1 _
        (cubeCollarRetraction_mem_boundary_of_mem_boundary hy),
      fun _ hy => p.property.2 _
        (cubeCollarRetraction_mem_boundaryJar_of_mem_boundaryJar hy)⟩⟩

@[simp] theorem cubeCollarRetractionRelGenLoop_apply
    {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (k + 1) X A a) (y : I^ Fin (k + 1)) :
    (cubeCollarRetractionRelGenLoop p).val y = p.val (cubeCollarRetraction y) :=
  rfl

/-- Coordinatewise collar retraction does not change a relative homotopy class. -/
theorem relGenLoopHomotopic_cubeCollarRetraction
    {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (k + 1) X A a) :
    RelGenLoop.Homotopic p (cubeCollarRetractionRelGenLoop p) := by
  refine ⟨⟨⟨fun sy => p.val (cubeCollarRetractionHomotopyPoint sy), by
      exact p.val.continuous.comp' continuous_cubeCollarRetractionHomotopyPoint⟩,
    fun y => ?_, fun y => ?_⟩, fun s => ?_⟩
  · change p.val (cubeCollarRetractionHomotopyPoint (0, y)) = p.val y
    rw [cubeCollarRetractionHomotopyPoint_zero]
  · change p.val (cubeCollarRetractionHomotopyPoint (1, y)) =
      p.val (cubeCollarRetraction y)
    rw [cubeCollarRetractionHomotopyPoint_one]
  · constructor
    · intro y hy
      exact p.property.1 _ (cubeCollarRetractionHomotopyPoint_mem_boundary s hy)
    · intro y hy
      exact p.property.2 _ (cubeCollarRetractionHomotopyPoint_mem_boundaryJar s hy)

/-! ### Boundary-relative perturbation of a sphere homotopy cube -/

/-- A time slice of the radial full-collar perturbation of a finite PL homotopy cube. The full
collar vanishes on every spatial face, so each slice remains a relative sphere loop. -/
noncomputable def radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (basedInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)),
        mem_sphere_zero_iff_norm.mpr
          (norm_radialProj (hne (Fin.cons s y)))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        ((basedInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous.comp (by fun_prop))
        (fun y => hne (Fin.cons s y))) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤ radialProj
          (basedInteriorTranslate A.mesh
            (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y))
              (Fin.last (d + 1))
        rw [basedInteriorTranslate_apply,
          cubeCollarWeight_eq_zero_of_mem_boundary (Cube.mem_boundary_cons s hy),
          zero_smul, add_zero, cubeCollarRetraction_cons]
        exact le_trans (by norm_num) (radialProj_last_nonneg
          (cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
            A.mesh_pos H hheight (collarCoord s)
              (cubeCollarRetraction_tail_mem_boundary hy))),
      fun y hy => Subtype.ext (by
        change radialProj (basedInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) =
            ((sphereBasepoint (d + 1) : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2)))
        rw [basedInteriorTranslate_apply,
          cubeCollarWeight_eq_zero_of_mem_boundary
            (Cube.mem_boundary_cons s (Cube.boundaryJar_subset_boundary (k + 1) hy)),
          zero_smul, add_zero, cubeCollarRetraction_cons,
          cubeGridAffineApprox_relativeSphereHomotopy_eq_on_boundaryJar
            A.mesh_pos H hjar (collarCoord s)
              (cubeCollarRetraction_tail_mem_boundaryJar hy)]
        exact radialProj_of_norm_eq_one
          (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (s : I) (y : I^ Fin (k + 1)) :
    (((radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
      A t hne s).val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (basedInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t (Fin.cons s y)) :=
  rfl

/-- The perturbed slices form a homotopy through relative sphere loops. -/
theorem radialBoundaryInteriorTranslateRelativeSphereHomotopy_homotopic
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic
      (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 0)
      (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 1) := by
  let G := basedInteriorTranslate A.mesh
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
    exact (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
      A t hne s).property.1 y hy
  · intro y hy
    exact (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
      A t hne s).property.2 y hy

theorem radialBoundaryInteriorTranslateRelativeSphereHomotopySlice_zero
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 0 =
      cubeCollarRetractionRelGenLoop (A.approxSlice 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  change radialProj (basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t (Fin.cons 0 y)) =
    radialProj (cubeGridAffineApprox (k + 2) A.mesh
      (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 0 (cubeCollarRetraction y)))
  rw [basedInteriorTranslate_apply,
    cubeCollarWeight_eq_zero_of_mem_boundary
      (show (Fin.cons 0 y : I^ Fin (k + 2)) ∈ ∂I^(k + 2) from
        ⟨0, Or.inl rfl⟩),
    zero_smul, add_zero, cubeCollarRetraction_cons, collarCoord_zero]

theorem radialBoundaryInteriorTranslateRelativeSphereHomotopySlice_one
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 1 =
      cubeCollarRetractionRelGenLoop (A.approxSlice 1) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  apply Subtype.ext
  change radialProj (basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t (Fin.cons 1 y)) =
    radialProj (cubeGridAffineApprox (k + 2) A.mesh
      (relativeSphereHomotopyToEuclidean H)
        (Fin.cons 1 (cubeCollarRetraction y)))
  rw [basedInteriorTranslate_apply,
    cubeCollarWeight_eq_zero_of_mem_boundary
      (show (Fin.cons 1 y : I^ Fin (k + 2)) ∈ ∂I^(k + 2) from
        ⟨0, Or.inr rfl⟩),
    zero_smul, add_zero, cubeCollarRetraction_cons, collarCoord_one]

theorem relativeSpherePLHomotopyApproximation_approxSlice_zero_homotopic_boundaryTranslate
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic (A.approxSlice 0)
      (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 0) := by
  rw [radialBoundaryInteriorTranslateRelativeSphereHomotopySlice_zero]
  exact relGenLoopHomotopic_cubeCollarRetraction (A.approxSlice 0)

theorem relativeSpherePLHomotopyApproximation_approxSlice_one_homotopic_boundaryTranslate
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    RelGenLoop.Homotopic (A.approxSlice 1)
      (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice A t hne 1) := by
  rw [radialBoundaryInteriorTranslateRelativeSphereHomotopySlice_one]
  exact relGenLoopHomotopic_cubeCollarRetraction (A.approxSlice 1)

/-! ### Stable general position relative to the full homotopy boundary -/

/-- Radial projection of the full-collar perturbation, bundled on the whole homotopy cube. -/
noncomputable def radialBoundaryInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0) :
    C(I^ Fin (k + 2), Sph (d + 1)) :=
  ⟨fun y =>
      ⟨radialProj (basedInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t y),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne y))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        (basedInteriorTranslate A.mesh
          (relativeSphereHomotopyToEuclidean H) t).continuous hne) _⟩

@[simp] theorem coe_radialBoundaryInteriorTranslateRelativeSphereHomotopyCube
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (t : EuclideanSpace ℝ (Fin (d + 2)))
    (hne : ∀ y, basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y ≠ 0)
    (y : I^ Fin (k + 2)) :
    ((radialBoundaryInteriorTranslateRelativeSphereHomotopyCube A t hne y :
      Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (basedInteriorTranslate A.mesh
        (relativeSphereHomotopyToEuclidean H) t y) :=
  rfl

/-- Data produced by boundary-relative stable general position for a relative sphere homotopy
and a based sphere PL map. -/
structure RelativeSphereBoundaryGeneralPositionHomotopy
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g) where
  translation : EuclideanSpace ℝ (Fin (d + 2))
  translation_norm_lt_half : ‖translation‖ < 1 / 2
  perturbed_ne_zero : ∀ y, basedInteriorTranslate A.mesh
    (relativeSphereHomotopyToEuclidean H) translation y ≠ 0
  range_inter_subset_singleton :
    Set.range (radialBoundaryInteriorTranslateRelativeSphereHomotopyCube
      A translation perturbed_ne_zero) ∩ Set.range B.approx ⊆
        {sphereBasepoint (d + 1)}

namespace RelativeSphereBoundaryGeneralPositionHomotopy

/-- The initial relative loop of a boundary-general-position homotopy. -/
noncomputable def start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
    A D.translation D.perturbed_ne_zero 0

/-- The final relative loop of a boundary-general-position homotopy. -/
noncomputable def finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
    A D.translation D.perturbed_ne_zero 1

theorem approxStart_homotopic_start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 0) D.start :=
  relativeSpherePLHomotopyApproximation_approxSlice_zero_homotopic_boundaryTranslate
    A D.translation D.perturbed_ne_zero

theorem approxFinish_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (A.approxSlice 1) D.finish :=
  relativeSpherePLHomotopyApproximation_approxSlice_one_homotopic_boundaryTranslate
    A D.translation D.perturbed_ne_zero

theorem start_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic D.start D.finish :=
  radialBoundaryInteriorTranslateRelativeSphereHomotopy_homotopic
    A D.translation D.perturbed_ne_zero

theorem originalStart_homotopic_start
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (relativeSphereHomotopySlice H hheight hjar 0) D.start :=
  (A.originalSlice_homotopic_approxSlice 0).trans D.approxStart_homotopic_start

theorem originalFinish_homotopic_finish
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) :
    RelGenLoop.Homotopic (relativeSphereHomotopySlice H hheight hjar 1) D.finish :=
  (A.originalSlice_homotopic_approxSlice 1).trans D.approxFinish_homotopic_finish

/-- Every time slice of the perturbed homotopy is separated from the second PL image. -/
theorem slice_range_inter_subset_singleton
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    {A : RelativeSpherePLHomotopyApproximation H hheight hjar}
    {g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1))}
    {B : SpherePLApproximation g}
    (D : RelativeSphereBoundaryGeneralPositionHomotopy A g B) (s : I) :
    Set.range (radialBoundaryInteriorTranslateRelativeSphereHomotopySlice
      A D.translation D.perturbed_ne_zero s).val ∩ Set.range B.approx ⊆
        {sphereBasepoint (d + 1)} := by
  rintro x ⟨hxfirst, hxsecond⟩
  apply D.range_inter_subset_singleton
  constructor
  · obtain ⟨y, hy⟩ := hxfirst
    refine ⟨Fin.cons s y, ?_⟩
    apply Subtype.ext
    change radialProj (basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) D.translation (Fin.cons s y)) =
        ((x : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
    rw [← hy]
    rfl
  · exact hxsecond

end RelativeSphereBoundaryGeneralPositionHomotopy

/-- To verify radial separation on the boundary of a time-first homotopy cube, it suffices to
verify it on the two endpoint slices and on the spatial boundary cylinder. -/
theorem radial_cubeGridAffineApproxBoundaryRange_inter_subset_of_endpoints_and_spatial
    {R : Set (EuclideanSpace ℝ (Fin (d + 2)))} {b : EuclideanSpace ℝ (Fin (d + 2))}
    (N : ℕ) (H : C(I × I^ Fin (k + 1), Sph (d + 1)))
    (hzero : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) N
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 0 y))) ∩ R ⊆ {b})
    (hone : Set.range (fun y => radialProj (cubeGridAffineApprox (k + 2) N
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 1 y))) ∩ R ⊆ {b})
    (hspatial : Set.range (fun sy : I × {y : I^ Fin (k + 1) // y ∈ ∂I^(k + 1)} =>
        radialProj (cubeGridAffineApprox (k + 2) N
          (relativeSphereHomotopyToEuclidean H) (Fin.cons sy.1 sy.2))) ∩ R ⊆ {b}) :
    radialProj '' cubeGridAffineApproxBoundaryRange (k + 2) N
      (relativeSphereHomotopyToEuclidean H) ∩ R ⊆ {b} := by
  rintro x ⟨hxboundary, hxR⟩
  obtain ⟨v, hv, hvx⟩ := hxboundary
  obtain ⟨y, hy, hyv⟩ := hv
  have hcons : Fin.cons (y 0) (fun i => y i.succ) = y := Fin.cons_self_tail y
  rcases Cube.mem_boundary_iff_splitAtFirst.mp hy with (hzeroTime | honeTime) | htail
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
  · apply hspatial
    constructor
    · refine ⟨⟨y 0, ⟨(fun i => y i.succ), htail⟩⟩, ?_⟩
      calc
        radialProj (cubeGridAffineApprox (k + 2) N
            (relativeSphereHomotopyToEuclidean H)
              (Fin.cons (y 0) fun i => y i.succ)) = radialProj v := by
                rw [hcons, hyv]
        _ = x := hvx
    · exact hxR

/-- **Stable general position relative to a varying homotopy boundary.** If the radial PL
boundary of a relative homotopy cube already meets a based sphere PL image only at the basepoint,
then a full-collar perturbation extends that separation over the entire homotopy. Its time slices
remain cap-safe relative loops, and both endpoint classes are unchanged. -/
theorem exists_relativeSphereBoundaryGeneralPositionHomotopy
    (hdim : k + m + 2 ≤ d)
    {H : C(I × I^ Fin (k + 1), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g : Ω^ (Fin m) (Sph (d + 1)) (sphereBasepoint (d + 1)))
    (B : SpherePLApproximation g)
    (hboundary : radialProj '' cubeGridAffineApproxBoundaryRange
        (k + 2) A.mesh (relativeSphereHomotopyToEuclidean H) ∩
      Set.range (fun z => radialProj (cubeGridAffineApprox m B.mesh
        (genLoopToEuclidean g) z)) ⊆
        {((sphereBasepoint (d + 1) : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))}) :
    Nonempty (RelativeSphereBoundaryGeneralPositionHomotopy A g B) := by
  let E := EuclideanSpace ℝ (Fin (d + 2))
  have hdimE : (k + 2) + m + 2 ≤ finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    omega
  obtain ⟨t, ht, hne, hinter⟩ :=
    exists_boundaryInteriorTranslate_radial_inter_subset_singleton
      (volume : Measure E) A.mesh_pos B.mesh_pos hdimE
      (relativeSphereHomotopyToEuclidean H) (genLoopToEuclidean g)
      (fun y => norm_coe_sph (H (y 0, fun i => y i.succ)))
      A.dist_le_half hboundary
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
    change radialProj (basedInteriorTranslate A.mesh
      (relativeSphereHomotopyToEuclidean H) t y) =
        ((x : Sph (d + 1)) : E)
    rw [← hy]
    rfl
  · refine ⟨z, ?_⟩
    change radialProj (cubeGridAffineApprox m B.mesh
      (genLoopToEuclidean g) z) = ((x : Sph (d + 1)) : E)
    rw [← hz]
    exact (B.coe_approx z).symm

end Submission
