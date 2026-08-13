/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereReducedSuspensionStable
import Submission.SphereSuspensionGeneral
import Submission.SphereSuspensionReduction

/-!
# Sphere-map representatives of reduced suspension

This file identifies the output of the cubically defined numerical reduced-suspension
homomorphism on any class represented by a based sphere map.  The only source-coordinate
correction is the explicit homeomorphism obtained by reducing the suspended canonical cubical
sphere generator.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The diagonal homotopy class of the meridian-collapse comparison in sphere coordinates. -/
noncomputable def sphereSuspensionReductionClass (n : ℕ) :
    π_ (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  sphereTargetMapClass (n + 1) (sphereSuspensionReductionMap n)
    (sphereSuspensionReductionMap_basepoint n)

/-- The diagonal source-coordinate class built into numerical reduced suspension. -/
noncomputable def sphereReducedSuspensionSourceClass (q : ℕ) :
    π_ (q + 2) (Sph (q + 2)) (sphereBasepoint (q + 2)) :=
  sphereTargetMapClass (q + 2)
    (sphereDiagonalReducedSuspensionGeneratorMap q)
    (sphereDiagonalReducedSuspensionGeneratorMap_basepoint q)

/-- The source-coordinate class is the reduced suspension of the canonical diagonal sphere
generator. -/
theorem sphereReducedSuspensionSourceClass_eq_generator_image (q : ℕ) :
    sphereReducedSuspensionSourceClass q =
      sphereDiagonalReducedSuspensionHom q (sphereGeneratorClass (q + 1)) := by
  rw [sphereDiagonalReducedSuspensionHom_generator]
  rfl

/-- The source-coordinate class is nontrivial. -/
theorem sphereReducedSuspensionSourceClass_ne_one (q : ℕ) :
    sphereReducedSuspensionSourceClass q ≠ 1 := by
  rw [sphereReducedSuspensionSourceClass_eq_generator_image]
  intro h
  apply sphereGeneratorClass_ne_one q
  apply (sphereDiagonalReducedSuspensionHom_bijective q).1
  rw [map_one]
  exact h

/-- The source-coordinate class generates the target diagonal homotopy group. -/
theorem sphereReducedSuspensionSourceClass_generates (q : ℕ) :
    ∀ x : π_ (q + 2) (Sph (q + 2)) (sphereBasepoint (q + 2)),
      x ∈ Subgroup.zpowers (sphereReducedSuspensionSourceClass q) := by
  rw [sphereReducedSuspensionSourceClass_eq_generator_image]
  exact sphereDiagonalReducedSuspensionHom_generator_generates q

/-- The exact cubical representative used by numerical reduced suspension. -/
noncomputable def genLoopSphereReducedSuspension (m q : ℕ)
    (α : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m)) :
    Ω^ (Fin (q + 2)) (Sph (m + 1)) (sphereBasepoint (m + 1)) :=
  GenLoop.congr (sphereBasepoint (m + 1)) (finSuccEquiv (q + 1)).symm
    (GenLoop.map
      ⟨ReducedSusp.sphereHomeomorph m (sphereBasepoint m),
        (ReducedSusp.sphereHomeomorph m (sphereBasepoint m)).continuous⟩
      (ReducedSusp.sphereHomeomorph_base m (sphereBasepoint m))
      (GenLoop.reducedSuspension α))

@[simp]
theorem genLoopSphereReducedSuspension_apply (m q : ℕ)
    (α : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m))
    (u : I^ Fin (q + 2)) :
    genLoopSphereReducedSuspension m q α u =
      ReducedSusp.sphereHomeomorph m (sphereBasepoint m)
        (ReducedSusp.mk (sphereBasepoint m)
          (u 0, α (fun i ↦ u i.succ))) :=
  rfl

/-- Evaluation of the numerical reduced-suspension homomorphism on a cubical representative. -/
@[simp]
theorem sphereReducedSuspensionPiHom_mk (m q : ℕ)
    (α : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m)) :
    sphereReducedSuspensionPiHom m q
        (⟦α⟧ : π_ (q + 1) (Sph m) (sphereBasepoint m)) =
      (⟦genLoopSphereReducedSuspension m q α⟧ :
        π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1))) :=
  rfl

/-- On a class represented by `f : S^(q+1) ⟶ S^m`, numerical reduced suspension is represented
by the reduced suspension of `f`, precomposed with the maintained source-coordinate
homeomorphism. -/
theorem sphereReducedSuspensionPiHom_sphereTargetMapClass (m q : ℕ)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    sphereReducedSuspensionPiHom m q
        (sphereTargetMapClass (q + 1) f hf) =
      sphereTargetMapClass (q + 2)
        ((sphereReducedSuspensionMap (q + 1) m f hf).comp
          (sphereDiagonalReducedSuspensionGeneratorMap q))
        (by
          rw [ContinuousMap.comp_apply,
            sphereDiagonalReducedSuspensionGeneratorMap_basepoint,
            sphereReducedSuspensionMap_basepoint]) := by
  rw [sphereTargetMapClass, sphereReducedSuspensionPiHom_mk, sphereTargetMapClass]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro u
  change genLoopSphereReducedSuspension m q
      (sphereTargetMapGenLoop (q + 1) f hf) u =
    sphereReducedSuspensionMap (q + 1) m f hf
      (sphereDiagonalReducedSuspensionGeneratorMap q (cubeToSphere (q + 2) u))
  rw [genLoopSphereReducedSuspension_apply]
  have hsource := congrArg
    (fun g : C(I^ Fin (q + 2), Sph (q + 2)) ↦ g u)
    (targetGenLoopSphereMap_comp_cubeToSphere (q + 1)
      (sphereDiagonalReducedSuspensionGeneratorLoop q))
  change sphereDiagonalReducedSuspensionGeneratorMap q (cubeToSphere (q + 2) u) =
    sphereDiagonalReducedSuspensionGeneratorLoop q u at hsource
  rw [hsource]
  simp only [sphereTargetMapGenLoop_apply,
    sphereDiagonalReducedSuspensionGeneratorLoop_apply,
    reducedSuspensionSphereGeneratorLoop_apply,
    sphereReducedSuspensionMap, ContinuousMap.comp_apply]
  change ReducedSusp.sphereHomeomorph m (sphereBasepoint m)
      (ReducedSusp.mk (sphereBasepoint m)
        (u 0, f (cubeToSphere (q + 1) (fun i ↦ u i.succ)))) =
    ReducedSusp.sphereHomeomorph m (sphereBasepoint m)
      (ReducedSusp.map (sphereBasepoint (q + 1)) (sphereBasepoint m) f hf
        ((ReducedSusp.sphereHomeomorph (q + 1) (sphereBasepoint (q + 1))).symm
          (ReducedSusp.sphereHomeomorph (q + 1) (sphereBasepoint (q + 1))
            (ReducedSusp.mk (sphereBasepoint (q + 1))
              (u 0, cubeToSphere (q + 1) (fun i ↦ u i.succ))))))
  rw [Homeomorph.symm_apply_apply, ReducedSusp.map_mk]

/-- Equivalently, numerical reduced suspension applies the induced homotopy-group map of the
reduced sphere-map suspension to its fixed source-coordinate class. -/
theorem sphereReducedSuspensionPiHom_sphereTargetMapClass_eq_map (m q : ℕ)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    sphereReducedSuspensionPiHom m q
        (sphereTargetMapClass (q + 1) f hf) =
      HomotopyGroup.map (sphereReducedSuspensionMap (q + 1) m f hf)
        (sphereReducedSuspensionMap_basepoint (q + 1) m f hf)
        (sphereReducedSuspensionSourceClass q) := by
  rw [sphereReducedSuspensionPiHom_sphereTargetMapClass]
  exact sphereTargetMapClass_comp (q + 2)
    (sphereDiagonalReducedSuspensionGeneratorMap q)
    (sphereDiagonalReducedSuspensionGeneratorMap_basepoint q)
    (sphereReducedSuspensionMap (q + 1) m f hf)
    (sphereReducedSuspensionMap_basepoint (q + 1) m f hf)

/-- On represented classes, the unreduced and reduced geometric suspensions are intertwined by
the diagonal meridian-collapse classes in source and target coordinates. -/
theorem sphereSuspensionReductionClass_naturality (m q : ℕ)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    HomotopyGroup.map (sphereSuspensionReductionMap m)
        (sphereSuspensionReductionMap_basepoint m)
        (sphereSuspensionTargetMapClass q m f hf) =
      HomotopyGroup.map (sphereReducedSuspensionMap (q + 1) m f hf)
        (sphereReducedSuspensionMap_basepoint (q + 1) m f hf)
        (sphereSuspensionReductionClass (q + 1)) := by
  unfold sphereSuspensionTargetMapClass sphereSuspensionReductionClass
  rw [← sphereTargetMapClass_comp (q + 2)
      (sphereSuspensionMap (q + 1) m f)
      (sphereSuspensionMap_basepoint (q + 1) m f hf)
      (sphereSuspensionReductionMap m)
      (sphereSuspensionReductionMap_basepoint m)]
  rw [← sphereTargetMapClass_comp (q + 2)
      (sphereSuspensionReductionMap (q + 1))
      (sphereSuspensionReductionMap_basepoint (q + 1))
      (sphereReducedSuspensionMap (q + 1) m f hf)
      (sphereReducedSuspensionMap_basepoint (q + 1) m f hf)]
  let A := (sphereSuspensionReductionMap m).comp
    (sphereSuspensionMap (q + 1) m f)
  let B := (sphereReducedSuspensionMap (q + 1) m f hf).comp
    (sphereSuspensionReductionMap (q + 1))
  have hA : A (sphereBasepoint (q + 2)) = sphereBasepoint (m + 1) := by
    change sphereSuspensionReductionMap m
      (sphereSuspensionMap (q + 1) m f (sphereBasepoint ((q + 1) + 1))) = _
    rw [sphereSuspensionMap_basepoint (q + 1) m f hf,
      sphereSuspensionReductionMap_basepoint]
  have hB : B (sphereBasepoint (q + 2)) = sphereBasepoint (m + 1) := by
    change sphereReducedSuspensionMap (q + 1) m f hf
      (sphereSuspensionReductionMap (q + 1)
        (sphereBasepoint ((q + 1) + 1))) = _
    rw [sphereSuspensionReductionMap_basepoint,
      sphereReducedSuspensionMap_basepoint]
  have hmap : A = B :=
    sphereSuspensionReductionMap_naturality (q + 1) m f hf
  let H : ContinuousMap.Homotopy A B :=
    (ContinuousMap.Homotopy.refl A).cast rfl hmap
  have hbase : ∀ t : I, H (t, sphereBasepoint (q + 2)) = sphereBasepoint (m + 1) := by
    intro t
    change A (sphereBasepoint (q + 2)) = sphereBasepoint (m + 1)
    exact hA
  exact sphereTargetMapClass_eq_of_homotopy (q + 2) hA hB H hbase

/-- Once the two explicit diagonal source-coordinate classes are identified, applying the
meridian-collapse comparison to geometric suspension is exactly numerical reduced suspension. -/
theorem map_sphereGeometricSuspension_eq_sphereReducedSuspensionPiHom_of_sourceClass_eq
    (m q : ℕ)
    (hsource : sphereSuspensionReductionClass (q + 1) =
      sphereReducedSuspensionSourceClass q)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    HomotopyGroup.map (sphereSuspensionReductionMap m)
        (sphereSuspensionReductionMap_basepoint m)
        (sphereGeometricSuspension m q
          (sphereTargetMapClass (q + 1) f hf)) =
      sphereReducedSuspensionPiHom m q
        (sphereTargetMapClass (q + 1) f hf) := by
  rw [sphereGeometricSuspension_sphereTargetMapClass]
  rw [sphereSuspensionReductionClass_naturality, hsource]
  exact (sphereReducedSuspensionPiHom_sphereTargetMapClass_eq_map m q f hf).symm

end Submission
