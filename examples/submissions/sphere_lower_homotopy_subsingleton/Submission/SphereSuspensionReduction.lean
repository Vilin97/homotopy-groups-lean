/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.ReducedSuspensionSphere
import Submission.Model.SuspensionReduction
import Submission.SphereSuspension

/-!
# Comparing unreduced and reduced suspension in sphere coordinates

Both maintained suspension models turn the suspension of a metric sphere into the next metric
sphere.  The comparison between them is the quotient which collapses the basepoint meridian.
This file transports that quotient into sphere coordinates and proves the naturality square for
an arbitrary based sphere map.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- In metric-sphere coordinates, collapse the basepoint meridian of the unreduced suspension. -/
noncomputable def sphereSuspensionReductionMap (n : ℕ) :
    C(Sph (n + 1), Sph (n + 1)) :=
  (⟨ReducedSusp.sphereHomeomorph n (sphereBasepoint n),
      (ReducedSusp.sphereHomeomorph n (sphereBasepoint n)).continuous⟩ :
      C(ReducedSusp (Sph n) (sphereBasepoint n), Sph (n + 1))).comp
    ((Susp.toReduced (sphereBasepoint n)).comp
      (⟨(suspSphHomeo n).symm, (suspSphHomeo n).continuous_symm⟩ :
        C(Sph (n + 1), Susp (Sph n))))

/-- The sphere-coordinate reduction map preserves the preferred basepoint. -/
@[simp]
theorem sphereSuspensionReductionMap_basepoint (n : ℕ) :
    sphereSuspensionReductionMap n (sphereBasepoint (n + 1)) =
      sphereBasepoint (n + 1) := by
  change ReducedSusp.sphereHomeomorph n (sphereBasepoint n)
    (Susp.toReduced (sphereBasepoint n)
      ((suspSphHomeo n).symm (sphereBasepoint (n + 1)))) = sphereBasepoint (n + 1)
  rw [suspSphHomeo_symm_sphereBasepoint,
    Susp.toReduced_basepoint_meridian,
    ReducedSusp.sphereHomeomorph_base]

/-- The sphere-coordinate reduction map is onto. -/
theorem sphereSuspensionReductionMap_surjective (n : ℕ) :
    Function.Surjective (sphereSuspensionReductionMap n) :=
  (ReducedSusp.sphereHomeomorph n (sphereBasepoint n)).surjective.comp
    ((Susp.toReduced_surjective (sphereBasepoint n)).comp
      (suspSphHomeo n).symm.surjective)

/-- Suspend a based sphere map using reduced suspension and the maintained reduced-sphere
coordinates. -/
noncomputable def sphereReducedSuspensionMap (m n : ℕ)
    (f : C(Sph m, Sph n))
    (hf : f (sphereBasepoint m) = sphereBasepoint n) :
    C(Sph (m + 1), Sph (n + 1)) :=
  (⟨ReducedSusp.sphereHomeomorph n (sphereBasepoint n),
      (ReducedSusp.sphereHomeomorph n (sphereBasepoint n)).continuous⟩ :
      C(ReducedSusp (Sph n) (sphereBasepoint n), Sph (n + 1))).comp
    ((ReducedSusp.map (sphereBasepoint m) (sphereBasepoint n) f hf).comp
      (⟨(ReducedSusp.sphereHomeomorph m (sphereBasepoint m)).symm,
          (ReducedSusp.sphereHomeomorph m
            (sphereBasepoint m)).continuous_symm⟩ :
        C(Sph (m + 1), ReducedSusp (Sph m) (sphereBasepoint m))))

/-- Reduced suspension carries a based sphere map to a based sphere map. -/
@[simp]
theorem sphereReducedSuspensionMap_basepoint (m n : ℕ)
    (f : C(Sph m, Sph n))
    (hf : f (sphereBasepoint m) = sphereBasepoint n) :
    sphereReducedSuspensionMap m n f hf (sphereBasepoint (m + 1)) =
      sphereBasepoint (n + 1) := by
  change ReducedSusp.sphereHomeomorph n (sphereBasepoint n)
    (ReducedSusp.map (sphereBasepoint m) (sphereBasepoint n) f hf
      ((ReducedSusp.sphereHomeomorph m (sphereBasepoint m)).symm
        (sphereBasepoint (m + 1)))) = sphereBasepoint (n + 1)
  rw [← ReducedSusp.sphereHomeomorph_base m (sphereBasepoint m),
    Homeomorph.symm_apply_apply, ReducedSusp.map_base,
    ReducedSusp.sphereHomeomorph_base]

/-- The explicit unreduced suspension and the reduced suspension of a based sphere map commute
with the meridian-collapse comparison maps. -/
theorem sphereSuspensionReductionMap_naturality (m n : ℕ)
    (f : C(Sph m, Sph n))
    (hf : f (sphereBasepoint m) = sphereBasepoint n) :
    (sphereSuspensionReductionMap n).comp (sphereSuspensionMap m n f) =
      (sphereReducedSuspensionMap m n f hf).comp
        (sphereSuspensionReductionMap m) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨q, rfl⟩ := (suspSphHomeo m).surjective z
  induction q using Susp.ind with
  | h p =>
      simp only [ContinuousMap.comp_apply, sphereSuspensionReductionMap,
        sphereReducedSuspensionMap, sphereSuspensionMap_apply_susp]
      change ReducedSusp.sphereHomeomorph n (sphereBasepoint n)
          (Susp.toReduced (sphereBasepoint n)
            ((suspSphHomeo n).symm
              (suspSphHomeo n (Susp.mk (p.1, f p.2))))) =
        ReducedSusp.sphereHomeomorph n (sphereBasepoint n)
          (ReducedSusp.map (sphereBasepoint m) (sphereBasepoint n) f hf
            ((ReducedSusp.sphereHomeomorph m (sphereBasepoint m)).symm
              (ReducedSusp.sphereHomeomorph m (sphereBasepoint m)
                (Susp.toReduced (sphereBasepoint m)
                  ((suspSphHomeo m).symm (suspSphHomeo m (Susp.mk p)))))))
      rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
        Homeomorph.symm_apply_apply, Susp.toReduced_mk, Susp.toReduced_mk,
        ReducedSusp.map_mk]

end Submission
