/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SphereLoopBridge
import Submission.Topology.MappingCone

/-!
# Sphere homotopy classes and mapping-cone retractions

For a based positive-dimensional sphere map into a simply connected target, this file combines
the free-homotopy classification of its cubical homotopy-group class with the mapping-cone
retraction criterion.  The bottom inclusion in the mapping cone retracts exactly when the
attaching map represents the identity homotopy class.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- A based positive-dimensional sphere map into a simply connected target represents the
identity exactly when the inclusion of the target into its mapping cone has a retraction. -/
theorem exists_sphereTargetMappingConeIncl_retraction_iff_class_eq_one
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (n : ℕ) (x : X) (f : C(SphereSpace (n + 1), X))
    (hf : f (sphereBasepoint (n + 1)) = x) :
    (∃ r : topologicalMappingCone (TopCat.ofHom f) ⟶ TopCat.of X,
        topologicalMappingConeIncl (TopCat.ofHom f) ≫ r = 𝟙 (TopCat.of X)) ↔
      sphereTargetMapClass (n + 1) f hf = 1 := by
  rw [exists_topologicalMappingConeIncl_retraction_iff_homotopy_const]
  exact (sphereTargetMapClass_eq_one_iff_freelyNullhomotopic n f hf).symm

/-- The homotopy-invariant version: the mapping-cone inclusion admits a homotopy retraction
exactly when the represented sphere class is the identity. -/
theorem exists_sphereTargetMappingConeIncl_homotopy_retraction_iff_class_eq_one
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (n : ℕ) (x : X) (f : C(SphereSpace (n + 1), X))
    (hf : f (sphereBasepoint (n + 1)) = x) :
    (∃ r : topologicalMappingCone (TopCat.ofHom f) ⟶ TopCat.of X,
        Nonempty
          (TopCat.Homotopy
            (topologicalMappingConeIncl (TopCat.ofHom f) ≫ r)
            (𝟙 (TopCat.of X)))) ↔
      sphereTargetMapClass (n + 1) f hf = 1 := by
  rw [exists_topologicalMappingConeIncl_homotopy_retraction_iff_nullhomotopic,
    ← exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic]
  exact exists_sphereTargetMappingConeIncl_retraction_iff_class_eq_one n x f hf

end Submission
