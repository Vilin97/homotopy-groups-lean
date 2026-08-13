/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SphereLoopBridge
import Submission.SphereSuspensionConst

/-!
# Geometric suspension on arbitrary sphere homotopy classes

The explicit sphere-map suspension in `Submission.SphereSuspension` applies to maps
`Sᵐ ⟶ Sⁿ`, while `Submission.Hurewicz.SphereLoopBridge` identifies positive-dimensional
cubical homotopy classes with based sphere maps.  This file combines the two constructions to
give a well-defined geometric suspension

`π_{q+1}(Sᵐ) ⟶ π_{q+2}(Sᵐ⁺¹)`.

No comparison with the cap-excision suspension homomorphism is asserted here.  The main result
is instead the representative formula: a class represented by `f` suspends to the class
represented by the explicit map `sphereSuspensionMap _ _ f`.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The homotopy class represented by the explicit suspension of a based sphere map. -/
noncomputable def sphereSuspensionTargetMapClass (q m : ℕ)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1)) :=
  sphereTargetMapClass (q + 2) (sphereSuspensionMap (q + 1) m f)
    (sphereSuspensionMap_basepoint (q + 1) m f hf)

/-- Based-homotopic sphere maps have equal explicitly suspended homotopy classes. -/
theorem sphereSuspensionTargetMapClass_eq_of_homotopy (q m : ℕ)
    {f g : C(Sph (q + 1), Sph m)}
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m)
    (hg : g (sphereBasepoint (q + 1)) = sphereBasepoint m)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint (q + 1)) = sphereBasepoint m) :
    sphereSuspensionTargetMapClass q m f hf =
      sphereSuspensionTargetMapClass q m g hg := by
  exact sphereTargetMapClass_eq_of_homotopy (q + 2)
    (sphereSuspensionMap_basepoint (q + 1) m f hf)
    (sphereSuspensionMap_basepoint (q + 1) m g hg)
    (sphereSuspensionMapHomotopy (q + 1) m H)
    (sphereSuspensionMapHomotopy_basepoint (q + 1) m H hbase)

/-- Suspend a cubical representative of a positive-dimensional sphere homotopy class. -/
noncomputable def genLoopSphereSuspension (m q : ℕ)
    (α : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m)) :
    π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1)) :=
  sphereSuspensionTargetMapClass q m (targetGenLoopSphereMap q α)
    (targetGenLoopSphereMap_basepoint q α)

/-- Cubically homotopic representatives have equal geometric suspensions. -/
theorem genLoopSphereSuspension_homotopyInvariant (m q : ℕ)
    {α β : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m)}
    (H : GenLoop.Homotopic α β) :
    genLoopSphereSuspension m q α = genLoopSphereSuspension m q β := by
  obtain ⟨H⟩ := H
  exact sphereSuspensionTargetMapClass_eq_of_homotopy q m
    (targetGenLoopSphereMap_basepoint q α)
    (targetGenLoopSphereMap_basepoint q β)
    (targetGenLoopSphereMapHomotopy q H)
    (targetGenLoopSphereMapHomotopy_basepoint q H)

/-- Geometric suspension on arbitrary positive-dimensional sphere homotopy classes. -/
noncomputable def sphereGeometricSuspension (m q : ℕ) :
    π_ (q + 1) (Sph m) (sphereBasepoint m) →
      π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1)) :=
  Quotient.lift (genLoopSphereSuspension m q)
    (fun _ _ H ↦ genLoopSphereSuspension_homotopyInvariant m q H)

/-- Evaluation of geometric suspension on a represented cubical class. -/
@[simp]
theorem sphereGeometricSuspension_mk (m q : ℕ)
    (α : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m)) :
    sphereGeometricSuspension m q ⟦α⟧ = genLoopSphereSuspension m q α :=
  rfl

/-- A class represented by a based sphere map suspends to the class represented by that map's
explicit geometric suspension. -/
theorem sphereGeometricSuspension_sphereTargetMapClass (m q : ℕ)
    (f : C(Sph (q + 1), Sph m))
    (hf : f (sphereBasepoint (q + 1)) = sphereBasepoint m) :
    sphereGeometricSuspension m q (sphereTargetMapClass (q + 1) f hf) =
      sphereSuspensionTargetMapClass q m f hf := by
  let A := targetGenLoopSphereMap q (sphereTargetMapGenLoop (q + 1) f hf)
  have hA : A (sphereBasepoint (q + 1)) = sphereBasepoint m :=
    targetGenLoopSphereMap_basepoint q _
  have hmap : A = f := targetGenLoopSphereMap_sphereTargetMapGenLoop q f hf
  let H : ContinuousMap.Homotopy A f :=
    (ContinuousMap.Homotopy.refl A).cast rfl hmap
  have hbase : ∀ t : I, H (t, sphereBasepoint (q + 1)) = sphereBasepoint m := by
    intro t
    change A (sphereBasepoint (q + 1)) = sphereBasepoint m
    exact hA
  exact sphereSuspensionTargetMapClass_eq_of_homotopy q m hA hf H hbase

/-- Geometric suspension preserves the identity element in every positive source dimension. -/
@[simp]
theorem sphereGeometricSuspension_one (m q : ℕ) :
    sphereGeometricSuspension m q
        (1 : π_ (q + 1) (Sph m) (sphereBasepoint m)) =
      (1 : π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1))) := by
  rw [HomotopyGroup.one_def, sphereGeometricSuspension_mk]
  change sphereSuspensionTargetMapClass q m
      (targetGenLoopSphereMap q
        (GenLoop.const : Ω^ (Fin (q + 1)) (Sph m) (sphereBasepoint m))) _ = 1
  simp only [targetGenLoopSphereMap_const]
  exact sphereTargetMapClass_eq_one_of_nullhomotopic (q + 2)
    (sphereSuspensionMap (q + 1) m
      (ContinuousMap.const (Sph (q + 1)) (sphereBasepoint m)))
    (sphereSuspensionMap_basepoint (q + 1) m _ rfl)
    (sphereSuspensionMapConstHomotopy (q + 1) m)
    (sphereSuspensionMapConstHomotopy_basepoint (q + 1) m)

/-- Geometric suspension bundled as an identity-preserving map. -/
noncomputable def sphereGeometricSuspensionOneHom (m q : ℕ) :
    OneHom
      (π_ (q + 1) (Sph m) (sphereBasepoint m))
      (π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1))) where
  toFun := sphereGeometricSuspension m q
  map_one' := sphereGeometricSuspension_one m q

@[simp]
theorem sphereGeometricSuspensionOneHom_apply (m q : ℕ)
    (a : π_ (q + 1) (Sph m) (sphereBasepoint m)) :
    sphereGeometricSuspensionOneHom m q a = sphereGeometricSuspension m q a :=
  rfl

end Submission
