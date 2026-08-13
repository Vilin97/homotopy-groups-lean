/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereSuspension

/-!
# Nullhomotopy of a suspended constant sphere map

Unreduced suspension does not carry a constant map to a literally constant map: its image is a
meridian.  This file contracts that meridian to its equatorial value and transports the
contraction through the chosen sphere-suspension homeomorphisms.  The construction works for a
map `Sᵐ ⟶ Sⁿ` with unrelated source and target dimensions and fixes the preferred basepoint
throughout.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

namespace Susp

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- Contract the meridian obtained by suspending a constant map to its equatorial value. -/
def meridianContractionToFun (y : Y) (p : I × Susp X) : Susp Y :=
  Quotient.lift
    (fun q : I × X => Susp.mk (Set.Icc.convexComb q.1 midpoint p.1, y))
    (by
      intro a b hab
      rcases hab with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact congrArg
          (fun q : I × X => Susp.mk (Set.Icc.convexComb q.1 midpoint p.1, y)) h
      · exact congrArg (fun t : I => Susp.mk (t, y)) (by simp [ha, hb])
      · exact congrArg (fun t : I => Susp.mk (t, y)) (by simp [ha, hb]))
    p.2

@[simp]
theorem meridianContractionToFun_mk (y : Y) (s : I) (p : I × X) :
    meridianContractionToFun y (s, Susp.mk p) =
      Susp.mk (Set.Icc.convexComb p.1 midpoint s, y) :=
  rfl

/-- The meridian contraction is jointly continuous in time and in the suspension variable. -/
theorem continuous_meridianContractionToFun (y : Y) :
    Continuous (meridianContractionToFun (X := X) y) := by
  refine Susp.isQuotientMap_mk.continuous_lift_prod_right ?_
  change Continuous fun p : I × (I × X) =>
    Susp.mk (Set.Icc.convexComb p.2.1 midpoint p.1, y)
  fun_prop

/-- Suspending a constant map is homotopic to the constant map at the equator. -/
def meridianContraction (y : Y) :
    ContinuousMap.Homotopy
      (Susp.map (ContinuousMap.const X y))
      (ContinuousMap.const (Susp X) (Susp.mk (midpoint, y))) where
  toFun := meridianContractionToFun y
  continuous_toFun := continuous_meridianContractionToFun y
  map_zero_left q := by
    induction q using Susp.ind with
    | h p => simp
  map_one_left q := by
    induction q using Susp.ind with
    | h p => simp

/-- The contraction fixes the preferred equatorial point. -/
@[simp]
theorem meridianContraction_equator (y : Y) (x : X) (s : I) :
    meridianContraction y (s, Susp.mk (midpoint, x)) = Susp.mk (midpoint, y) := by
  change Susp.mk (Set.Icc.convexComb midpoint midpoint s, y) = Susp.mk (midpoint, y)
  rw [Set.Icc.convexComb_eq]

end Susp

/-- The suspension of a constant sphere map is based-nullhomotopic, with source and target
dimensions allowed to differ. -/
noncomputable def sphereSuspensionMapConstHomotopy (m n : ℕ) :
    ContinuousMap.Homotopy
      (sphereSuspensionMap m n
        (ContinuousMap.const (Sph m) (sphereBasepoint n)))
      (ContinuousMap.const (Sph (m + 1)) (sphereBasepoint (n + 1))) where
  toFun p := suspSphHomeo n
    (Susp.meridianContraction (X := Sph m) (sphereBasepoint n)
      (p.1, (suspSphHomeo m).symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    calc
      suspSphHomeo n
          (Susp.meridianContraction (X := Sph m) (sphereBasepoint n)
            (0, (suspSphHomeo m).symm z)) =
          suspSphHomeo n
            (Susp.map (ContinuousMap.const (Sph m) (sphereBasepoint n))
              ((suspSphHomeo m).symm z)) :=
        congrArg (suspSphHomeo n)
          ((Susp.meridianContraction (X := Sph m) (sphereBasepoint n)).map_zero_left _)
      _ = sphereSuspensionMap m n
          (ContinuousMap.const (Sph m) (sphereBasepoint n)) z := rfl
  map_one_left z := by
    calc
      suspSphHomeo n
          (Susp.meridianContraction (X := Sph m) (sphereBasepoint n)
            (1, (suspSphHomeo m).symm z)) =
          suspSphHomeo n (Susp.mk (Susp.midpoint, sphereBasepoint n)) :=
        congrArg (suspSphHomeo n)
          ((Susp.meridianContraction (X := Sph m) (sphereBasepoint n)).map_one_left _)
      _ = sphereBasepoint (n + 1) := suspSphHomeo_equator_sphereBasepoint n

/-- The nullhomotopy of a suspended constant sphere map fixes the sphere basepoint. -/
theorem sphereSuspensionMapConstHomotopy_basepoint (m n : ℕ) (t : I) :
    sphereSuspensionMapConstHomotopy m n (t, sphereBasepoint (m + 1)) =
      sphereBasepoint (n + 1) := by
  change suspSphHomeo n
    (Susp.meridianContraction (X := Sph m) (sphereBasepoint n)
      (t, (suspSphHomeo m).symm (sphereBasepoint (m + 1)))) = sphereBasepoint (n + 1)
  rw [suspSphHomeo_symm_sphereBasepoint m]
  rw [Susp.meridianContraction_equator]
  exact suspSphHomeo_equator_sphereBasepoint n

end Submission
