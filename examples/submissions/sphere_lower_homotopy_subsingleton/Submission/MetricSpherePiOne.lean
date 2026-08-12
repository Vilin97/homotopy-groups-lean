/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ChallengeDeps
import Submission.MetricSpherePiOneGeneric

/-!
# The fundamental group of the metric circle

This file closes the model gap between Mathlib's complex unit circle and the exact metric
`SphereSpace 1` used by the benchmark.  The source circle computation uses the exponential
covering.  Homotopy invariance then transports it across an explicit homeomorphism which sends
the standard point `1 : Circle` to `sphereBasepoint 1`.
-/

open HomotopyGroups
open scoped Topology

noncomputable section

namespace Submission

/-- The standard complex unit circle as the benchmark's metric `SphereSpace 1`. -/
def circleHomeomorphMetricSphereOne : Circle ≃ₜ SphereSpace 1 :=
  circleHomeomorphSphOne

@[simp]
theorem circleHomeomorphMetricSphereOne_one :
    circleHomeomorphMetricSphereOne (1 : Circle) = sphereBasepoint 1 := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [circleHomeomorphMetricSphereOne, circleHomeomorphSphOne, sphereBasepoint]

/-- The fundamental group of the benchmark's exact metric circle is infinite cyclic. -/
theorem pi1_sphere_one_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 1 (SphereSpace 1) (sphereBasepoint 1) ≃*
        Multiplicative ℤ) :=
  pi1_sph_one_at_mulEquiv_int (sphereBasepoint 1)

end Submission
