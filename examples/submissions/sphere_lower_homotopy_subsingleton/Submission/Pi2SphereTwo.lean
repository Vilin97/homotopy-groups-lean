/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import ChallengeDeps
import Submission.Pi2SphereTwoGeneric

/-!
# The second homotopy group of the two-sphere

This file specializes the challenge-independent calculation to the exact sphere and basepoint
used by the generated benchmark.
-/

open HomotopyGroups
open scoped Topology

noncomputable section

namespace Submission

/-- The exact lattice cell `π₂(S²) ≃ ℤ`, for the metric sphere and distinguished basepoint used
by the benchmark. -/
theorem pi2_sphere_two_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 2 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative ℤ) :=
  pi2_sphere_two_at_mulEquiv_int (sphereBasepoint 2)

end Submission
