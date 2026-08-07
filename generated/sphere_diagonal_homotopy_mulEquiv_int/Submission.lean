import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_diagonal_homotopy_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1))
          (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  sorry

end Submission
