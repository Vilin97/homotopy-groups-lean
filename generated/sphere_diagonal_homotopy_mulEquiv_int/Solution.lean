import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_diagonal_homotopy_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1))
          (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  exact Submission.sphere_diagonal_homotopy_mulEquiv_int n
