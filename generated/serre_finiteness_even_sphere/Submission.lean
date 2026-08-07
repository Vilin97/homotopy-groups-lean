import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem serre_finiteness_even_sphere (n k : ℕ)
    (hk : 2 * (n + 1) < k) (hExceptional : k ≠ 4 * n + 3) :
    Finite
      (HomotopyGroup.Pi k (SphereSpace (2 * (n + 1)))
        (sphereBasepoint (2 * (n + 1)))) := by
  sorry

end Submission
