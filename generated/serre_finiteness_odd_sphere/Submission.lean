import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem serre_finiteness_odd_sphere (n k : ℕ) (hk : 2 * n + 3 < k) :
    Finite
      (HomotopyGroup.Pi k (SphereSpace (2 * n + 3))
        (sphereBasepoint (2 * n + 3))) := by
  sorry

end Submission
