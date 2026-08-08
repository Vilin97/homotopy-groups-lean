import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem positive_stable_stem_finite (k : ℕ) (hk : 0 < k) :
    Finite
      (HomotopyGroup.Pi (2 * k + 2) (SphereSpace (k + 2))
        (sphereBasepoint (k + 2))) := by
  sorry

end Submission
