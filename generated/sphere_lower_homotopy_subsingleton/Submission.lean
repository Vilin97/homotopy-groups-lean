import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_lower_homotopy_subsingleton (n k : ℕ) (hk : k < n) :
    Subsingleton
      (HomotopyGroup.Pi k (SphereSpace n) (sphereBasepoint n)) := by
  sorry

end Submission
