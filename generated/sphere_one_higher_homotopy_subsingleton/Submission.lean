import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_one_higher_homotopy_subsingleton (k : ℕ) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (sphereBasepoint 1)) := by
  sorry

end Submission
