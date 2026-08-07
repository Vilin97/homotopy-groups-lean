import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_three_all_higher_homotopy_nontrivial (k : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (k + 3) (SphereSpace 3) (sphereBasepoint 3)) := by
  sorry

end Submission
