import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_two_all_higher_homotopy_nontrivial (k : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (k + 2) (SphereSpace 2) (sphereBasepoint 2)) := by
  sorry

end Submission
