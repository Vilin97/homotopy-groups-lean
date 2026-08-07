import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi1_complexProjectiveSpace_subsingleton (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (HomotopyGroup.Pi 1 (ComplexProjectiveSpace n)
        (complexProjectiveBasepoint n)) := by
  sorry

end Submission
