import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi2_complexProjectiveSpace_mulEquiv_int (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 2 (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        Multiplicative ℤ) := by
  sorry

end Submission
