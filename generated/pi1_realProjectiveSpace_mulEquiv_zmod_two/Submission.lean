import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi1_realProjectiveSpace_mulEquiv_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

end Submission
