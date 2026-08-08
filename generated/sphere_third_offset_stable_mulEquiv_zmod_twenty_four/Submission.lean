import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_third_offset_stable_mulEquiv_zmod_twenty_four (n : ℕ) (hn : 5 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 3) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 24)) := by
  sorry

end Submission
