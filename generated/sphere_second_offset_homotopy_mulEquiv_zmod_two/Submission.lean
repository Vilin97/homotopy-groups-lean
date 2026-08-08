import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_second_offset_homotopy_mulEquiv_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 2) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

end Submission
