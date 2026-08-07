import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_first_stable_homotopy_mulEquiv_zmod_two (n : ℕ) (hn : 3 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

end Submission
