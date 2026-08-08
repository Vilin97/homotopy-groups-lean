import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi6_sphere_three_mulEquiv_zmod_twelve :
    Nonempty
      (HomotopyGroup.Pi 6 (SphereSpace 3) (sphereBasepoint 3) ≃*
        Multiplicative (ZMod 12)) := by
  sorry

end Submission
