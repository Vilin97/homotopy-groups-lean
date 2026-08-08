import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi5_sphere_two_mulEquiv_zmod_two :
    Nonempty
      (HomotopyGroup.Pi 5 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

end Submission
