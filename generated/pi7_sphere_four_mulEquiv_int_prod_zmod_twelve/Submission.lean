import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem pi7_sphere_four_mulEquiv_int_prod_zmod_twelve :
    Nonempty
      (HomotopyGroup.Pi 7 (SphereSpace 4) (sphereBasepoint 4) ≃*
        Multiplicative ℤ × Multiplicative (ZMod 12)) := by
  sorry

end Submission
