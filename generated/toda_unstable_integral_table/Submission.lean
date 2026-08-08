import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem toda_unstable_integral_table (nIndex k : Fin 20) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 1 + k.val)
          (SphereSpace (nIndex.val + 1)) (sphereBasepoint (nIndex.val + 1)) ≃*
        todaIntegralGroup nIndex k) := by
  sorry

end Submission
