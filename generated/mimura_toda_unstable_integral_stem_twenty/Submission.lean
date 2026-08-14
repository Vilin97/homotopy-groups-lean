import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem mimura_toda_unstable_integral_stem_twenty (nIndex : Fin 21) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 22)
          (SphereSpace (nIndex.val + 2)) (sphereBasepoint (nIndex.val + 2)) ≃*
        mimuraTodaStemTwentyGroup nIndex) := by
  sorry

end Submission
