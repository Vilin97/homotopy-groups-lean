import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped Topology

namespace Submission

theorem stable_three_primary_groups_001_108 (stemIndex : Fin 108) :
    Nonempty
      (CommGroup.primaryComponent
          (π_ (2 * (stemIndex.val + 1) + 2)
            (StableStems.StableSphere (stemIndex.val + 3))
            (StableStems.stableSphereBasepoint (stemIndex.val + 3))) 3 ≃*
        stableThreePrimaryGroup stemIndex) := by
  sorry

end Submission
