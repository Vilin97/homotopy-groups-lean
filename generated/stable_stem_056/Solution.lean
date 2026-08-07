import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_056 :
    Nonempty
      (π_ 114 (StableSphere 58) (stableSphereBasepoint 58) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.stable_stem_056
