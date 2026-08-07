import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_036 :
    Nonempty
      (π_ 74 (StableSphere 38) (stableSphereBasepoint 38) ≃*
        Multiplicative (ZMod 6)) := by
  exact Submission.stable_stem_036
