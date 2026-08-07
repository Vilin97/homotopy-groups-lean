import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_001 :
    Nonempty
      (π_ 4 (StableSphere 3) (stableSphereBasepoint 3) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.stable_stem_001
