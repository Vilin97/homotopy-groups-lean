import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_044 :
    Nonempty
      (π_ 90 (StableSphere 46) (stableSphereBasepoint 46) ≃*
        Multiplicative (ZMod 8)) := by
  exact Submission.stable_stem_044
