import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_021 :
    Nonempty
      (π_ 44 (StableSphere 23) (stableSphereBasepoint 23) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  exact Submission.stable_stem_021
