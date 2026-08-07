import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_022 :
    Nonempty
      (π_ 46 (StableSphere 24) (stableSphereBasepoint 24) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  exact Submission.stable_stem_022
