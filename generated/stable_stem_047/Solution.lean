import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_047 :
    Nonempty
      (π_ 96 (StableSphere 49) (stableSphereBasepoint 49) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 131040)))))) := by
  exact Submission.stable_stem_047
