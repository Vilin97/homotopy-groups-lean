import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_083 :
    Nonempty
      (π_ 168 (StableSphere 85) (stableSphereBasepoint 85) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 8 × (ZMod 758520)))))) := by
  exact Submission.stable_stem_083
