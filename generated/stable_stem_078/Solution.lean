import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_078 :
    Nonempty
      (π_ 158 (StableSphere 80) (stableSphereBasepoint 80) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 12)))))) := by
  exact Submission.stable_stem_078
