import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_039 :
    Nonempty
      (π_ 80 (StableSphere 41) (stableSphereBasepoint 41) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 13200))))))) := by
  exact Submission.stable_stem_039
