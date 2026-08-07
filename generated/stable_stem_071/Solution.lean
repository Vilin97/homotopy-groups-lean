import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_071 :
    Nonempty
      (π_ 144 (StableSphere 73) (stableSphereBasepoint 73) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 8 × (ZMod 138181680))))))))) := by
  exact Submission.stable_stem_071
