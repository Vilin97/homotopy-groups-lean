import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_081 :
    Nonempty
      (π_ 164 (StableSphere 83) (stableSphereBasepoint 83) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 24)))))))) := by
  exact Submission.stable_stem_081
