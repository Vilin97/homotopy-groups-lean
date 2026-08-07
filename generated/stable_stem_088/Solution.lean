import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_088 :
    Nonempty
      (π_ 178 (StableSphere 90) (stableSphereBasepoint 90) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))))) := by
  exact Submission.stable_stem_088
