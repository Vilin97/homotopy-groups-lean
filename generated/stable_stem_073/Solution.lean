import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_073 :
    Nonempty
      (π_ 148 (StableSphere 75) (stableSphereBasepoint 75) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2)))))))) := by
  exact Submission.stable_stem_073
