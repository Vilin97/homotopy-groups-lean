import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_076 :
    Nonempty
      (π_ 154 (StableSphere 78) (stableSphereBasepoint 78) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 20)))) := by
  exact Submission.stable_stem_076
