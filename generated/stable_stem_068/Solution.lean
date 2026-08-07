import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_068 :
    Nonempty
      (π_ 138 (StableSphere 70) (stableSphereBasepoint 70) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 6)))) := by
  exact Submission.stable_stem_068
