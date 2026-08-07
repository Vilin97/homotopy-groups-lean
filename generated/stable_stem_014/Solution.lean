import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_014 :
    Nonempty
      (π_ 30 (StableSphere 16) (stableSphereBasepoint 16) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  exact Submission.stable_stem_014
