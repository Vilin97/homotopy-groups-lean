import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_018 :
    Nonempty
      (π_ 38 (StableSphere 20) (stableSphereBasepoint 20) ≃*
        Multiplicative (ZMod 2 × (ZMod 8))) := by
  exact Submission.stable_stem_018
