import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_038 :
    Nonempty
      (π_ 78 (StableSphere 40) (stableSphereBasepoint 40) ≃*
        Multiplicative (ZMod 2 × (ZMod 60))) := by
  exact Submission.stable_stem_038
