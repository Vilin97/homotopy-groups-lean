import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_049 :
    Nonempty
      (π_ 100 (StableSphere 51) (stableSphereBasepoint 51) ≃*
        Multiplicative (ZMod 2 × (ZMod 6))) := by
  exact Submission.stable_stem_049
