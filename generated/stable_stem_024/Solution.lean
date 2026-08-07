import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_024 :
    Nonempty
      (π_ 50 (StableSphere 26) (stableSphereBasepoint 26) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  exact Submission.stable_stem_024
