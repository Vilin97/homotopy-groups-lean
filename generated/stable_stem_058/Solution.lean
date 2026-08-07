import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_058 :
    Nonempty
      (π_ 118 (StableSphere 60) (stableSphereBasepoint 60) ≃*
        Multiplicative (ZMod 2 × (ZMod 2))) := by
  exact Submission.stable_stem_058
