import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_075 :
    Nonempty
      (π_ 152 (StableSphere 77) (stableSphereBasepoint 77) ≃*
        Multiplicative (ZMod 6 × (ZMod 72))) := by
  exact Submission.stable_stem_075
