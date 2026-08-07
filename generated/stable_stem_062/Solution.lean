import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_062 :
    Nonempty
      (π_ 126 (StableSphere 64) (stableSphereBasepoint 64) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6))))) := by
  exact Submission.stable_stem_062
