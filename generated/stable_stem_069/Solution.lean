import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_069 :
    Nonempty
      (π_ 140 (StableSphere 71) (stableSphereBasepoint 71) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2))))) := by
  exact Submission.stable_stem_069
