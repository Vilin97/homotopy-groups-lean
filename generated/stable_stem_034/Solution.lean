import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_034 :
    Nonempty
      (π_ 70 (StableSphere 36) (stableSphereBasepoint 36) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))) := by
  exact Submission.stable_stem_034
