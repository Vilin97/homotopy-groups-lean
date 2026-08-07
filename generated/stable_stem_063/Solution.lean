import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_063 :
    Nonempty
      (π_ 128 (StableSphere 65) (stableSphereBasepoint 65) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 32640))))) := by
  exact Submission.stable_stem_063
