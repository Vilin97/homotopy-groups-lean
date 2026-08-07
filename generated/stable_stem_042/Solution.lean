import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_042 :
    Nonempty
      (π_ 86 (StableSphere 44) (stableSphereBasepoint 44) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 24)))) := by
  exact Submission.stable_stem_042
