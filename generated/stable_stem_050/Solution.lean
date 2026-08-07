import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_050 :
    Nonempty
      (π_ 102 (StableSphere 52) (stableSphereBasepoint 52) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 6)))) := by
  exact Submission.stable_stem_050
