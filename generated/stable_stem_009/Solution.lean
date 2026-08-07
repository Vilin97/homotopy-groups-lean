import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_009 :
    Nonempty
      (π_ 20 (StableSphere 11) (stableSphereBasepoint 11) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2)))) := by
  exact Submission.stable_stem_009
