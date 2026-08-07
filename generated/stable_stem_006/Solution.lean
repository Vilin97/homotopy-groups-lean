import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_006 :
    Nonempty
      (π_ 14 (StableSphere 8) (stableSphereBasepoint 8) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.stable_stem_006
