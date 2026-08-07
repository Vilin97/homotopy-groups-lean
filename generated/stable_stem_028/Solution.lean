import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_028 :
    Nonempty
      (π_ 58 (StableSphere 30) (stableSphereBasepoint 30) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.stable_stem_028
