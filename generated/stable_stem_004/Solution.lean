import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_004 :
    Nonempty
      (π_ 10 (StableSphere 6) (stableSphereBasepoint 6) ≃*
        Multiplicative (ZMod 1)) := by
  exact Submission.stable_stem_004
