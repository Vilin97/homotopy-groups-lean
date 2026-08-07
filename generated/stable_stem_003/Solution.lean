import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_003 :
    Nonempty
      (π_ 8 (StableSphere 5) (stableSphereBasepoint 5) ≃*
        Multiplicative (ZMod 24)) := by
  exact Submission.stable_stem_003
