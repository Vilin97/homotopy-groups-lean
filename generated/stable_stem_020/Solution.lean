import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_020 :
    Nonempty
      (π_ 42 (StableSphere 22) (stableSphereBasepoint 22) ≃*
        Multiplicative (ZMod 24)) := by
  exact Submission.stable_stem_020
