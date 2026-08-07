import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_011 :
    Nonempty
      (π_ 24 (StableSphere 13) (stableSphereBasepoint 13) ≃*
        Multiplicative (ZMod 504)) := by
  exact Submission.stable_stem_011
