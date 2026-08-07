import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_015 :
    Nonempty
      (π_ 32 (StableSphere 17) (stableSphereBasepoint 17) ≃*
        Multiplicative (ZMod 2 × (ZMod 480))) := by
  exact Submission.stable_stem_015
