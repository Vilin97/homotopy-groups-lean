import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_031 :
    Nonempty
      (π_ 64 (StableSphere 33) (stableSphereBasepoint 33) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 16320)))) := by
  exact Submission.stable_stem_031
