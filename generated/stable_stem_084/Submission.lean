import ChallengeDeps
import Submission.Helpers

open HomotopyGroups.StableStems
open scoped Topology

namespace Submission

theorem stable_stem_084 :
    (Nonempty
      (π_ 170 (StableSphere 86) (stableSphereBasepoint 86) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 6)))))))) ∨
    (Nonempty
      (π_ 170 (StableSphere 86) (stableSphereBasepoint 86) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 6))))))) := by
  sorry

end Submission
