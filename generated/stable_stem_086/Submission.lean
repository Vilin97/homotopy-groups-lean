import ChallengeDeps
import Submission.Helpers

open HomotopyGroups.StableStems
open scoped Topology

namespace Submission

theorem stable_stem_086 :
    (Nonempty
      (π_ 174 (StableSphere 88) (stableSphereBasepoint 88) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 8 × (ZMod 120)))))))) ∨
    (Nonempty
      (π_ 174 (StableSphere 88) (stableSphereBasepoint 88) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 8 × (ZMod 120))))))) := by
  sorry

end Submission
