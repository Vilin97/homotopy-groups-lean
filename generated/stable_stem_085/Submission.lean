import ChallengeDeps
import Submission.Helpers

open HomotopyGroups.StableStems
open scoped Topology

namespace Submission

theorem stable_stem_085 :
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 12)))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 12 × (ZMod 12))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 12 × (ZMod 12))))))))) ∨
    (Nonempty
      (π_ 172 (StableSphere 87) (stableSphereBasepoint 87) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 6 × (ZMod 12)))))))))) := by
  sorry

end Submission
