import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_087 :
    Nonempty
      (π_ 176 (StableSphere 89) (stableSphereBasepoint 89) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4 × (ZMod 5520)))))))) := by
  exact Submission.stable_stem_087
