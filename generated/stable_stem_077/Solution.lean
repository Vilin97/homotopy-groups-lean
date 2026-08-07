import ChallengeDeps
import Submission

open HomotopyGroups.StableStems
open scoped Topology

theorem stable_stem_077 :
    Nonempty
      (π_ 156 (StableSphere 79) (stableSphereBasepoint 79) ≃*
        Multiplicative (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 4))))))) := by
  exact Submission.stable_stem_077
