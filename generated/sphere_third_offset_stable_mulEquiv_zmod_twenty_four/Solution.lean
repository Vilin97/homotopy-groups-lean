import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_third_offset_stable_mulEquiv_zmod_twenty_four (n : ℕ) (hn : 5 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 3) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 24)) := by
  exact Submission.sphere_third_offset_stable_mulEquiv_zmod_twenty_four n hn
