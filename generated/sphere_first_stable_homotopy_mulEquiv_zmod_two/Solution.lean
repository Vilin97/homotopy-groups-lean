import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_first_stable_homotopy_mulEquiv_zmod_two (n : ℕ) (hn : 3 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.sphere_first_stable_homotopy_mulEquiv_zmod_two n hn
