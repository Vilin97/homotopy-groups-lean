import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem pi1_realProjectiveSpace_mulEquiv_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  exact Submission.pi1_realProjectiveSpace_mulEquiv_zmod_two n hn
