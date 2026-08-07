import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem pi1_complexProjectiveSpace_subsingleton (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (HomotopyGroup.Pi 1 (ComplexProjectiveSpace n)
        (complexProjectiveBasepoint n)) := by
  exact Submission.pi1_complexProjectiveSpace_subsingleton n hn
