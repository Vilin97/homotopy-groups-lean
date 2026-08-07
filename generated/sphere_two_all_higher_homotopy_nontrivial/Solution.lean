import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_two_all_higher_homotopy_nontrivial (k : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (k + 2) (SphereSpace 2) (sphereBasepoint 2)) := by
  exact Submission.sphere_two_all_higher_homotopy_nontrivial k
