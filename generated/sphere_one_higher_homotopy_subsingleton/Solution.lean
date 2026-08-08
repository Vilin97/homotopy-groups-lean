import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_one_higher_homotopy_subsingleton (k : ℕ) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (sphereBasepoint 1)) := by
  exact Submission.sphere_one_higher_homotopy_subsingleton k
