import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem sphere_lower_homotopy_subsingleton (n k : ℕ) (hk : k < n) :
    Subsingleton
      (HomotopyGroup.Pi k (SphereSpace n) (sphereBasepoint n)) := by
  exact Submission.sphere_lower_homotopy_subsingleton n k hk
