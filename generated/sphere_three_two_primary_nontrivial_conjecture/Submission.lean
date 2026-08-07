import ChallengeDeps
import Submission.Helpers

open HomotopyGroups
open scoped BigOperators Topology

namespace Submission

theorem sphere_three_two_primary_nontrivial_conjecture (k : ℕ) :
    ∃ α : HomotopyGroup.Pi (k + 10 + 1) (SphereSpace 3) (sphereBasepoint 3),
      α ≠ 1 ∧ ∃ r : ℕ, α ^ (2 ^ (r + 1)) = 1 := by
  sorry

end Submission
