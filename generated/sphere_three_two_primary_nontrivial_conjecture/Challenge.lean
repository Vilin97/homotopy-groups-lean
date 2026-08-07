import ChallengeDeps

open HomotopyGroups
open scoped BigOperators Topology

theorem sphere_three_two_primary_nontrivial_conjecture (k : ℕ) :
    ∃ α : HomotopyGroup.Pi (k + 10 + 1) (SphereSpace 3) (sphereBasepoint 3),
      α ≠ 1 ∧ ∃ r : ℕ, α ^ (2 ^ (r + 1)) = 1 := by
  sorry
