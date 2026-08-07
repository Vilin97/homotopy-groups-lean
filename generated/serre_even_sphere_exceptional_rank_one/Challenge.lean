import ChallengeDeps

open HomotopyGroups
open scoped Topology

theorem serre_even_sphere_exceptional_rank_one (n : ℕ) :
    ∃ T : CommGrpCat, Finite T ∧
      Nonempty
        (HomotopyGroup.Pi (4 * n + 3) (SphereSpace (2 * (n + 1)))
            (sphereBasepoint (2 * (n + 1))) ≃*
          Multiplicative ℤ × T) := by
  sorry
