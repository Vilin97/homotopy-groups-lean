import ChallengeDeps

open HomotopyGroups
open scoped Topology

theorem realProjectiveSpace_higher_homotopy_mulEquiv_sphere (n k : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 2) (SphereSpace n)
          (sphereBasepoint n)) := by
  sorry
