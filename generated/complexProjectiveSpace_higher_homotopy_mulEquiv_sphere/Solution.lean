import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem complexProjectiveSpace_higher_homotopy_mulEquiv_sphere (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 3) (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 3) (SphereSpace (2 * n + 1))
          (sphereBasepoint (2 * n + 1))) := by
  exact Submission.complexProjectiveSpace_higher_homotopy_mulEquiv_sphere n k hn
