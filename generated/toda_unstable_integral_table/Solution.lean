import ChallengeDeps
import Submission

open HomotopyGroups
open scoped Topology

theorem toda_unstable_integral_table (nIndex k : Fin 20) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 1 + k.val)
          (SphereSpace (nIndex.val + 1)) (sphereBasepoint (nIndex.val + 1)) ≃*
        todaIntegralGroup nIndex k) := by
  exact Submission.toda_unstable_integral_table nIndex k
