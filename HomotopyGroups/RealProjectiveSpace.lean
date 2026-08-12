import HomotopyGroups.Spaces
import Submission.RealProjectiveSpace

open HomotopyGroups
open scoped Topology

namespace Submission

private theorem realProjective_basepoint_eq (n : ℕ) :
    realProjectiveModelBasepoint n = realProjectiveBasepoint n := by
  rfl

private theorem sphere_basepoint_eq (n : ℕ) :
    sphereModelBasepoint n = sphereBasepoint n := by
  rfl

/-- Higher homotopy groups of real projective space agree with those of its sphere cover. -/
theorem realProjectiveSpace_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (_hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 2) (SphereSpace n)
          (sphereBasepoint n)) := by
  rw [← realProjective_basepoint_eq n, ← sphere_basepoint_eq n]
  exact realProjectiveModel_higher_homotopy_mulEquiv_sphere n k

/-- The fundamental group of real projective `n`-space is cyclic of order two for `n ≥ 2`. -/
theorem pi1_realProjectiveSpace_mulEquiv_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  rw [← realProjective_basepoint_eq n]
  exact piOne_realProjectiveModel_mulEquiv_zmod_two n hn

end Submission
