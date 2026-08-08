import Mathlib
import Submission.Helpers

open scoped ContinuousMap Topology Topology.Homotopy

universe u

namespace Submission

/-- Higher homotopy groups are abelian.  In the cubical model used by Mathlib,
the commutative group structure is constructed by the Eckmann--Hilton argument. -/
theorem higher_homotopy_mul_comm
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X)
    (a b : HomotopyGroup.Pi (n + 2) X x) :
    a * b = b * a := by
  exact mul_comm a b

end Submission
