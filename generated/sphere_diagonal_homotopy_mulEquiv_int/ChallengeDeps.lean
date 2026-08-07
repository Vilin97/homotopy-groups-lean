import Mathlib

/-!
# Homotopy groups of standard spaces

`SphereSpace` is the unit metric sphere in `ℝ^(n+1)`.  The projective-space models
use mathlib's algebraic `Projectivization`, equipped with the quotient topology supplied
by `Mathlib.Topology.Constructions`.  These are concrete topological types, rather than
uninterpreted placeholders.
-/

open scoped Topology

namespace HomotopyGroups

/-- The standard unit `n`-sphere in Euclidean `(n+1)`-space. -/
abbrev SphereSpace (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first coordinate vector, used as the basepoint of `SphereSpace n`. -/
noncomputable def sphereBasepoint (n : ℕ) : SphereSpace n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩



end HomotopyGroups
