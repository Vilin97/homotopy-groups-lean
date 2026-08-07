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

/-- Complex projective `n`-space with its standard quotient topology. -/
abbrev ComplexProjectiveSpace (n : ℕ) :=
  Projectivization ℂ (Fin (n + 1) → ℂ)

/-- The quotient topology on complex projective space. -/
noncomputable instance instTopologicalSpaceComplexProjectiveSpace (n : ℕ) :
    TopologicalSpace (ComplexProjectiveSpace n) := by
  unfold ComplexProjectiveSpace Projectivization
  infer_instance

/-- The complex line spanned by the first coordinate vector. -/
noncomputable def complexProjectiveBasepoint (n : ℕ) : ComplexProjectiveSpace n :=
  Projectivization.mk ℂ (Pi.single 0 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)



end HomotopyGroups
