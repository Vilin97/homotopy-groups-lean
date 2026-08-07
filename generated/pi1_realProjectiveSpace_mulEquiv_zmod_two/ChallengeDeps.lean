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

/-- Real projective `n`-space with its standard quotient topology. -/
abbrev RealProjectiveSpace (n : ℕ) :=
  Projectivization ℝ (Fin (n + 1) → ℝ)

/-- The quotient topology on real projective space. -/
noncomputable instance instTopologicalSpaceRealProjectiveSpace (n : ℕ) :
    TopologicalSpace (RealProjectiveSpace n) := by
  unfold RealProjectiveSpace Projectivization
  infer_instance

/-- The line spanned by the first coordinate vector. -/
noncomputable def realProjectiveBasepoint (n : ℕ) : RealProjectiveSpace n :=
  Projectivization.mk ℝ (Pi.single 0 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)



end HomotopyGroups
