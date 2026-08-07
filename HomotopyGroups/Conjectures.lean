import EvalTools.Markers
import HomotopyGroups.Spaces
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Open conjectures expressible in the native homotopy-group language

The declaration below is the concrete torsion-element formulation of the
Ivanov–Mikhailov–Wu conjecture that the 2-primary component of `π_m(S³)` is
nonzero for every `m > 10`.  Writing the dimension as `k + 10 + 1` also exposes
the positive-dimensional group instance to Lean without an artificial typeclass
assumption.

The second declaration states Isaksen--Wang--Xu's stable-stem growth conjecture
directly on the stable representatives used by this benchmark.  Other prominent
open problems are deliberately tracked in `research/open-problems.json` rather
than weakened into placeholder Lean structures.  Freyd's generating hypothesis
and Curtis's spherical-classes conjecture need a stable homotopy category and
named stable Hurewicz operations; Moore's exponent conjecture needs finite-CW,
localization, and primary-torsion APIs.  The pinned mathlib has none of these.
Hopf invariant one is a theorem, not an open conjecture, and no concrete
`HopfInvariant` API exists from which to state it faithfully.
-/

open scoped BigOperators Topology

namespace HomotopyGroups

@[eval_problem]
theorem sphere_three_two_primary_nontrivial_conjecture (k : ℕ) :
    ∃ α : HomotopyGroup.Pi (k + 10 + 1) (SphereSpace 3) (sphereBasepoint 3),
      α ≠ 1 ∧ ∃ r : ℕ, α ^ (2 ^ (r + 1)) = 1 := by
  sorry

/-- The representative `π_(2k+2)(S^(k+2))` lies in the stable range. -/
abbrev StableSphereGroup (k : ℕ) :=
  HomotopyGroup.Pi (2 * k + 2) (SphereSpace (k + 2)) (sphereBasepoint (k + 2))

/-- An element whose order divides a power of two. -/
def IsTwoPrimaryElement {G : Type*} [Group G] (x : G) : Prop :=
  ∃ r : ℕ, x ^ (2 ^ r) = 1

/-- Cardinality of the two-primary torsion subset; stable stems above zero are finite. -/
noncomputable def twoPrimaryOrder (G : Type*) [Group G] : ℕ :=
  Nat.card {x : G // IsTwoPrimaryElement x}

/-- Product of two-primary stable-stem orders in dimensions `1` through `k`. -/
noncomputable def cumulativeTwoPrimaryStableOrder (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, twoPrimaryOrder (StableSphereGroup i)

/-- Isaksen--Wang--Xu Conjecture 1.4: cumulative two-primary order has
quadratic logarithmic growth with a nonzero limiting constant. -/
@[eval_problem]
theorem stable_two_primary_quadratic_growth_conjecture :
    ∃ C : ℝ, C ≠ 0 ∧
      Filter.Tendsto
        (fun k : ℕ =>
          Real.logb 2 ((cumulativeTwoPrimaryStableOrder k : ℕ) : ℝ) /
            (k : ℝ) ^ 2)
        Filter.atTop (nhds C) := by
  sorry

end HomotopyGroups
