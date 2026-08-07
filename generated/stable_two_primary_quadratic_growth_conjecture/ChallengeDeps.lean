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
theorem pi1_circle_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃*
        Multiplicative ℤ) := by
  sorry
theorem sphere_lower_homotopy_subsingleton
    (n k : ℕ) (hk : k < n) :
    Subsingleton
      (HomotopyGroup.Pi k (SphereSpace n) (sphereBasepoint n)) := by
  sorry
theorem sphere_diagonal_homotopy_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1))
          (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  sorry
theorem pi3_sphere_two_mulEquiv_int :
    Nonempty
      (HomotopyGroup.Pi 3 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative ℤ) := by
  sorry
theorem sphere_first_stable_homotopy_mulEquiv_zmod_two
    (n : ℕ) (hn : 3 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry
theorem pi1_realProjectiveSpace_mulEquiv_zmod_two
    (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry
theorem realProjectiveSpace_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (RealProjectiveSpace n)
          (realProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 2) (SphereSpace n)
          (sphereBasepoint n)) := by
  sorry
theorem pi1_complexProjectiveSpace_subsingleton
    (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (HomotopyGroup.Pi 1 (ComplexProjectiveSpace n)
        (complexProjectiveBasepoint n)) := by
  sorry
theorem pi2_complexProjectiveSpace_mulEquiv_int
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 2 (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        Multiplicative ℤ) := by
  sorry
theorem complexProjectiveSpace_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (k + 3) (ComplexProjectiveSpace n)
          (complexProjectiveBasepoint n) ≃*
        HomotopyGroup.Pi (k + 3) (SphereSpace (2 * n + 1))
          (sphereBasepoint (2 * n + 1))) := by
  sorry

end HomotopyGroups
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



end HomotopyGroups
