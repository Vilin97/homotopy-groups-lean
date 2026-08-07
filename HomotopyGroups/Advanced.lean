import EvalTools.Markers
import HomotopyGroups.Spaces
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Advanced global results about homotopy groups of spheres

The finiteness declarations are concrete forms of Serre's rational computation:
apart from the diagonal group, the only nonfinite case is `π_(2n-1)(S^n)` for
even `n`, where the group has rank one.  The bundled finite commutative group in
`serre_even_sphere_exceptional_rank_one` states this without introducing an
unformalized rationalization operation.

There is no native suspension homomorphism, Hurewicz map, Hopf invariant,
Whitehead product, relative homotopy group, or long exact fibration sequence in
the pinned mathlib.  Consequently, Freudenthal, Hurewicz, Hopf-invariant-one,
and EHP statements are documented blockers rather than fake benchmark holes.
-/

open scoped Topology

namespace HomotopyGroups

@[eval_problem]
theorem serre_finiteness_odd_sphere
    (n k : ℕ) (hk : 2 * n + 3 < k) :
    Finite
      (HomotopyGroup.Pi k (SphereSpace (2 * n + 3))
        (sphereBasepoint (2 * n + 3))) := by
  sorry

@[eval_problem]
theorem serre_finiteness_even_sphere
    (n k : ℕ)
    (hk : 2 * (n + 1) < k) (hExceptional : k ≠ 4 * n + 3) :
    Finite
      (HomotopyGroup.Pi k (SphereSpace (2 * (n + 1)))
        (sphereBasepoint (2 * (n + 1)))) := by
  sorry

@[eval_problem]
theorem serre_even_sphere_exceptional_rank_one (n : ℕ) :
    ∃ T : CommGrpCat, Finite T ∧
      Nonempty
        (HomotopyGroup.Pi (4 * n + 3) (SphereSpace (2 * (n + 1)))
            (sphereBasepoint (2 * (n + 1))) ≃*
          Multiplicative ℤ × T) := by
  sorry

@[eval_problem]
theorem sphere_two_all_higher_homotopy_nontrivial (k : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (k + 2) (SphereSpace 2) (sphereBasepoint 2)) := by
  sorry

@[eval_problem]
theorem sphere_three_all_higher_homotopy_nontrivial (k : ℕ) :
    Nontrivial
      (HomotopyGroup.Pi (k + 3) (SphereSpace 3) (sphereBasepoint 3)) := by
  sorry

end HomotopyGroups
