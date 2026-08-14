import EvalTools.Markers
import HomotopyGroups.Spaces
import Mathlib.Data.ZMod.Basic

/-!
# Statement families added from the literature review

These declarations close the most immediate formal-statement gaps found while
auditing the accompanying literature review.  They deliberately state concrete
group equivalences for the benchmark's metric-sphere model.  Their presence is
not a claim that the proofs already exist in the pinned Mathlib.

The integral Toda table through the 19-stem is generated separately from its
versioned CSV registry in `HomotopyGroups.TodaTable`.  The exact positive-stem
3-primary table through 108 is generated in
`HomotopyGroups.StableThreePrimary`, using Mathlib's existing
`CommGroup.primaryComponent`.  The complete Mimura--Toda 20-stem is generated
from its source-audited CSV in `HomotopyGroups.MimuraTodaTable`.  The
2-primary-only unstable tables still need structured transcriptions;
degree-zero p-local statements still need localization foundations.
-/

open scoped Topology

namespace HomotopyGroups

/-- Every homotopy group of the metric circle above degree one is trivial. -/
@[eval_problem]
theorem sphere_one_higher_homotopy_subsingleton (k : ℕ) :
    Subsingleton
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (sphereBasepoint 1)) := by
  exact Submission.sph_one_higher_homotopy_subsingleton_at k (sphereBasepoint 1)

/-- The complete second-offset family: `pi_(n+2)(S^n) = C2` for `n >= 2`. -/
@[eval_problem]
theorem sphere_second_offset_homotopy_mulEquiv_zmod_two
    (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 2) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- The first exceptional third-offset value: `pi_5(S^2) = C2`. -/
@[eval_problem]
theorem pi5_sphere_two_mulEquiv_zmod_two :
    Nonempty
      (HomotopyGroup.Pi 5 (SphereSpace 2) (sphereBasepoint 2) ≃*
        Multiplicative (ZMod 2)) := by
  sorry

/-- The second exceptional third-offset value: `pi_6(S^3) = C12`. -/
@[eval_problem]
theorem pi6_sphere_three_mulEquiv_zmod_twelve :
    Nonempty
      (HomotopyGroup.Pi 6 (SphereSpace 3) (sphereBasepoint 3) ≃*
        Multiplicative (ZMod 12)) := by
  sorry

/-- The third exceptional third-offset value: `pi_7(S^4) = Z x C12`. -/
@[eval_problem]
theorem pi7_sphere_four_mulEquiv_int_prod_zmod_twelve :
    Nonempty
      (HomotopyGroup.Pi 7 (SphereSpace 4) (sphereBasepoint 4) ≃*
        Multiplicative ℤ × Multiplicative (ZMod 12)) := by
  sorry

/-- The stable part of the third offset: `pi_(n+3)(S^n) = C24` for `n >= 5`. -/
@[eval_problem]
theorem sphere_third_offset_stable_mulEquiv_zmod_twenty_four
    (n : ℕ) (hn : 5 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi (n + 3) (SphereSpace n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 24)) := by
  sorry

/-- Every positive stable stem is finite, stated at the canonical representative
used by this benchmark. -/
@[eval_problem]
theorem positive_stable_stem_finite (k : ℕ) (hk : 0 < k) :
    Finite
      (HomotopyGroup.Pi (2 * k + 2) (SphereSpace (k + 2))
        (sphereBasepoint (k + 2))) := by
  sorry

end HomotopyGroups
