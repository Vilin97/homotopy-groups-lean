/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.AbsoluteIsomorphism
import Submission.MetricSpherePiOne

/-!
# The homotopy groups on the sphere diagonal

The first-nonvanishing Hurewicz isomorphism and the integral top homology of a sphere compute
`pi_d(S^d)` for every `d >= 2`.  Combining this with the maintained metric-circle computation
gives the uniform exact-model diagonal theorem used by the benchmark.
-/

open CategoryTheory HomotopyGroups
open scoped Topology

noncomputable section

namespace Submission

/-- In every dimension at least two, first-nonvanishing Hurewicz followed by the sphere's top
homology orientation identifies the diagonal homotopy group with the integers. -/
theorem sphere_diagonal_succ_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 2) (SphereSpace (n + 2))
          (sphereBasepoint (n + 2)) ≃*
        Multiplicative ℤ) := by
  let hHurewicz :
      Additive
          (HomotopyGroup.Pi (n + 2) (SphereSpace (n + 2))
            (sphereBasepoint (n + 2))) ≃+
        (Hgrp (n + 2) (TopCat.of (SphereSpace (n + 2))) : Type) :=
    (isNConnected_sphere_succ_succ n).absoluteHurewiczAddEquiv
      (sphereBasepoint (n + 2))
  let hHomology :
      (Hgrp (n + 2) (TopCat.of (SphereSpace (n + 2))) : Type) ≃+ ℤ := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      (hgrpSphereSelfIsoZ (n + 1)).addCommGroupIsoToAddEquiv
  exact ⟨AddEquiv.toMultiplicativeRight (hHurewicz.trans hHomology)⟩

/-- **The integral sphere diagonal:** for every `d >= 1`, the benchmark's exact metric-sphere
model satisfies `pi_d(S^d) ≅ ℤ`. -/
theorem sphere_diagonal_homotopy_mulEquiv_int (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1))
          (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  cases n with
  | zero => simpa using pi1_sphere_one_mulEquiv_int
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        sphere_diagonal_succ_mulEquiv_int n

end Submission
