/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.AbsoluteIsomorphism
import Submission.MetricSpherePiOneGeneric

/-!
# The homotopy groups on the sphere diagonal

The first-nonvanishing Hurewicz isomorphism and the integral top homology of a sphere compute
`π_d(S^d)` for every `d ≥ 2`. Together with the metric-circle calculation, this gives a
challenge-independent theorem for every positive-dimensional metric sphere and every basepoint.
-/

open CategoryTheory
open scoped Topology

noncomputable section

namespace Submission

/-- In every dimension at least two and at every basepoint, first-nonvanishing Hurewicz followed
by the sphere's top-homology orientation identifies the diagonal homotopy group with `ℤ`. -/
theorem sphere_diagonal_sph_succ_at_mulEquiv_int (n : ℕ) (x : Sph (n + 2)) :
    Nonempty
      (HomotopyGroup.Pi (n + 2) (Sph (n + 2)) x ≃*
        Multiplicative ℤ) := by
  let hHurewicz :
      Additive (HomotopyGroup.Pi (n + 2) (Sph (n + 2)) x) ≃+
        (Hgrp (n + 2) (TopCat.of (Sph (n + 2))) : Type) :=
    (isNConnected_sphere_succ_succ n).absoluteHurewiczAddEquiv x
  let hHomology :
      (Hgrp (n + 2) (TopCat.of (Sph (n + 2))) : Type) ≃+ ℤ := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      (hgrpSphereSelfIsoZ (n + 1)).addCommGroupIsoToAddEquiv
  exact ⟨AddEquiv.toMultiplicativeRight (hHurewicz.trans hHomology)⟩

/-- For every positive sphere dimension and every basepoint, the diagonal homotopy group of the
metric sphere is infinite cyclic. -/
theorem sphere_diagonal_sph_at_mulEquiv_int (n : ℕ) (x : Sph (n + 1)) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) x ≃*
        Multiplicative ℤ) := by
  cases n with
  | zero => simpa using pi1_sph_one_at_mulEquiv_int x
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        sphere_diagonal_sph_succ_at_mulEquiv_int n x

end Submission
