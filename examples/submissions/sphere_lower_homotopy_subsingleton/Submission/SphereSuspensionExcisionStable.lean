/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereSuspensionHurewicz

/-!
# Stable-range sphere suspension through cap excision

`Submission.sphereSuspensionExcisionHomAt` exposes the cap-inclusion map in every relative
degree.  This file records exactly how much of its bijectivity is already known and packages the
remaining stable-range homotopy-excision statement in subtraction-free coordinates, together
with its fixed-stem consequences.

The map is bijective below the diagonal because both relative groups vanish, and on the diagonal
by the relative Hurewicz proof.  Consequently the genuinely new content of stable homotopy
excision consists only of positive stems.  If that statement is supplied, the final section
iterates the resulting absolute sphere equivalences from the canonical stable representative
`π_(2k+2)(S^(k+2))` throughout stem `k`.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## The proved range -/

/-- The first-nonzero-degree theorem is the diagonal specialization of arbitrary-degree cap
excision. -/
theorem sphereSuspensionExcisionHomAt_bijective_diagonal (n : ℕ) :
    Function.Bijective (sphereSuspensionExcisionHomAt (n + 1) n) := by
  rw [sphereSuspensionExcisionHomAt_diagonal]
  exact sphereSuspensionExcisionHom_bijective n

/-- Cap excision is already bijective in every degree through the sphere diagonal: below it both
relative groups are trivial, and at it relative Hurewicz applies. -/
theorem sphereSuspensionExcisionHomAt_bijective_to_diagonal
    (m q : ℕ) (hm : 1 ≤ m) (hq : q + 1 ≤ m) :
    Function.Bijective (sphereSuspensionExcisionHomAt m q) := by
  by_cases hlt : q + 1 < m
  · exact sphereSuspensionExcisionHomAt_bijective_below m q hm (by omega)
  · have hmq : m = q + 1 := by omega
    subst m
    exact sphereSuspensionExcisionHomAt_bijective_diagonal q

/-! ## The remaining stable-range assertion -/

/-- Cap excision along stem `k`, from sphere dimension `n+1` and absolute degree `n+k+1`.
Its relative degree is one larger. -/
noncomputable def sphereStemSuspensionExcisionHom (n k : ℕ) :=
  sphereSuspensionExcisionHomAt (n + 1) (n + k)

/-- The zero-stem specialization is the original diagonal cap-excision map. -/
theorem sphereStemSuspensionExcisionHom_zero (n : ℕ) :
    sphereStemSuspensionExcisionHom n 0 = sphereSuspensionExcisionHom n :=
  rfl

/-- The zero stem of cap excision is unconditionally bijective. -/
theorem sphereStemSuspensionExcisionHom_bijective_zero (n : ℕ) :
    Function.Bijective (sphereStemSuspensionExcisionHom n 0) := by
  rw [sphereStemSuspensionExcisionHom_zero]
  exact sphereSuspensionExcisionHom_bijective n

/-- The stable-range homotopy-excision assertion.  Here `m` is the source sphere dimension and
`q+1` is the absolute homotopy degree.  The subtraction-free inequality `q+3 ≤ 2m` is exactly
Freudenthal's isomorphism range `q+1 ≤ 2m-2`. -/
def SphereSuspensionExcisionStableRange : Prop :=
  ∀ m q : ℕ, 2 ≤ m → q + 3 ≤ 2 * m →
    Function.Bijective (sphereSuspensionExcisionHomAt m q)

/-- Since cap excision is proved through the diagonal, the stable-range assertion is equivalent
to its restriction strictly above the diagonal.  This is the precise remaining
Blakers--Massey gap. -/
theorem sphereSuspensionExcisionStableRange_iff_positiveStem :
    SphereSuspensionExcisionStableRange ↔
      ∀ m q : ℕ, 2 ≤ m → m < q + 1 → q + 3 ≤ 2 * m →
        Function.Bijective (sphereSuspensionExcisionHomAt m q) := by
  constructor
  · intro h m q hm _ hrange
    exact h m q hm hrange
  · intro h m q hm hrange
    by_cases hdiag : q + 1 ≤ m
    · exact sphereSuspensionExcisionHomAt_bijective_to_diagonal m q (by omega) hdiag
    · exact h m q hm (by omega) hrange

/-- Stable-range cap excision in the usual fixed-stem coordinates. -/
theorem sphereStemSuspensionExcisionHom_bijective_of_stableRange
    (hstable : SphereSuspensionExcisionStableRange)
    (n k : ℕ) (hkn : k + 1 ≤ n) :
    Function.Bijective (sphereStemSuspensionExcisionHom n k) :=
  hstable (n + 1) (n + k) (by omega) (by omega)

/-! ## Absolute consequences and iteration -/

/-- A bijective fixed-stem cap-excision step yields the corresponding equivalence of absolute
sphere homotopy groups. -/
theorem nonempty_sphereStemSuspensionMulEquiv_of_capExcision
    (n k : ℕ)
    (hbij : Function.Bijective (sphereStemSuspensionExcisionHom n k)) :
    Nonempty
      (π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        π_ (n + k + 2) (Sph (n + 2)) (sphereBasepoint (n + 2))) := by
  simpa only [sphereStemSuspensionExcisionHom, Nat.add_assoc] using
    (nonempty_sphereSuspensionMulEquiv_of_capExcisionAt
      (n + 1) (n + k) (by omega) hbij)

/-- Iterating a finite family of bijective fixed-stem cap maps gives an equivalence between the
endpoint sphere homotopy groups. -/
theorem nonempty_sphereStemCapExcisionIterEquiv
    (n k r : ℕ)
    (hbij : ∀ j : ℕ, j < r →
      Function.Bijective (sphereStemSuspensionExcisionHom (n + j) k)) :
    Nonempty
      (π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        π_ (n + k + r + 1) (Sph (n + r + 1))
          (sphereBasepoint (n + r + 1))) := by
  induction r with
  | zero =>
      exact ⟨MulEquiv.refl _⟩
  | succ r ih =>
      obtain ⟨previous⟩ := ih fun j hj => hbij j (Nat.lt_succ_of_lt hj)
      obtain ⟨step⟩ := nonempty_sphereStemSuspensionMulEquiv_of_capExcision
        (n + r) k (hbij r (Nat.lt_succ_self r))
      let step' :
          π_ (n + k + r + 1) (Sph (n + r + 1))
              (sphereBasepoint (n + r + 1)) ≃*
            π_ (n + k + r + 2) (Sph (n + r + 2))
              (sphereBasepoint (n + r + 2)) := by
        have hdeg : n + r + k = n + k + r := by omega
        rw [hdeg] at step
        exact step
      exact ⟨previous.trans step'⟩

/-- Arbitrary-degree form of finite cap-excision iteration.  At step `j`, both the sphere
dimension and homotopy-degree parameter have increased by `j`. -/
theorem nonempty_sphereCapExcisionIterEquiv
    (m q r : ℕ) (hm : 1 ≤ m)
    (hbij : ∀ j : ℕ, j < r →
      Function.Bijective (sphereSuspensionExcisionHomAt (m + j) (q + j))) :
    Nonempty
      (π_ (q + 1) (Sph m) (sphereBasepoint m) ≃*
        π_ (q + r + 1) (Sph (m + r)) (sphereBasepoint (m + r))) := by
  induction r with
  | zero =>
      exact ⟨MulEquiv.refl _⟩
  | succ r ih =>
      obtain ⟨previous⟩ := ih fun j hj => hbij j (Nat.lt_succ_of_lt hj)
      obtain ⟨step⟩ := nonempty_sphereSuspensionMulEquiv_of_capExcisionAt
        (m + r) (q + r) (by omega) (hbij r (Nat.lt_succ_self r))
      exact ⟨previous.trans step⟩

/-- Assuming stable-range cap excision, every stem can be transported from its canonical stable
representative `π_(2k+2)(S^(k+2))` through any finite number of suspensions. -/
theorem nonempty_sphereStableStemCapExcisionIterEquiv
    (hstable : SphereSuspensionExcisionStableRange) (k r : ℕ) :
    Nonempty
      (π_ (2 * k + 1 + 1) (Sph (k + 2)) (sphereBasepoint (k + 2)) ≃*
        π_ (2 * k + 1 + r + 1) (Sph (k + 2 + r))
          (sphereBasepoint (k + 2 + r))) := by
  exact nonempty_sphereCapExcisionIterEquiv (k + 2) (2 * k + 1) r (by omega)
    (fun j _ => hstable (k + 2 + j) (2 * k + 1 + j) (by omega) (by omega))

/-- Transport any identified stable representative throughout its stem, conditional only on the
single stable-range cap-excision assertion. -/
theorem sphere_stable_stem_mulEquiv_of_capExcision
    (hstable : SphereSuspensionExcisionStableRange)
    (k r : ℕ) {G : Type*} [Group G]
    (base : Nonempty
      (π_ (2 * k + 1 + 1) (Sph (k + 2)) (sphereBasepoint (k + 2)) ≃* G)) :
    Nonempty
      (π_ (2 * k + 1 + r + 1) (Sph (k + 2 + r))
          (sphereBasepoint (k + 2 + r)) ≃* G) := by
  obtain ⟨transport⟩ := nonempty_sphereStableStemCapExcisionIterEquiv hstable k r
  obtain ⟨base⟩ := base
  exact ⟨transport.symm.trans base⟩

end Submission
