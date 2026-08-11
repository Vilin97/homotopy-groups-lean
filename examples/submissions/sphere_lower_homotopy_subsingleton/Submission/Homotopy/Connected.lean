/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.WhiteheadTheorem.RelHomotopyGroup.Defs

/-!
# `n`-connectedness

A space is `n`-connected when it is path connected and its homotopy groups vanish up to degree
`n`; a pair `(X, A)` is `n`-connected when every relative homotopy group up to degree `n` is
trivial and `π₀(A) → π₀(X)` is surjective.

The `Nonempty (Unique …)` phrasing of `IsNConnectedPair.unique_piRel` is deliberate: it is exactly
the hypothesis shape consumed by `TopCat.disk.homotopicRel_boundary_of_unique_pi` and
`TopCat.disk.isCompressible_subtype_val_of_unique_pi` in the vendored WhiteheadTheorem library.
-/

open scoped Topology

namespace Submission

/-- `X` is `n`-connected: nonempty, path connected, and `π_k(X, x) = 1` for `1 ≤ k ≤ n`. -/
structure IsNConnected (n : ℕ) (X : Type) [TopologicalSpace X] : Prop where
  /-- an `n`-connected space is nonempty -/
  nonempty : Nonempty X
  /-- an `n`-connected space is path connected -/
  pathConnected : PathConnectedSpace X
  /-- the homotopy groups vanish up to degree `n` -/
  subsingleton_pi : ∀ k, k + 1 ≤ n → ∀ x : X, Subsingleton (HomotopyGroup.Pi (k + 1) X x)

/-- The pair `(X, A)` is `n`-connected. -/
structure IsNConnectedPair (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) : Prop where
  /-- every point of `X` can be joined to `A` -/
  surjective_iStar_zero : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a)
  /-- the relative homotopy groups vanish up to degree `n` -/
  unique_piRel : ∀ k, k + 1 ≤ n → ∀ a : A, Nonempty (Unique (π_rel (k + 1) X A a))

namespace IsNConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X]

theorem mono {m n : ℕ} (h : m ≤ n) (hX : IsNConnected n X) : IsNConnected m X where
  nonempty := hX.nonempty
  pathConnected := hX.pathConnected
  subsingleton_pi k hk := hX.subsingleton_pi k (hk.trans h)

/-- A path-connected nonempty space is `0`-connected. -/
theorem zero (hne : Nonempty X) (hpc : PathConnectedSpace X) : IsNConnected 0 X where
  nonempty := hne
  pathConnected := hpc
  subsingleton_pi k hk := by omega

end IsNConnected

namespace IsNConnectedPair

variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X}

theorem mono {m n : ℕ} (h : m ≤ n) (hX : IsNConnectedPair n X A) : IsNConnectedPair m X A where
  surjective_iStar_zero := hX.surjective_iStar_zero
  unique_piRel k hk := hX.unique_piRel k (hk.trans h)

end IsNConnectedPair

end Submission
