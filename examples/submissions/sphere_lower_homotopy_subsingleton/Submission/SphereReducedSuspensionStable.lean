/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SphereReducedSuspensionBijective

/-!
# Reduced suspension in arbitrary positive degree

`Submission.sphereReducedSuspensionHom` already suspends cubical homotopy groups indexed by an
arbitrary nonempty coordinate type, but its target is indexed by `Option N`.  This file exposes the
specialization to the numerical groups used by the sphere lattice and packages iteration along a
fixed stem.

The resulting homomorphism

`π_(q+1)(S^n) → π_(q+2)(S^(n+1))`

is unconditional.  Bijectivity is deliberately an explicit hypothesis outside the diagonal: that
is precisely the stable-range Freudenthal input still needed before the published stable groups can
be transported across the lattice.  On the diagonal, the hypothesis is discharged by
`sphereDiagonalReducedSuspensionHom_bijective`.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-! ## Numerical reduced suspension -/

/-- Reduced suspension between exact metric-sphere homotopy groups in an arbitrary positive
degree.  The parameter `q` presents the source degree as `q + 1`, ensuring that both sides carry
their canonical group structures. -/
noncomputable def sphereReducedSuspensionPiHom (n q : ℕ) :
    π_ (q + 1) (Sph n) (sphereBasepoint n) →*
      π_ (q + 2) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  (HomotopyGroup.congrHom ((finSuccEquiv (q + 1)).symm)).comp
    (sphereReducedSuspensionHom (N := Fin (q + 1)) n (sphereBasepoint n))

/-- Bijectivity upgrades arbitrary-degree numerical reduced suspension to a multiplicative
equivalence. -/
noncomputable def sphereReducedSuspensionPiEquiv (n q : ℕ)
    (hbij : Function.Bijective (sphereReducedSuspensionPiHom n q)) :
    π_ (q + 1) (Sph n) (sphereBasepoint n) ≃*
      π_ (q + 2) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  MulEquiv.ofBijective (sphereReducedSuspensionPiHom n q) hbij

/-- The earlier diagonal homomorphism is exactly the diagonal specialization of the
arbitrary-degree construction. -/
theorem sphereReducedSuspensionPiHom_diagonal (n : ℕ) :
    sphereReducedSuspensionPiHom (n + 1) n = sphereDiagonalReducedSuspensionHom n :=
  rfl

/-- Consequently, numerical reduced suspension is unconditionally bijective on the diagonal. -/
theorem sphereReducedSuspensionPiHom_bijective_diagonal (n : ℕ) :
    Function.Bijective (sphereReducedSuspensionPiHom (n + 1) n) := by
  rw [sphereReducedSuspensionPiHom_diagonal]
  exact sphereDiagonalReducedSuspensionHom_bijective n

/-! ## Fixed-stem suspension -/

/-- Reduced suspension along the fixed stem `k`, from
`π_((n+1)+k)(S^(n+1))` to `π_((n+2)+k)(S^(n+2))`.

Writing the sphere dimension as `n + 1` makes every homotopy degree visibly positive and makes
iteration start at the canonical stable representative by taking `n = k + 1`. -/
noncomputable def sphereStemReducedSuspensionHom (n k : ℕ) :
    π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) →*
      π_ (n + k + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  sphereReducedSuspensionPiHom (n + 1) (n + k)

/-- A bijective fixed-stem suspension step as a multiplicative equivalence. -/
noncomputable def sphereStemReducedSuspensionEquiv (n k : ℕ)
    (hbij : Function.Bijective (sphereStemReducedSuspensionHom n k)) :
    π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
      π_ (n + k + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  MulEquiv.ofBijective (sphereStemReducedSuspensionHom n k) hbij

/-- The zero stem is exactly the previously constructed diagonal suspension homomorphism. -/
theorem sphereStemReducedSuspensionHom_zero (n : ℕ) :
    sphereStemReducedSuspensionHom n 0 = sphereDiagonalReducedSuspensionHom n :=
  rfl

/-- Every zero-stem step is bijective. -/
theorem sphereStemReducedSuspensionHom_bijective_zero (n : ℕ) :
    Function.Bijective (sphereStemReducedSuspensionHom n 0) := by
  rw [sphereStemReducedSuspensionHom_zero]
  exact sphereDiagonalReducedSuspensionHom_bijective n

/-! ## Iteration along a stem -/

/-- If the first `r` numerical reduced-suspension maps are bijective, their composite is a
multiplicative equivalence.  Keeping the sphere dimension and the degree parameter separate makes
the recursive indexing definitionally exact: at step `j` they are `n + j` and `q + j`. -/
theorem nonempty_sphereReducedSuspensionPiIterEquiv (n q r : ℕ)
    (hbij : ∀ j : ℕ, j < r → Function.Bijective
      (sphereReducedSuspensionPiHom (n + j) (q + j))) :
    Nonempty
      (π_ (q + 1) (Sph n) (sphereBasepoint n) ≃*
        π_ (q + r + 1) (Sph (n + r)) (sphereBasepoint (n + r))) := by
  induction r with
  | zero =>
      exact ⟨MulEquiv.refl _⟩
  | succ r ih =>
      obtain ⟨previous⟩ := ih fun j hj => hbij j (Nat.lt_succ_of_lt hj)
      let step := sphereReducedSuspensionPiEquiv (n + r) (q + r)
        (hbij r (Nat.lt_succ_self r))
      exact ⟨previous.trans step⟩

/-- Fixed-stem specialization of numerical suspension iteration.  The `j`th hypothesis is the
actual map
`π_(n+k+j+1)(S^(n+j+1)) → π_(n+k+j+2)(S^(n+j+2))`.

The equivalent indices are deliberately associated as `n + 1 + j` and `n + k + j`; this is the
recursion-friendly presentation of the same fixed stem. -/
theorem nonempty_sphereStemReducedSuspensionIterEquiv (n k r : ℕ)
    (hbij : ∀ j : ℕ, j < r → Function.Bijective
      (sphereReducedSuspensionPiHom (n + 1 + j) (n + k + j))) :
    Nonempty
      (π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        π_ (n + k + r + 1) (Sph (n + 1 + r)) (sphereBasepoint (n + 1 + r))) :=
  nonempty_sphereReducedSuspensionPiIterEquiv (n + 1) (n + k) r hbij

/-- Transport any identified group across a finite segment of a fixed stem using the concrete
reduced-suspension maps. -/
theorem sphere_stem_mulEquiv_of_reduced_suspension
    (n k r : ℕ) {G : Type*} [Group G]
    (base : Nonempty
      (π_ (n + k + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃* G))
    (hbij : ∀ j : ℕ, j < r → Function.Bijective
      (sphereReducedSuspensionPiHom (n + 1 + j) (n + k + j))) :
    Nonempty
      (π_ (n + k + r + 1) (Sph (n + 1 + r))
          (sphereBasepoint (n + 1 + r)) ≃* G) := by
  obtain ⟨transport⟩ := nonempty_sphereStemReducedSuspensionIterEquiv n k r hbij
  obtain ⟨base⟩ := base
  exact ⟨transport.symm.trans base⟩

/-- Canonical stable-representative form of fixed-stem transport.  Stem `k` starts at
`π_(2k+2)(S^(k+2))`; `r` bijective concrete suspensions transport its group to
`π_(2k+r+2)(S^(k+r+2))`.  The conclusion uses the definitionally recursive but arithmetically
equal indices `(2k+1)+r+1` and `(k+2)+r`. -/
theorem sphere_stable_stem_mulEquiv_of_reduced_suspension
    (k r : ℕ) {G : Type*} [Group G]
    (base : Nonempty
      (π_ (2 * k + 1 + 1) (Sph (k + 2)) (sphereBasepoint (k + 2)) ≃* G))
    (hbij : ∀ j : ℕ, j < r →
      Function.Bijective
        (sphereReducedSuspensionPiHom (k + 2 + j) (2 * k + 1 + j))) :
    Nonempty
      (π_ (2 * k + 1 + r + 1) (Sph (k + 2 + r))
          (sphereBasepoint (k + 2 + r)) ≃* G) := by
  obtain ⟨transport⟩ := nonempty_sphereReducedSuspensionPiIterEquiv
    (k + 2) (2 * k + 1) r hbij
  obtain ⟨base⟩ := base
  exact ⟨transport.symm.trans base⟩

/-- The iterated zero-stem transport is unconditional; this is the fixed-stem formulation of the
concrete diagonal suspension result. -/
theorem nonempty_sphereStemReducedSuspensionIterEquiv_zero (n r : ℕ) :
    Nonempty
      (π_ (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        π_ (n + r + 1) (Sph (n + r + 1)) (sphereBasepoint (n + r + 1))) := by
  induction r with
  | zero =>
      exact ⟨MulEquiv.refl _⟩
  | succ r ih =>
      obtain ⟨previous⟩ := ih
      exact ⟨previous.trans (sphereDiagonalReducedSuspensionEquiv (n + r))⟩

end Submission
