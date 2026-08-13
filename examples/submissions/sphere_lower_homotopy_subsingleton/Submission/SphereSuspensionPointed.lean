/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.DiagonalInduction
import Submission.SphereSuspensionConst

/-!
# Pointed and group-level properties of diagonal sphere suspension

The explicit meridian contraction from `Submission.SphereSuspensionConst` shows that geometric
diagonal suspension preserves the identity element of the homotopy group.

We then bundle diagonal suspension as a `OneHom` and isolate the two remaining facts needed for
the exact diagonal calculation on the actual geometric map: multiplication compatibility and
bijectivity.  Supplying those facts produces the successive `MulEquiv`s consumed by
`Submission.sphere_diagonal_mulEquiv_int_of_suspension_steps`.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The suspension of the constant based sphere self-map is based-nullhomotopic. -/
noncomputable def sphereSuspensionConstHomotopy (n : ℕ) :
    ContinuousMap.Homotopy
      (sphereSuspensionSelfMap n
        (ContinuousMap.const (Sph n) (sphereBasepoint n)))
      (ContinuousMap.const (Sph (n + 1)) (sphereBasepoint (n + 1))) :=
  sphereSuspensionMapConstHomotopy n n

/-- The nullhomotopy of the suspended constant self-map fixes the sphere basepoint. -/
theorem sphereSuspensionConstHomotopy_basepoint (n : ℕ) (t : I) :
    sphereSuspensionConstHomotopy n (t, sphereBasepoint (n + 1)) =
      sphereBasepoint (n + 1) :=
  sphereSuspensionMapConstHomotopy_basepoint n n t

/-- The constant based sphere self-map represents the identity homotopy class. -/
@[simp]
theorem sphereSelfMapClass_const (n : ℕ) :
    sphereSelfMapClass (n + 1)
      (ContinuousMap.const (Sph (n + 1)) (sphereBasepoint (n + 1))) rfl = 1 := by
  rw [HomotopyGroup.one_def]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro x
  rfl

/-- Geometric diagonal suspension preserves the identity class. -/
@[simp]
theorem sphereDiagonalSuspension_one (n : ℕ) :
    sphereDiagonalSuspension n
      (1 : HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1))) = 1 := by
  rw [HomotopyGroup.one_def, sphereDiagonalSuspension_mk]
  change sphereSuspensionSelfMapClass (n + 1)
      (genLoopSphereMap n
        (GenLoop.const : Ω^ (Fin (n + 1)) (Sph (n + 1)) (sphereBasepoint (n + 1))))
      (genLoopSphereMap_basepoint n _) = 1
  simp only [genLoopSphereMap_const]
  change sphereSuspensionSelfMapClass (n + 1)
      (ContinuousMap.const (Sph (n + 1)) (sphereBasepoint (n + 1))) rfl = 1
  rw [← sphereSelfMapClass_const (n + 1)]
  exact sphereSelfMapClass_eq_of_homotopy (n + 2)
    (sphereSuspensionSelfMap_basepoint (n + 1)
      (ContinuousMap.const (Sph (n + 1)) (sphereBasepoint (n + 1))) rfl)
    rfl (sphereSuspensionConstHomotopy (n + 1))
    (sphereSuspensionConstHomotopy_basepoint (n + 1))

/-- Diagonal suspension as an identity-preserving map. -/
noncomputable def sphereDiagonalSuspensionOneHom (n : ℕ) :
    OneHom
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)))
      (HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2))) where
  toFun := sphereDiagonalSuspension n
  map_one' := sphereDiagonalSuspension_one n

@[simp]
theorem sphereDiagonalSuspensionOneHom_apply (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1))) :
    sphereDiagonalSuspensionOneHom n a = sphereDiagonalSuspension n a :=
  rfl

/-- Diagonal suspension is nonconstant: it carries the canonical generator to a nonidentity
class in the next dimension. -/
theorem sphereDiagonalSuspension_generator_ne_one (n : ℕ) :
    sphereDiagonalSuspension n (sphereGeneratorClass (n + 1)) ≠ 1 := by
  rw [sphereDiagonalSuspension_generator]
  exact sphereGeneratorClass_ne_one (n + 1)

/-- Once multiplication compatibility is supplied, geometric diagonal suspension bundles as a
monoid homomorphism. -/
noncomputable def sphereDiagonalSuspensionMonoidHom (n : ℕ)
    (hmul : ∀ a b : HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)),
      sphereDiagonalSuspension n (a * b) =
        sphereDiagonalSuspension n a * sphereDiagonalSuspension n b) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) →*
      HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) where
  toFun := sphereDiagonalSuspension n
  map_one' := sphereDiagonalSuspension_one n
  map_mul' := hmul

/-- Multiplication compatibility and bijectivity upgrade the actual geometric suspension map to
the successive multiplicative equivalence required by diagonal induction. -/
noncomputable def sphereDiagonalSuspensionMulEquiv (n : ℕ)
    (hmul : ∀ a b : HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)),
      sphereDiagonalSuspension n (a * b) =
        sphereDiagonalSuspension n a * sphereDiagonalSuspension n b)
    (hbij : Function.Bijective (sphereDiagonalSuspension n)) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
      HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  MulEquiv.ofBijective (sphereDiagonalSuspensionMonoidHom n hmul) hbij

/-- Concrete reduction of the exact sphere diagonal to multiplicativity and bijectivity of the
geometric suspension function constructed in this development. -/
theorem sphere_diagonal_mulEquiv_int_of_geometric_suspension
    (hmul : ∀ (n : ℕ)
      (a b : HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1))),
      sphereDiagonalSuspension n (a * b) =
        sphereDiagonalSuspension n a * sphereDiagonalSuspension n b)
    (hbij : ∀ n : ℕ, Function.Bijective (sphereDiagonalSuspension n))
    (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  apply sphere_diagonal_mulEquiv_int_of_suspension_steps
  intro m
  exact ⟨sphereDiagonalSuspensionMulEquiv m (hmul m) (hbij m)⟩

end Submission
