/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.DiagonalInduction
import Submission.ForMathlib.HomotopyGroup.Congr
import Submission.ForMathlib.HomotopyGroup.Map
import Submission.Model.ReducedSuspensionSphere
import Submission.ReducedSuspensionGroup

/-!
# Reduced suspension as a homomorphism between metric-sphere homotopy groups

The general reduced-suspension homomorphism lands in a quotient space and adds an `Option`
coordinate.  This file transports its target through the pointed sphere homeomorphism and
reindexes the cube along `Option (Fin n) ≃ Fin (n+1)`.  The result is an unconditional monoid
homomorphism between successive positive diagonal groups in the exact metric-sphere model.

Consequently the remaining input for propagation of the integral diagonal is bijectivity alone;
multiplication compatibility is no longer a separate hypothesis.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- Reduced suspension followed by the pointed homeomorphism to the next metric sphere. -/
noncomputable def sphereReducedSuspensionHom {N : Type*} [DecidableEq N] [Nonempty N]
    (n : ℕ) (x₀ : Sph n) :
    HomotopyGroup N (Sph n) x₀ →*
      HomotopyGroup (Option N) (Sph (n + 1)) (sphereBasepoint (n + 1)) :=
  (HomotopyGroup.mapHom (N := Option N)
    (⟨ReducedSusp.sphereHomeomorph n x₀,
      (ReducedSusp.sphereHomeomorph n x₀).continuous⟩ :
      C(ReducedSusp (Sph n) x₀, Sph (n + 1)))
    (ReducedSusp.sphereHomeomorph_base n x₀)).comp
      HomotopyGroup.reducedSuspensionHom

/-- The reduced-suspension homomorphism between successive metric-sphere diagonal groups. -/
noncomputable def sphereDiagonalReducedSuspensionHom (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) →*
      HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  (HomotopyGroup.congrHom ((finSuccEquiv (n + 1)).symm)).comp
    (sphereReducedSuspensionHom (N := Fin (n + 1)) (n + 1) (sphereBasepoint (n + 1)))

/-- Bijectivity upgrades metric-sphere reduced suspension to the equivalence needed by diagonal
induction. -/
noncomputable def sphereDiagonalReducedSuspensionMulEquiv (n : ℕ)
    (hbij : Function.Bijective (sphereDiagonalReducedSuspensionHom n)) :
    HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
      HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2)) :=
  MulEquiv.ofBijective (sphereDiagonalReducedSuspensionHom n) hbij

/-- Concrete reduction of the exact integral diagonal to bijectivity alone for the constructed
metric-sphere reduced-suspension homomorphism. -/
theorem sphere_diagonal_mulEquiv_int_of_reduced_suspension_bijective
    (hbij : ∀ n : ℕ, Function.Bijective (sphereDiagonalReducedSuspensionHom n))
    (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  apply sphere_diagonal_mulEquiv_int_of_suspension_steps
  intro m
  exact ⟨sphereDiagonalReducedSuspensionMulEquiv m (hbij m)⟩

end Submission
