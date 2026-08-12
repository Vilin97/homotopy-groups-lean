/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.LoopSphereHomology
import Submission.Homotopy.FibrationLESGroup
import Submission.Homotopy.LoopSpace
import Submission.Hurewicz.DegreeOne

/-!
# The second homotopy group of the two-sphere

This file proves `π₂(S²) ≃ ℤ` independently of the generated benchmark declarations. The proof
shifts `π₂(S²)` to `π₁(ΩS²)` using the path fibration, applies the degree-one Hurewicz theorem,
and uses the integral homology calculation `H₁(ΩS²) ≃ ℤ`.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

noncomputable section

namespace Submission

/-- At the south pole, the path-fibration connecting map, degree-one Hurewicz, and the homology
of the loop space identify `π₂(S²)` with `ℤ`. -/
theorem pi2_sphere_two_at_southPole_mulEquiv_int :
    Nonempty (π_ 2 (Sph 2) (southPoleVal 1) ≃* Multiplicative ℤ) := by
  let x₀ : Sph 2 := southPoleVal 1
  change Nonempty (π_ 2 (Sph 2) x₀ ≃* Multiplicative ℤ)
  let e : π_ 2 (Sph 2) x₀ ≃* π_ 1 (pathFib x₀) (loopBase x₀) :=
    fibDeltaMulEquiv (loopBase x₀) (isSerreFibration_ev₁ (Sph 2) x₀) 0
      (subsingleton_pi_pathSpace x₀ 2 _)
      (subsingleton_pi_pathSpace x₀ 1 _)
  letI : CommGroup (π_ 1 (pathFib x₀) (loopBase x₀)) :=
    { (inferInstance : Group (π_ 1 (pathFib x₀) (loopBase x₀))) with
      mul_comm := fun a b => e.symm.injective (by
        simpa only [map_mul] using mul_comm (e.symm a) (e.symm b)) }
  letI : PathConnectedSpace (pathFib x₀) :=
    pathConnectedSpace_pathFibre ⟨Path.refl x₀⟩
      (fun p q => paths_homotopic_sph (by omega) p q)
  let hHurewicz : Additive (π_ 1 (pathFib x₀) (loopBase x₀)) ≃+
      (Hgrp 1 (pathFib x₀) : Type) :=
    (MulEquiv.toAdditive Abelianization.equivOfComm).trans
      (hurewiczOnePiOfSpace (pathFib x₀) (loopBase x₀))
  let hHomology : (Hgrp 1 (pathFib x₀) : Type) ≃+ ℤ :=
    (loopSphereHgrpMul x₀ (by omega) 1).addCommGroupIsoToAddEquiv
  exact ⟨e.trans (AddEquiv.toMultiplicativeRight (hHurewicz.trans hHomology))⟩

/-- The second homotopy group of the metric two-sphere is infinite cyclic at every basepoint. -/
theorem pi2_sphere_two_at_mulEquiv_int (x : Sph 2) :
    Nonempty (π_ 2 (Sph 2) x ≃* Multiplicative ℤ) := by
  letI := pathConnectedSpace_sph (n := 2) (by omega)
  obtain ⟨changeBasepoint⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 2) x (southPoleVal 1)
  obtain ⟨atSouthPole⟩ := pi2_sphere_two_at_southPole_mulEquiv_int
  exact ⟨changeBasepoint.trans atSouthPole⟩

end Submission
