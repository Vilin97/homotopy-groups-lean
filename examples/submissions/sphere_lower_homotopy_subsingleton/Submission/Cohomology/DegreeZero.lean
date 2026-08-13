/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Singular
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Degree-zero singular cohomology of connected spaces

A zero-cocycle has equal values on the two ends of every edge, so it factors through the set of
connected components.  On a connected simplicial set it is therefore constant.  Consequently,
pullback in degree zero along any map whose source is connected is surjective.

## Main results

* `Submission.zeroCocycle_eq_smul_one` -- a zero-cocycle on a connected simplicial set is
  constant;
* `Submission.surjective_Hcoh_map_zero_of_isConnected` -- degree-zero pullback onto a connected
  simplicial set is surjective;
* `Submission.surjective_Hsing_map_zero_of_pathConnected` -- the topological specialization.
-/

open CategoryTheory Simplicial

noncomputable section

namespace Submission

variable {R : Type} [CommRing R]

/-- A zero-cocycle takes equal values at the ends of every edge. -/
theorem zeroCocycle_eq_of_edge {S : SSet.{0}} (f : cocycles S R 0)
    {x y : S _⦋0⦌} (e : S.Edge x y) :
    (f : Cochain S R 0) x = (f : Cochain S R 0) y := by
  have h := congrFun f.2 e.edge
  have h' : (f : Cochain S R 0) (SSet.face S 0 e.edge) -
      (f : Cochain S R 0) (SSet.face S 1 e.edge) = 0 := by
    simpa [coboundary_apply, Fin.sum_univ_two, sub_eq_add_neg] using h
  have h₀ : SSet.face S 0 e.edge = y := by
    simpa only [SSet.face, SSet.restrict, SimplicialObject.δ_def] using e.tgt_eq
  have h₁ : SSet.face S 1 e.edge = x := by
    simpa only [SSet.face, SSet.restrict, SimplicialObject.δ_def] using e.src_eq
  rw [h₀, h₁] at h'
  exact (sub_eq_zero.mp h').symm

/-- Every zero-cocycle on a connected simplicial set is a scalar multiple of the unit cocycle. -/
theorem zeroCocycle_eq_smul_one {S : SSet.{0}} [S.IsConnected]
    (f : cocycles S R 0) (x : S _⦋0⦌) :
    f = (f : Cochain S R 0) x • oneCocycle S R := by
  apply Subtype.ext
  ext y
  let g : S.π₀ → R := SSet.π₀.lift (f : Cochain S R 0)
    fun _ _ e ↦ zeroCocycle_eq_of_edge f e
  have hxy : SSet.π₀.mk y = SSet.π₀.mk x := Subsingleton.elim _ _
  have h := congrArg g hxy
  simpa [g, oneCocycle, Cochain.one] using h

/-- Pullback in degree zero along a morphism whose source is connected is surjective. -/
theorem surjective_Hcoh_map_zero_of_isConnected {S T : SSet.{0}} [S.IsConnected]
    (f : S ⟶ T) : Function.Surjective (Hcoh.map R f 0) := by
  intro z
  refine Hcoh.induction_on z fun a ↦ ?_
  let x : S _⦋0⦌ := Classical.arbitrary _
  let b : cocycles T R 0 := (a : Cochain S R 0) x • oneCocycle T R
  refine ⟨Hcoh.mk b, ?_⟩
  rw [Hcoh.map_mk]
  congr 1
  apply Subtype.ext
  change Cochain.pullback f 0 (b : Cochain T R 0) = (a : Cochain S R 0)
  rw [show a = (a : Cochain S R 0) x • oneCocycle S R from
    zeroCocycle_eq_smul_one a x]
  change (a : Cochain S R 0) x •
      Cochain.pullback f 0 (Cochain.one T R) =
    (a : Cochain S R 0) x • Cochain.one S R
  rw [pullback_one]

/-- Pullback in degree zero along a continuous map whose source is path-connected is
surjective. -/
theorem surjective_Hsing_map_zero_of_pathConnected {X Y : TopCat.{0}}
    [PathConnectedSpace X] (f : X ⟶ Y) :
    Function.Surjective (Hsing.map (R := R) f 0) :=
  surjective_Hcoh_map_zero_of_isConnected (R := R) (TopCat.toSSet.map f)

/-- Every degree-zero mod-two cohomology class of a path-connected space is zero or the unit. -/
theorem degreeZeroModTwoClass_eq_zero_or_eq_one
    {X : TopCat.{0}} [PathConnectedSpace X] (x : Hsing 0 X (ZMod 2)) :
    x = 0 ∨ x = Hsing.one X (ZMod 2) := by
  refine Hcoh.induction_on x fun f ↦ ?_
  let S := TopCat.toSSet.obj X
  let σ : S _⦋0⦌ := Classical.arbitrary _
  have hf := zeroCocycle_eq_smul_one f σ
  have hc : (f : Cochain (TopCat.toSSet.obj X) (ZMod 2) 0) σ = 0 ∨
      (f : Cochain (TopCat.toSSet.obj X) (ZMod 2) 0) σ = 1 := by
    exact (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) _
  rcases hc with hc | hc
  · left
    rw [hf, hc, zero_smul]
    rfl
  · right
    rw [hf, hc, one_smul]
    rfl

/-- The degree-zero unit is nonzero on every nonempty space over nontrivial coefficients. -/
theorem Hsing.one_ne_zero
    {X : TopCat.{0}} {R : Type} [CommRing R] [Nontrivial R] [Nonempty X] :
    Hsing.one X R ≠ 0 := by
  intro hzero
  have hmem := (Hcoh.mk_eq_zero_iff
    (oneCocycle (TopCat.toSSet.obj X) R)).mp hzero
  rw [coboundaries_zero, Submodule.mem_bot] at hmem
  let S := TopCat.toSSet.obj X
  let σ : S _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm
    (Classical.choice (inferInstance : Nonempty X))
  have hvalue := congrArg
    (fun f : Cochain (TopCat.toSSet.obj X) R 0 ↦ f σ) hmem
  change (1 : R) = 0 at hvalue
  exact _root_.one_ne_zero hvalue

end Submission
