/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.LoopSpace

/-!
# The connecting map of a fibration as a group homomorphism

`Submission/Homotopy/FibrationLES.lean` builds the long exact sequence of a Serre fibration as a
sequence of *pointed sets*, with connecting map `∂ = bd ∘ pStar⁻¹`.  For the computation of
homotopy groups one needs `∂` as a *group homomorphism*.

The boundary map of the pair is already a homomorphism (`RelHomotopyGroup.bdHom`), so the only
missing ingredient is that `pStar : π_rel (n+2) (E, F) → π_(n+2) B` is one.  That is immediate:
concatenation of relative generalized loops in the free direction `i.castSucc` is defined by the
same pointwise formula as concatenation of absolute generalized loops, and postcomposition with
`p` does not see the formula.

## Main declarations

* `Submission.pGenLoop_transAt` — postcomposition with `p` commutes with concatenation;
* `Submission.pStarHom`, `Submission.pStarMulEquiv` — `pStar` as a homomorphism, and as an
  isomorphism when `p` is a Serre fibration;
* `Submission.fibDeltaHom`, `Submission.fibDeltaMulEquiv` — the connecting map as a homomorphism,
  and as an isomorphism when the total space is weakly contractible.
-/

noncomputable section

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)} {b : B}
  (e : (⇑p ⁻¹' {b} : Set E))

/-- Postcomposition with `p` turns concatenation of relative generalized loops in the free
direction `i.castSucc` into concatenation of generalized loops in the same direction. -/
theorem pGenLoop_transAt {n : ℕ} (i : Fin n) (f g : RelGenLoop (n + 1) E (⇑p ⁻¹' {b}) e) :
    pGenLoop e (RelGenLoop.transAt i f g) =
      GenLoop.transAt i.castSucc (pGenLoop e f) (pGenLoop e g) := by
  refine _root_.GenLoop.ext _ _ fun y => ?_
  show p ((RelGenLoop.transAt i f g).val y) = _
  rw [RelGenLoop.transAt_apply, GenLoop.transAt_apply]
  split_ifs <;> rfl

/-- **`pStar` is a group homomorphism** in degrees at least two. -/
def pStarHom (n : ℕ) : π_rel (n + 2) E (⇑p ⁻¹' {b}) e →* π_ (n + 2) B b where
  toFun := pStar e (n + 2)
  map_one' := by
    have h1 : (1 : π_rel (n + 2) E (⇑p ⁻¹' {b}) e) = default := RelHomotopyGroup.one_def
    rw [h1, pStar_default, default_eq_one]
  map_mul' x y := by
    obtain ⟨f, rfl⟩ := Quotient.exists_rep x
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    rw [RelHomotopyGroup.mul_mk (0 : Fin (n + 1)) f g, pStar_mk, pStar_mk, pStar_mk,
      pGenLoop_transAt, ← HomotopyGroup.mul_mk (0 : Fin (n + 1)).castSucc]

@[simp]
theorem coe_pStarHom (n : ℕ) : ⇑(pStarHom e n) = pStar e (n + 2) := rfl

/-- For a Serre fibration, `pStar` is an isomorphism of groups in degrees at least two. -/
def pStarMulEquiv (hp : IsSerreFibration p) (n : ℕ) :
    π_rel (n + 2) E (⇑p ⁻¹' {b}) e ≃* π_ (n + 2) B b :=
  MulEquiv.ofBijective (pStarHom e n) (bijective_pStar e hp (n + 1))

/-- **The connecting map of the long exact sequence of a fibration, as a group homomorphism.** -/
def fibDeltaHom (hp : IsSerreFibration p) (n : ℕ) :
    π_ (n + 2) B b →* π_ (n + 1) (⇑p ⁻¹' {b}) e :=
  (RelHomotopyGroup.bdHom n E (⇑p ⁻¹' {b}) e).comp (pStarMulEquiv e hp n).symm.toMonoidHom

@[simp]
theorem coe_fibDeltaHom (hp : IsSerreFibration p) (n : ℕ) :
    ⇑(fibDeltaHom e hp n) = fibDelta e hp (n + 1) :=
  rfl

/-- **The connecting isomorphism.**  If the total space of a Serre fibration is weakly
contractible in degrees `n + 1` and `n + 2`, the connecting map is an isomorphism of groups
`π_(n+2)(B) ≃* π_(n+1)(F)`. -/
def fibDeltaMulEquiv (hp : IsSerreFibration p) (n : ℕ)
    (h₁ : Subsingleton (π_ (n + 2) E ↑e)) (h₂ : Subsingleton (π_ (n + 1) E ↑e)) :
    π_ (n + 2) B b ≃* π_ (n + 1) (⇑p ⁻¹' {b}) e :=
  MulEquiv.ofBijective (fibDeltaHom e hp n) <| by
    rw [coe_fibDeltaHom]
    exact bijective_fibDelta_of_subsingleton e hp n h₁ h₂


/-! ### Reading off the vanishing of a homotopy group of the total space -/

section Vanishing

/-- If both the fibre and the base have trivial `π_(k+1)`, so does the total space. -/
theorem subsingleton_pi_total_of_subsingleton_base (hp : IsSerreFibration p) (k : ℕ)
    (hF : Subsingleton (π_ (k + 1) (⇑p ⁻¹' {b}) e)) (hB : Subsingleton (π_ (k + 1) B b)) :
    Subsingleton (π_ (k + 1) E ↑e) := by
  have key : ∀ z : π_ (k + 1) E ↑e, z = default := by
    intro z
    have hz : z ∈ pStarAbs e (k + 1) ⁻¹' {default} := Subsingleton.elim _ _
    rw [isExactAt_iStarFib_pStarAbs e hp k] at hz
    obtain ⟨y, rfl⟩ := hz
    rw [Subsingleton.elim y default, iStarFib_default]
  exact ⟨fun a c => by rw [key a, key c]⟩

/-- If the fibre has trivial `π_(k+1)` and the connecting map out of `π_(k+1)(B)` is injective,
then `π_(k+1)` of the total space is trivial. -/
theorem subsingleton_pi_total_of_injective_fibDelta (hp : IsSerreFibration p) (k : ℕ)
    (hF : Subsingleton (π_ (k + 1) (⇑p ⁻¹' {b}) e))
    (hδ : Function.Injective (fibDelta e hp k)) :
    Subsingleton (π_ (k + 1) E ↑e) := by
  have key : ∀ z : π_ (k + 1) E ↑e, z = default := by
    intro z
    have hmem : pStarAbs e (k + 1) z ∈ fibDelta e hp k ⁻¹' {default} := by
      rw [isExactAt_pStarAbs_fibDelta e hp k]
      exact ⟨z, rfl⟩
    have h0 : pStarAbs e (k + 1) z = default :=
      hδ ((Set.mem_preimage.mp hmem).trans (fibDelta_default e hp k).symm)
    have hz : z ∈ pStarAbs e (k + 1) ⁻¹' {default} := h0
    rw [isExactAt_iStarFib_pStarAbs e hp k] at hz
    obtain ⟨y, rfl⟩ := hz
    rw [Subsingleton.elim y default, iStarFib_default]
  exact ⟨fun a c => by rw [key a, key c]⟩

/-- If the base has trivial `π_(k+1)` and the connecting map into `π_(k+1)(F)` is surjective,
then `π_(k+1)` of the total space is trivial. -/
theorem subsingleton_pi_total_of_surjective_fibDelta (hp : IsSerreFibration p) (k : ℕ)
    (hB : Subsingleton (π_ (k + 1) B b))
    (hδ : Function.Surjective (fibDelta e hp (k + 1))) :
    Subsingleton (π_ (k + 1) E ↑e) := by
  have hi : ∀ y : π_ (k + 1) (⇑p ⁻¹' {b}) e, iStarFib e (k + 1) y = default := by
    intro y
    have hy : y ∈ iStarFib e (k + 1) ⁻¹' {default} := by
      rw [isExactAt_fibDelta_iStarFib e hp (k + 1)]
      exact hδ y
    exact hy
  have key : ∀ z : π_ (k + 1) E ↑e, z = default := by
    intro z
    have hz : z ∈ pStarAbs e (k + 1) ⁻¹' {default} := Subsingleton.elim _ _
    rw [isExactAt_iStarFib_pStarAbs e hp k] at hz
    obtain ⟨y, rfl⟩ := hz
    exact hi y
  exact ⟨fun a c => by rw [key a, key c]⟩

end Vanishing

end Submission
