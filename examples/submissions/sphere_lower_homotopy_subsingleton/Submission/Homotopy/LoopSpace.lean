/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.FibrationLES
import Submission.Homotopy.RelGroup
import Submission.Homotopy.PathFibration
import Submission.ForMathlib.HomotopyGroup.Contractible
import Submission.ForMathlib.HomotopyGroup.Homeomorph

/-!
# The remaining gap in the long exact sequence of a fibration

Everything in `Submission/Homotopy/FibrationLES.lean` is proved as pointed sets. This file adds the
statement that is still missing, namely injectivity of the connecting map

`∂ : π_(k+1)(B, b) → π_k(F, e)`

of a Serre fibration whose total space is weakly contractible.

**Why it is missing.** `∂ = bd ∘ pStar⁻¹`, and `pStar` is a bijection by
`Submission.bijective_pStar`, so the statement is equivalent to injectivity of
`RelHomotopyGroup.bd`. Pointed-set exactness of the long exact sequence of the pair only gives
that `∂` has *trivial kernel* (`Submission.fibDelta_eq_default_iff`), which upgrades to
injectivity as soon as `∂` is a homomorphism of groups. The vendored `WhiteheadTheorem` library
deliberately gives `π_rel` no group structure, so that upgrade is not available yet; it will
follow from the `Group (π_rel (n + 2))` instance being developed in
`Submission/Homotopy/RelGroup.lean`, together with the (easy) fact that `bd` — restriction to the
top face — commutes with concatenation in the first cube coordinate.

Once that lands, `injective_fibDelta_of_subsingleton` below should be discharged and this file
merged into `FibrationLES.lean`. Everything after it is proved outright from that one input, so
this file completes the long exact sequence of a fibration in the group range and derives the
loop-space shift.

## Main statements

* `Submission.injective_bd_of_subsingleton`, `Submission.injective_fibDelta_of_subsingleton`.
* `Submission.bijective_fibDelta_of_subsingleton` — `∂` is bijective when the total space is
  weakly contractible.
* `Submission.nonempty_piSucc_equiv_pi_loopSpace` — `π_(k+1)(X, x₀) ≃ π_k(Ω X, const)`.
-/

noncomputable section

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

/-! ### `π₀` of a path-connected space -/

/-- The zeroth homotopy set of a path-connected space is a singleton. -/
theorem subsingleton_piZero {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] (y : Y) :
    Subsingleton (π_ 0 Y y) := by
  refine ⟨fun a c => Quotient.inductionOn₂ a c fun f g => Quotient.sound ⟨?_⟩⟩
  have hsub : ∀ z : I^ Fin 0, z = default := fun z => Subsingleton.elim _ _
  exact
    { toFun := fun st => (PathConnectedSpace.somePath (f default) (g default)) st.1
      continuous_toFun := (map_continuous _).comp continuous_fst
      map_zero_left := fun z => by rw [hsub z]; simp
      map_one_left := fun z => by rw [hsub z]; simp
      prop' := fun _ z hz => isEmptyElim (⟨z, hz⟩ : ∂I^0) }

/-! ### The gap -/

section Gap

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)} {b : B}
  (e : (⇑p ⁻¹' {b} : Set E))

/-- The boundary map of a pair is injective in the group range when the ambient space is weakly
contractible one degree up. -/
theorem injective_bd_of_subsingleton {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}
    (j : ℕ) (h : Subsingleton (π_ (j + 2) X (a : X))) :
    Function.Injective (RelHomotopyGroup.bd (j + 1) X A a) := by
  have hhom : Function.Injective ⇑(RelHomotopyGroup.bdHom j X A a) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hx' : x ∈ RelHomotopyGroup.bd (j + 1) X A a ⁻¹' {default} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← RelHomotopyGroup.coe_bdHom, hx]
      exact (default_eq_one (N := Fin (j + 1)) (X := (A : Type _)) a).symm
    rw [RelHomotopyGroup.isExactAt_jStar_bd] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hy : y = default := Subsingleton.elim _ _
    rw [hy, (RelHomotopyGroup.jStar_isPointedMap (j + 2) X A a).map_default]
    exact RelHomotopyGroup.one_def.symm
  simpa only [RelHomotopyGroup.coe_bdHom] using hhom

/-- If the total space of a Serre fibration is weakly contractible in degrees `k+1` and `k+2`,
the connecting map `∂ : π_(k+2)(B) → π_(k+1)(F)` is injective. -/
theorem injective_fibDelta_of_subsingleton (hp : IsSerreFibration p) (j : ℕ)
    (h₁ : Subsingleton (π_ (j + 2) E (e : E))) :
    Function.Injective (fibDelta e hp (j + 1)) :=
  (injective_bd_of_subsingleton (X := E) (A := (⇑p ⁻¹' {b})) (a := e) j h₁).comp
    (pStarEquiv e hp (j + 1)).symm.injective

/-- If the total space of a Serre fibration is weakly contractible in degrees `k` and `k + 1`,
the connecting map `∂ : π_(k+1)(B) → π_k(F)` is a bijection. -/
theorem bijective_fibDelta_of_subsingleton (hp : IsSerreFibration p) (j : ℕ)
    (h₁ : Subsingleton (π_ (j + 2) E ↑e)) (h₂ : Subsingleton (π_ (j + 1) E ↑e)) :
    Function.Bijective (fibDelta e hp (j + 1)) :=
  ⟨injective_fibDelta_of_subsingleton e hp j h₁,
    surjective_fibDelta_of_subsingleton e hp (j + 1) h₂⟩

/-- The connecting map of a Serre fibration with weakly contractible total space, as an
equivalence `π_(k+1)(B, b) ≃ π_k(F, e)`. -/
def fibDeltaEquiv (hp : IsSerreFibration p) (j : ℕ)
    (h₁ : Subsingleton (π_ (j + 2) E ↑e)) (h₂ : Subsingleton (π_ (j + 1) E ↑e)) :
    π_ (j + 2) B b ≃ π_ (j + 1) (⇑p ⁻¹' {b}) e :=
  Equiv.ofBijective _ (bijective_fibDelta_of_subsingleton e hp j h₁ h₂)

end Gap

/-! ### The path–loop fibration -/

section PathLoop

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- The constant path, as a point of the fibre of the path fibration over `x₀`. -/
def loopBase : (⇑(ev₁ X x₀) ⁻¹' {x₀} : Set (PathSpace X x₀)) :=
  ⟨PathSpace.const X x₀, rfl⟩

@[simp]
theorem fibreEv₁Homeomorph_loopBase :
    fibreEv₁Homeomorph X x₀ (loopBase x₀) = Path.refl x₀ := rfl

/-- Every homotopy group of the total space of the path fibration is trivial. -/
theorem subsingleton_pi_pathSpace (k : ℕ) (γ : PathSpace X x₀) :
    Subsingleton (π_ k (PathSpace X x₀) γ) := by
  cases k with
  | zero => exact subsingleton_piZero γ
  | succ k => exact subsingleton_homotopyGroup_of_contractible (N := Fin (k + 1)) γ

/-- **The loop space shifts homotopy groups.** For every space `X`, every basepoint `x₀` and
every `k`, the connecting map of the path fibration is a bijection
`π_(k+1)(X, x₀) ≃ π_k(Ω X, const)`. -/
theorem nonempty_piSucc_equiv_pi_loopSpace (k : ℕ) :
    Nonempty (π_ (k + 2) X x₀ ≃ π_ (k + 1) (Path x₀ x₀) (Path.refl x₀)) := by
  refine ⟨(fibDeltaEquiv (loopBase x₀) (isSerreFibration_ev₁ X x₀) k ?_ ?_).trans
    (HomotopyGroup.homeomorphEquivOfEq (N := Fin (k + 1)) (fibreEv₁Homeomorph X x₀) rfl)⟩
  · exact subsingleton_pi_pathSpace x₀ (k + 2) _
  · exact subsingleton_pi_pathSpace x₀ (k + 1) _

end PathLoop

/-! ### The bottom rung: `π₀(Ω X) ≅ π₁(X)`

`Submission.nonempty_piSucc_equiv_pi_loopSpace` shifts homotopy groups from degree `k + 2` down
to degree `k + 1` of the loop space; the connecting-map argument it uses cannot reach degree
zero, where there are no groups.  The degree-zero statement — path components of `Ω X` are
homotopy classes of loops — is instead immediate from the definitions, once a homotopy of loops
is read as a path in the loop space.  That reading is `Submission.loopPathOfHomotopy`, and it is
where the compact-open topology of `Path x x` (`Path.instTopologicalSpace`) gets used. -/

section LoopPathConnected

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- **A homotopy of loops, read as a path in the loop space.**  The topology on `Path x x` is
induced from the compact-open topology on `C(I, X)`, so this is exactly the currying
`Path.continuous_uncurry_iff`. -/
def loopPathOfHomotopy {γ₀ γ₁ : Path x x} (H : γ₀.Homotopy γ₁) : Path γ₀ γ₁ where
  toFun s :=
    { toFun := fun t => H (s, t)
      continuous_toFun := (map_continuous H).comp (continuous_const.prodMk continuous_id)
      source' := H.source s
      target' := H.target s }
  continuous_toFun :=
    Path.continuous_uncurry_iff.mp ((map_continuous H).comp (continuous_fst.prodMk continuous_snd))
  source' := Path.ext (funext fun t => H.apply_zero t)
  target' := Path.ext (funext fun t => H.apply_one t)

@[simp]
theorem loopPathOfHomotopy_apply {γ₀ γ₁ : Path x x} (H : γ₀.Homotopy γ₁) (s t : I) :
    loopPathOfHomotopy H s t = H (s, t) := rfl

/-- Two homotopic loops lie in the same path component of the loop space. -/
theorem joined_of_homotopic {γ₀ γ₁ : Path x x} (h : γ₀.Homotopic γ₁) : Joined γ₀ γ₁ :=
  ⟨loopPathOfHomotopy h.some⟩

/-- **`π₁(X) = 0` implies that the loop space `Ω X` is path connected.**

This is the degree-zero end of the loop-space shift: `π₀(Ω X)` is the set of homotopy classes of
loops at `x`, which is `π₁(X, x)`.  Only the direction needed downstream is proved, and it is
stated for an arbitrary space. -/
theorem pathConnectedSpace_loopSpace (x : X) (h : Subsingleton (π_ 1 X x)) :
    PathConnectedSpace (Path x x) := by
  haveI hs : Subsingleton (Path.Homotopic.Quotient x x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)).symm.subsingleton
  refine ⟨⟨Path.refl x⟩, fun γ₀ γ₁ => ?_⟩
  have heq : (⟦γ₀⟧ : Path.Homotopic.Quotient x x) = ⟦γ₁⟧ := hs.elim _ _
  have hh : γ₀.Homotopic γ₁ := Quotient.exact heq
  exact joined_of_homotopic hh

end LoopPathConnected

end Submission
