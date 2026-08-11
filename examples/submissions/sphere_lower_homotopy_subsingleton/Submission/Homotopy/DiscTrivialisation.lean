/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.ContractionData
import Submission.Homotopy.PathFibration

/-!
# Fibre-homotopy trivialisation of a path fibration over a contractible piece of the base

Let `(X, x₀)` be a based space and `p = ev₁ : PathSpace X x₀ → X` the path fibration.
If `D ⊆ X` carries `ContractionData`, i.e. a continuous family of paths `c_b` in `D` from a base
point `b₀` to each `b ∈ D`, then `p⁻¹(D)` is fibre-homotopy trivial over `D`:

* `trivialise : F × D → p⁻¹(D)`, `(γ, b) ↦ γ ⬝ c_b`;
* `untrivialise : p⁻¹(D) → F × D`, `δ ↦ (δ ⬝ c_{p δ}⁻¹, p δ)`;

and the two composites are homotopic to the identity *through maps over `D`*.

## Implementation

Everything is done for a general **based family of paths** `w : C(T × I, X)` with `w (t, 0) = x₁`
(`Submission.BasedPathFamily`), whose total space is the pullback
`Pullback w.endpt (ev₁ X x₀)`. Both composites of the trivialisation have the shape
`(α ⬝ β) ⬝ β⁻¹`, so a single explicit homotopy `Submission.cancelAux` does all the work:
with `a u = (1 + 3u)/4` and `m u = (1 + u)/2`,
```
H u t = α (t / a u)             for t ≤ a u
      = β (4 (t - a u))         for a u ≤ t ≤ m u
      = β (2 (1 - t))           for m u ≤ t
```
is a homotopy from `(α ⬝ β) ⬝ β⁻¹` (at `u = 0`) to `α` (at `u = 1`) which is stationary at both
end points of the interval — in particular it never moves the end point of the path, which is
exactly the statement that the homotopy lies over the base.

## Main definitions and results

* `Submission.BasedPathFamily.trivialise`, `Submission.BasedPathFamily.untrivialise`;
* `Submission.BasedPathFamily.homotopyRight`, `Submission.BasedPathFamily.homotopyLeft` — the two
  homotopies, together with `..._snd` / `..._fst` saying that they lie over the base;
* `Submission.BasedPathFamily.homotopyEquiv` — the resulting homotopy equivalence;
* `Submission.trivialiseOver`, `Submission.untrivialiseOver`,
  `Submission.homotopyEquivOverDisc` — the version for `D ⊆ X` with `ContractionData`;
* `Submission.trivialiseOver_restrict` — the trivialisation over `D` restricts to `D' ⊆ D`.
-/

namespace Submission

open unitInterval

universe u v w

/-! ### Reparametrisation helpers -/

theorem coe_projI_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : ((projI x : I) : ℝ) = x :=
  congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨h0, h1⟩)

/-! ### Families of paths -/

section Family

variable {X : Type u} [TopologicalSpace X] {P : Type v} [TopologicalSpace P]
  {Q : Type w} [TopologicalSpace Q]

/-- Concatenation of two continuous families of paths: the first family is traversed on `[0, 1/2]`
and the second on `[1/2, 1]`. The hypothesis `h` guarantees continuity. -/
noncomputable def fconcat (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) : C(P × I, X) where
  toFun z :=
    if (z.2 : ℝ) ≤ 1 / 2 then α (z.1, projI (2 * (z.2 : ℝ)))
    else β (z.1, projI (2 * (z.2 : ℝ) - 1))
  continuous_toFun := by
    have hs : Continuous fun z : P × I => (z.2 : ℝ) := continuous_subtype_val.comp continuous_snd
    refine Continuous.if_le ?_ ?_ hs continuous_const ?_
    · exact α.continuous.comp
        (continuous_fst.prodMk (projI.continuous.comp (continuous_const.mul hs)))
    · exact β.continuous.comp (continuous_fst.prodMk
        (projI.continuous.comp ((continuous_const.mul hs).sub continuous_const)))
    · intro z hz
      rw [hz, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, projI_one, projI_zero]
      exact h z.1

theorem fconcat_apply (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (p : P) (t : I) :
    fconcat α β h (p, t) =
      if (t : ℝ) ≤ 1 / 2 then α (p, projI (2 * (t : ℝ))) else β (p, projI (2 * (t : ℝ) - 1)) :=
  rfl

@[simp] theorem fconcat_zero (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (p : P) :
    fconcat α β h (p, 0) = α (p, 0) := by
  rw [fconcat_apply, Set.Icc.coe_zero, if_pos (by norm_num), mul_zero, projI_zero]

@[simp] theorem fconcat_one (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (p : P) :
    fconcat α β h (p, 1) = β (p, 1) := by
  rw [fconcat_apply, Set.Icc.coe_one, if_neg (by norm_num),
    show (2 : ℝ) * 1 - 1 = 1 by norm_num, projI_one]

/-- Reversal of a continuous family of paths. -/
def fsymm (β : C(P × I, X)) : C(P × I, X) where
  toFun z := β (z.1, σ z.2)
  continuous_toFun :=
    β.continuous.comp (continuous_fst.prodMk (continuous_symm.comp continuous_snd))

@[simp] theorem fsymm_apply (β : C(P × I, X)) (p : P) (t : I) : fsymm β (p, t) = β (p, σ t) := rfl

@[simp] theorem fsymm_fsymm (β : C(P × I, X)) : fsymm (fsymm β) = β := by
  ext ⟨p, t⟩
  simp

theorem fconcat_one_eq_fsymm_zero (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (p : P) :
    fconcat α β h (p, 1) = fsymm β (p, 0) := by simp

/-- Concatenation only depends on the values of the two families along the given parameter. -/
theorem fconcat_congr {α β : C(P × I, X)} {h : ∀ p, α (p, 1) = β (p, 0)} {α' β' : C(Q × I, X)}
    {h' : ∀ q, α' (q, 1) = β' (q, 0)} {p : P} {q : Q} (hα : ∀ s, α (p, s) = α' (q, s))
    (hβ : ∀ s, β (p, s) = β' (q, s)) (t : I) :
    fconcat α β h (p, t) = fconcat α' β' h' (q, t) := by
  rw [fconcat_apply, fconcat_apply]
  split
  · exact hα _
  · exact hβ _

/-! ### The cancellation homotopy `(α ⬝ β) ⬝ β⁻¹ ≃ α` -/

/-- The explicit homotopy from `(α ⬝ β) ⬝ β⁻¹` (at time `u = 0`) to `α` (at time `u = 1`). -/
noncomputable def cancelAux (α β : C(P × I, X)) (z : (I × P) × I) : X :=
  if (z.2 : ℝ) ≤ (1 + 3 * (z.1.1 : ℝ)) / 4 then
    α (z.1.2, projI ((z.2 : ℝ) / ((1 + 3 * (z.1.1 : ℝ)) / 4)))
  else if (z.2 : ℝ) ≤ (1 + (z.1.1 : ℝ)) / 2 then
    β (z.1.2, projI (4 * ((z.2 : ℝ) - (1 + 3 * (z.1.1 : ℝ)) / 4)))
  else β (z.1.2, projI (2 * (1 - (z.2 : ℝ))))

theorem continuous_cancelAux (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) :
    Continuous (cancelAux α β) := by
  have hu : Continuous fun z : (I × P) × I => ((z.1.1 : I) : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have ht : Continuous fun z : (I × P) × I => ((z.2 : I) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous fun z : (I × P) × I => z.1.2 := continuous_snd.comp continuous_fst
  have ha : Continuous fun z : (I × P) × I => (1 + 3 * ((z.1.1 : I) : ℝ)) / 4 :=
    (continuous_const.add (continuous_const.mul hu)).div_const 4
  have hane : ∀ z : (I × P) × I, (1 + 3 * ((z.1.1 : I) : ℝ)) / 4 ≠ 0 := by
    intro z
    have := z.1.1.2.1
    positivity
  have hm : Continuous fun z : (I × P) × I => (1 + ((z.1.1 : I) : ℝ)) / 2 :=
    (continuous_const.add hu).div_const 2
  refine Continuous.if_le ?_ (Continuous.if_le ?_ ?_ ht hm ?_) ht ha ?_
  · exact α.continuous.comp (hp.prodMk (projI.continuous.comp (ht.div ha hane)))
  · exact β.continuous.comp
      (hp.prodMk (projI.continuous.comp (continuous_const.mul (ht.sub ha))))
  · exact β.continuous.comp
      (hp.prodMk (projI.continuous.comp (continuous_const.mul (continuous_const.sub ht))))
  · intro z hz
    have : 4 * (((z.2 : I) : ℝ) - (1 + 3 * ((z.1.1 : I) : ℝ)) / 4) = 2 * (1 - ((z.2 : I) : ℝ)) := by
      rw [hz]; ring
    rw [this]
  · intro z hz
    have hu0 : (0 : ℝ) ≤ ((z.1.1 : I) : ℝ) := z.1.1.2.1
    have hu1 : ((z.1.1 : I) : ℝ) ≤ 1 := z.1.1.2.2
    rw [if_pos (by rw [hz]; linarith)]
    have h1 : ((z.2 : I) : ℝ) / ((1 + 3 * ((z.1.1 : I) : ℝ)) / 4) = 1 := by
      rw [hz]; exact div_self (hane z)
    have h2 : 4 * (((z.2 : I) : ℝ) - (1 + 3 * ((z.1.1 : I) : ℝ)) / 4) = 0 := by rw [hz]; ring
    rw [h1, h2, projI_one, projI_zero]
    exact h z.1.2

/-- The cancellation homotopy, bundled as a continuous map. -/
noncomputable def cancelHomotopyMap (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) :
    C((I × P) × I, X) :=
  ⟨cancelAux α β, continuous_cancelAux α β h⟩

@[simp] theorem cancelHomotopyMap_apply (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0))
    (z : (I × P) × I) : cancelHomotopyMap α β h z = cancelAux α β z := rfl

/-- The cancellation homotopy is stationary at the start of the interval. -/
theorem cancelAux_zero_right (α β : C(P × I, X)) (u : I) (p : P) :
    cancelAux α β ((u, p), 0) = α (p, 0) := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
  rw [cancelAux, Set.Icc.coe_zero, if_pos (by positivity), zero_div, projI_zero]

/-- The cancellation homotopy is stationary at the end of the interval. -/
theorem cancelAux_one_right (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (u : I) (p : P) :
    cancelAux α β ((u, p), 1) = α (p, 1) := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  rw [cancelAux, Set.Icc.coe_one]
  by_cases hA : (1 : ℝ) ≤ (1 + 3 * (u : ℝ)) / 4
  · have hu : (u : ℝ) = 1 := by linarith
    rw [if_pos hA, hu]
    norm_num
  · rw [if_neg hA, if_neg (by intro hcon; apply hA; linarith), sub_self, mul_zero, projI_zero]
    exact (h p).symm

/-- At time `u = 1` the cancellation homotopy is the family `α` itself. -/
theorem cancelAux_one (α β : C(P × I, X)) (p : P) (t : I) :
    cancelAux α β ((1, p), t) = α (p, t) := by
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [cancelAux]
  simp only [Set.Icc.coe_one]
  rw [if_pos (by norm_num; linarith), show (1 + 3 * (1 : ℝ)) / 4 = 1 by norm_num, div_one,
    projI_coe]

/-- At time `u = 0` the cancellation homotopy is the triple concatenation `(α ⬝ β) ⬝ β⁻¹`. -/
theorem cancelAux_zero (α β : C(P × I, X)) (h : ∀ p, α (p, 1) = β (p, 0)) (p : P) (t : I) :
    cancelAux α β ((0, p), t) =
      fconcat (fconcat α β h) (fsymm β) (fconcat_one_eq_fsymm_zero α β h) (p, t) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rw [cancelAux]
  simp only [Set.Icc.coe_zero, mul_zero, add_zero]
  rw [fconcat_apply]
  by_cases hA : (t : ℝ) ≤ 1 / 4
  · rw [if_pos (by norm_num; linarith), if_pos (by linarith), fconcat_apply,
      coe_projI_of_mem (by linarith) (by linarith), if_pos (by linarith),
      show (t : ℝ) / (1 / 4) = 2 * (2 * (t : ℝ)) by ring]
  · rw [not_le] at hA
    rw [if_neg (not_le.mpr (by linarith))]
    by_cases hB : (t : ℝ) ≤ 1 / 2
    · rw [if_pos (by norm_num; linarith), if_pos hB, fconcat_apply,
        coe_projI_of_mem (by linarith) (by linarith), if_neg (not_le.mpr (by linarith)),
        show 4 * ((t : ℝ) - 1 / 4) = 2 * (2 * (t : ℝ)) - 1 by ring]
    · rw [not_le] at hB
      rw [if_neg (not_le.mpr (by norm_num; linarith)), if_neg (not_le.mpr (by linarith)),
        fsymm_apply]
      refine congrArg _ (Prod.ext rfl (Subtype.ext ?_))
      rw [coe_symm_eq, coe_projI_of_mem (by linarith) (by linarith),
        coe_projI_of_mem (by linarith) (by linarith)]
      ring

end Family

/-! ### Based families of paths and their total spaces -/

/-- A continuous family of paths in `X` indexed by `T`, all issuing from the point `x₁`. -/
structure BasedPathFamily (T : Type v) (X : Type u) [TopologicalSpace T] [TopologicalSpace X]
    (x₁ : X) where
  /-- The family of paths, as a single continuous map. -/
  curve : C(T × I, X)
  /-- Every path in the family starts at `x₁`. -/
  curve_zero : ∀ t : T, curve (t, 0) = x₁

/-- The fibre of the path fibration `ev₁ : PathSpace X x₀ → X` over the point `x₁`. -/
def PathFibre (X : Type u) [TopologicalSpace X] (x₀ x₁ : X) : Type u :=
  {γ : PathSpace X x₀ // ev₁ X x₀ γ = x₁}

instance (X : Type u) [TopologicalSpace X] (x₀ x₁ : X) : TopologicalSpace (PathFibre X x₀ x₁) :=
  inferInstanceAs (TopologicalSpace {γ : PathSpace X x₀ // ev₁ X x₀ γ = x₁})

namespace PathFibre

variable {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}

/-- The underlying continuous map `I → X` of a point of the fibre. -/
theorem continuous_toContinuousMap :
    Continuous fun γ : PathFibre X x₀ x₁ => (γ.1.1 : C(I, X)) :=
  continuous_subtype_val.comp continuous_subtype_val

@[simp] theorem source (γ : PathFibre X x₀ x₁) : γ.1.1 0 = x₀ := γ.1.2

@[simp] theorem target (γ : PathFibre X x₀ x₁) : γ.1.1 1 = x₁ := γ.2

end PathFibre

namespace BasedPathFamily

variable {X : Type u} [TopologicalSpace X] {T : Type v} [TopologicalSpace T] {x₁ : X}

/-- The endpoint map of a based family of paths. -/
def endpt (w : BasedPathFamily T X x₁) : C(T, X) :=
  ⟨fun t => w.curve (t, 1), w.curve.continuous.comp (continuous_id.prodMk continuous_const)⟩

@[simp] theorem endpt_apply (w : BasedPathFamily T X x₁) (t : T) : w.endpt t = w.curve (t, 1) :=
  rfl


/-! #### The two legs of the trivialisation -/

/-- The family `(γ, t) ↦ γ`, viewed as a family of paths indexed by `PathFibre X x₀ x₁ × T`. -/
def legFibre (x₀ x₁ : X) (T : Type v) [TopologicalSpace T] :
    C((PathFibre X x₀ x₁ × T) × I, X) where
  toFun z := z.1.1.1.1 z.2
  continuous_toFun :=
    Continuous.eval (PathFibre.continuous_toContinuousMap.comp (continuous_fst.comp continuous_fst))
      continuous_snd

@[simp] theorem legFibre_apply (x₀ x₁ : X) (T : Type v) [TopologicalSpace T]
    (p : PathFibre X x₀ x₁ × T) (t : I) : legFibre x₀ x₁ T (p, t) = p.1.1.1 t := rfl

variable (w : BasedPathFamily T X x₁) (x₀ : X)

/-- The part of the path space of `(X, x₀)` lying over the family `w`: pairs `(t, δ)` with `δ` a
path from `x₀` to the end point of `w t`. -/
abbrev Total : Type max u v := Pullback w.endpt (ev₁ X x₀)

/-- The projection of the total space to the index space. -/
def proj : C(Total w x₀, T) := Pullback.fst _ _

@[simp] theorem proj_apply (δ : Total w x₀) : proj w x₀ δ = δ.1.1 := rfl

/-- The family `(γ, t) ↦ w t`, viewed as a family of paths indexed by `PathFibre X x₀ x₁ × T`. -/
def legCurve : C((PathFibre X x₀ x₁ × T) × I, X) :=
  w.curve.comp ⟨fun z => (z.1.2, z.2), (continuous_snd.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem legCurve_apply (p : PathFibre X x₀ x₁ × T) (t : I) :
    legCurve w x₀ (p, t) = w.curve (p.2, t) := rfl

theorem legFibre_one_eq_legCurve_zero (p : PathFibre X x₀ x₁ × T) :
    legFibre x₀ x₁ T (p, 1) = legCurve w x₀ (p, 0) := by
  rw [legFibre_apply, legCurve_apply, w.curve_zero, PathFibre.target]

/-- The family `δ ↦ δ` of paths indexed by the total space. -/
def legTotal : C(Total w x₀ × I, X) where
  toFun z := z.1.1.2.1 z.2
  continuous_toFun := Continuous.eval (continuous_subtype_val.comp
    (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))) continuous_snd

@[simp] theorem legTotal_apply (δ : Total w x₀) (t : I) :
    legTotal w x₀ (δ, t) = δ.1.2.1 t := rfl

/-- The family `δ ↦ w (proj δ)` of paths indexed by the total space. -/
def legBase : C(Total w x₀ × I, X) :=
  w.curve.comp ⟨fun z => (z.1.1.1, z.2),
    (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd⟩

@[simp] theorem legBase_apply (δ : Total w x₀) (t : I) :
    legBase w x₀ (δ, t) = w.curve (δ.1.1, t) := rfl

theorem legTotal_one_eq_fsymm_legBase_zero (δ : Total w x₀) :
    legTotal w x₀ (δ, 1) = fsymm (legBase w x₀) (δ, 0) := by
  rw [fsymm_apply, symm_zero, legBase_apply]
  exact δ.2.symm

/-! #### The trivialisation and its inverse -/

/-- The family of paths `(γ, t) ↦ γ ⬝ w t` underlying the trivialisation. -/
noncomputable def trivialiseCurve : C((PathFibre X x₀ x₁ × T) × I, X) :=
  fconcat (legFibre x₀ x₁ T) (legCurve w x₀) (legFibre_one_eq_legCurve_zero w x₀)

theorem trivialiseCurve_zero (p : PathFibre X x₀ x₁ × T) : trivialiseCurve w x₀ (p, 0) = x₀ := by
  rw [trivialiseCurve, fconcat_zero, legFibre_apply]
  exact PathFibre.source p.1

theorem trivialiseCurve_one (p : PathFibre X x₀ x₁ × T) :
    trivialiseCurve w x₀ (p, 1) = w.endpt p.2 := by
  rw [trivialiseCurve, fconcat_one, legCurve_apply, endpt_apply]

/-- **The trivialisation** `F × T → p⁻¹(T)`, `(γ, t) ↦ γ ⬝ w t`. -/
noncomputable def trivialise : C(PathFibre X x₀ x₁ × T, Total w x₀) where
  toFun p :=
    ⟨(p.2, ⟨ContinuousMap.curry (trivialiseCurve w x₀) p, trivialiseCurve_zero w x₀ p⟩),
      (trivialiseCurve_one w x₀ p).symm⟩
  continuous_toFun := (continuous_snd.prodMk
    ((ContinuousMap.curry (trivialiseCurve w x₀)).continuous.subtype_mk _)).subtype_mk _

@[simp] theorem trivialise_fst (p : PathFibre X x₀ x₁ × T) : (trivialise w x₀ p).1.1 = p.2 := rfl

@[simp] theorem trivialise_val (p : PathFibre X x₀ x₁ × T) (t : I) :
    (trivialise w x₀ p).1.2.1 t = trivialiseCurve w x₀ (p, t) := rfl

@[simp] theorem proj_trivialise (p : PathFibre X x₀ x₁ × T) :
    proj w x₀ (trivialise w x₀ p) = p.2 := rfl

/-- The family of paths `δ ↦ δ ⬝ (w (proj δ))⁻¹` underlying the inverse trivialisation. -/
noncomputable def untrivialiseCurve : C(Total w x₀ × I, X) :=
  fconcat (legTotal w x₀) (fsymm (legBase w x₀)) (legTotal_one_eq_fsymm_legBase_zero w x₀)

theorem untrivialiseCurve_zero (δ : Total w x₀) : untrivialiseCurve w x₀ (δ, 0) = x₀ := by
  rw [untrivialiseCurve, fconcat_zero, legTotal_apply]
  exact δ.1.2.2

theorem untrivialiseCurve_one (δ : Total w x₀) : untrivialiseCurve w x₀ (δ, 1) = x₁ := by
  rw [untrivialiseCurve, fconcat_one, fsymm_apply, symm_one, legBase_apply]
  exact w.curve_zero _

/-- **The inverse trivialisation** `p⁻¹(T) → F × T`, `δ ↦ (δ ⬝ (w (proj δ))⁻¹, proj δ)`. -/
noncomputable def untrivialise : C(Total w x₀, PathFibre X x₀ x₁ × T) where
  toFun δ :=
    (⟨⟨ContinuousMap.curry (untrivialiseCurve w x₀) δ, untrivialiseCurve_zero w x₀ δ⟩,
      untrivialiseCurve_one w x₀ δ⟩, δ.1.1)
  continuous_toFun :=
    (((ContinuousMap.curry (untrivialiseCurve w x₀)).continuous.subtype_mk _).subtype_mk _).prodMk
      (continuous_fst.comp continuous_subtype_val)

@[simp] theorem untrivialise_snd (δ : Total w x₀) : (untrivialise w x₀ δ).2 = proj w x₀ δ := rfl

@[simp] theorem untrivialise_val (δ : Total w x₀) (t : I) :
    (untrivialise w x₀ δ).1.1.1 t = untrivialiseCurve w x₀ (δ, t) := rfl

/-! #### The two homotopies -/

theorem cancelRight_zero (u : I) (p : PathFibre X x₀ x₁ × T) :
    cancelAux (legFibre x₀ x₁ T) (legCurve w x₀) ((u, p), 0) = x₀ := by
  rw [cancelAux_zero_right, legFibre_apply]
  exact PathFibre.source p.1

theorem cancelRight_one (u : I) (p : PathFibre X x₀ x₁ × T) :
    cancelAux (legFibre x₀ x₁ T) (legCurve w x₀) ((u, p), 1) = x₁ := by
  rw [cancelAux_one_right _ _ (legFibre_one_eq_legCurve_zero w x₀), legFibre_apply]
  exact PathFibre.target p.1

/-- The homotopy `untrivialise ∘ trivialise ≃ id`, as a map. -/
noncomputable def homotopyRightMap :
    C(I × (PathFibre X x₀ x₁ × T), PathFibre X x₀ x₁ × T) where
  toFun z :=
    (⟨⟨ContinuousMap.curry (cancelHomotopyMap (legFibre x₀ x₁ T) (legCurve w x₀)
        (legFibre_one_eq_legCurve_zero w x₀)) z, cancelRight_zero w x₀ z.1 z.2⟩,
      cancelRight_one w x₀ z.1 z.2⟩, z.2.2)
  continuous_toFun :=
    (((ContinuousMap.curry (cancelHomotopyMap (legFibre x₀ x₁ T) (legCurve w x₀)
      (legFibre_one_eq_legCurve_zero w x₀))).continuous.subtype_mk _).subtype_mk _).prodMk
      (continuous_snd.comp continuous_snd)

@[simp] theorem homotopyRightMap_snd (z : I × (PathFibre X x₀ x₁ × T)) :
    (homotopyRightMap w x₀ z).2 = z.2.2 := rfl

theorem homotopyRightMap_zero (p : PathFibre X x₀ x₁ × T) :
    homotopyRightMap w x₀ (0, p) = untrivialise w x₀ (trivialise w x₀ p) := by
  refine Prod.ext (Subtype.ext (Subtype.ext (ContinuousMap.ext fun t => ?_))) rfl
  show cancelAux (legFibre x₀ x₁ T) (legCurve w x₀) (((0 : I), p), t) =
    untrivialiseCurve w x₀ (trivialise w x₀ p, t)
  rw [cancelAux_zero _ _ (legFibre_one_eq_legCurve_zero w x₀), untrivialiseCurve]
  apply fconcat_congr
  · intro s; rfl
  · intro s; rfl

theorem homotopyRightMap_one (p : PathFibre X x₀ x₁ × T) : homotopyRightMap w x₀ (1, p) = p := by
  refine Prod.ext (Subtype.ext (Subtype.ext (ContinuousMap.ext fun t => ?_))) rfl
  show cancelAux (legFibre x₀ x₁ T) (legCurve w x₀) (((1 : I), p), t) = p.1.1.1 t
  rw [cancelAux_one, legFibre_apply]

/-- `untrivialise ∘ trivialise` is homotopic to the identity, through maps over the base. -/
noncomputable def homotopyRight : ContinuousMap.Homotopy
    ((untrivialise w x₀).comp (trivialise w x₀)) (ContinuousMap.id (PathFibre X x₀ x₁ × T)) where
  toContinuousMap := homotopyRightMap w x₀
  map_zero_left := homotopyRightMap_zero w x₀
  map_one_left := homotopyRightMap_one w x₀

/-- The homotopy `untrivialise ∘ trivialise ≃ id` does not move the base coordinate. -/
@[simp] theorem homotopyRight_snd (z : I × (PathFibre X x₀ x₁ × T)) :
    (homotopyRight w x₀ z).2 = z.2.2 := rfl

theorem cancelLeft_zero (u : I) (δ : Total w x₀) :
    cancelAux (legTotal w x₀) (fsymm (legBase w x₀)) ((u, δ), 0) = x₀ := by
  rw [cancelAux_zero_right, legTotal_apply]
  exact δ.1.2.2

theorem cancelLeft_one (u : I) (δ : Total w x₀) :
    cancelAux (legTotal w x₀) (fsymm (legBase w x₀)) ((u, δ), 1) = w.endpt δ.1.1 := by
  rw [cancelAux_one_right _ _ (legTotal_one_eq_fsymm_legBase_zero w x₀), legTotal_apply]
  exact δ.2.symm

/-- The homotopy `trivialise ∘ untrivialise ≃ id`, as a map. -/
noncomputable def homotopyLeftMap : C(I × Total w x₀, Total w x₀) where
  toFun z :=
    ⟨(z.2.1.1, ⟨ContinuousMap.curry (cancelHomotopyMap (legTotal w x₀) (fsymm (legBase w x₀))
        (legTotal_one_eq_fsymm_legBase_zero w x₀)) z, cancelLeft_zero w x₀ z.1 z.2⟩),
      (cancelLeft_one w x₀ z.1 z.2).symm⟩
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      ((ContinuousMap.curry (cancelHomotopyMap (legTotal w x₀) (fsymm (legBase w x₀))
        (legTotal_one_eq_fsymm_legBase_zero w x₀))).continuous.subtype_mk _)).subtype_mk _

@[simp] theorem homotopyLeftMap_fst (z : I × Total w x₀) :
    (homotopyLeftMap w x₀ z).1.1 = z.2.1.1 := rfl

theorem homotopyLeftMap_zero (δ : Total w x₀) :
    homotopyLeftMap w x₀ (0, δ) = trivialise w x₀ (untrivialise w x₀ δ) := by
  refine Subtype.ext (Prod.ext rfl (Subtype.ext (ContinuousMap.ext fun t => ?_)))
  show cancelAux (legTotal w x₀) (fsymm (legBase w x₀)) (((0 : I), δ), t) =
    trivialiseCurve w x₀ (untrivialise w x₀ δ, t)
  rw [cancelAux_zero _ _ (legTotal_one_eq_fsymm_legBase_zero w x₀), trivialiseCurve]
  apply fconcat_congr
  · intro s; rfl
  · intro s
    simp only [fsymm_apply, symm_symm, legBase_apply, legCurve_apply]
    rfl

theorem homotopyLeftMap_one (δ : Total w x₀) : homotopyLeftMap w x₀ (1, δ) = δ := by
  refine Subtype.ext (Prod.ext rfl (Subtype.ext (ContinuousMap.ext fun t => ?_)))
  show cancelAux (legTotal w x₀) (fsymm (legBase w x₀)) (((1 : I), δ), t) = δ.1.2.1 t
  rw [cancelAux_one, legTotal_apply]

/-- `trivialise ∘ untrivialise` is homotopic to the identity, through maps over the base. -/
noncomputable def homotopyLeft : ContinuousMap.Homotopy
    ((trivialise w x₀).comp (untrivialise w x₀)) (ContinuousMap.id (Total w x₀)) where
  toContinuousMap := homotopyLeftMap w x₀
  map_zero_left := homotopyLeftMap_zero w x₀
  map_one_left := homotopyLeftMap_one w x₀

/-- The homotopy `trivialise ∘ untrivialise ≃ id` does not move the base coordinate. -/
@[simp] theorem homotopyLeft_proj (z : I × Total w x₀) :
    proj w x₀ (homotopyLeft w x₀ z) = proj w x₀ z.2 := rfl

/-- **The path fibration is trivial over a based family of paths**: `p⁻¹(T) ≃ₕ F × T`. -/
noncomputable def homotopyEquiv :
    ContinuousMap.HomotopyEquiv (Total w x₀) (PathFibre X x₀ x₁ × T) where
  toFun := untrivialise w x₀
  invFun := trivialise w x₀
  left_inv := ⟨homotopyLeft w x₀⟩
  right_inv := ⟨homotopyRight w x₀⟩

/-! #### Base change -/

variable {T' : Type v} [TopologicalSpace T']

/-- Restricting a based family of paths along a map of index spaces. -/
def comap (w : BasedPathFamily T X x₁) (j : C(T', T)) : BasedPathFamily T' X x₁ where
  curve := w.curve.comp (j.prodMap (ContinuousMap.id I))
  curve_zero t := w.curve_zero (j t)

@[simp] theorem comap_curve (j : C(T', T)) (t : T') (s : I) :
    (w.comap j).curve (t, s) = w.curve (j t, s) := rfl

/-- The map of total spaces induced by a map of index spaces. -/
def totalMap (j : C(T', T)) : C(Total (w.comap j) x₀, Total w x₀) where
  toFun z := ⟨(j z.1.1, z.1.2), z.2⟩
  continuous_toFun :=
    ((j.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

@[simp] theorem totalMap_val (j : C(T', T)) (z : Total (w.comap j) x₀) :
    (totalMap w x₀ j z).1 = (j z.1.1, z.1.2) := rfl

/-- **Restriction of the trivialisation**: the trivialisation over `T` restricts, along any map
`j : T' → T`, to the trivialisation of the restricted family. -/
theorem totalMap_trivialise (j : C(T', T)) (p : PathFibre X x₀ x₁ × T') :
    totalMap w x₀ j (trivialise (w.comap j) x₀ p) = trivialise w x₀ (p.1, j p.2) := by
  refine Subtype.ext (Prod.ext rfl (Subtype.ext (ContinuousMap.ext fun t => ?_)))
  show trivialiseCurve (w.comap j) x₀ (p, t) = trivialiseCurve w x₀ ((p.1, j p.2), t)
  rw [trivialiseCurve, trivialiseCurve]
  apply fconcat_congr
  · intro s; rfl
  · intro s; rfl

/-- **Restriction of the inverse trivialisation.** -/
theorem untrivialise_totalMap (j : C(T', T)) (z : Total (w.comap j) x₀) :
    untrivialise w x₀ (totalMap w x₀ j z) =
      ((untrivialise (w.comap j) x₀ z).1, j (untrivialise (w.comap j) x₀ z).2) := by
  refine Prod.ext (Subtype.ext (Subtype.ext (ContinuousMap.ext fun t => ?_))) rfl
  show untrivialiseCurve w x₀ (totalMap w x₀ j z, t) = untrivialiseCurve (w.comap j) x₀ (z, t)
  rw [untrivialiseCurve, untrivialiseCurve]
  apply fconcat_congr
  · intro s; rfl
  · intro s; rfl

end BasedPathFamily

/-! ### Trivialisation over a contractible piece of the base -/

section Disc

variable {X : Type u} [TopologicalSpace X] {E : Type v} [TopologicalSpace E]

theorem pullback_snd_mem {S : Set X} {q : C(↥S, X)} (hq : ∀ b : ↥S, q b = (b : X))
    {p : C(E, X)} (z : Pullback q p) : p z.1.2 ∈ S := by
  rw [← z.2, hq]
  exact z.1.1.2

theorem pullback_fst_val {S : Set X} {q : C(↥S, X)} (hq : ∀ b : ↥S, q b = (b : X))
    {p : C(E, X)} (z : Pullback q p) : p z.1.2 = (z.1.1 : X) := by
  rw [← z.2, hq]

theorem pullback_left_inv {S : Set X} {q : C(↥S, X)} (hq : ∀ b : ↥S, q b = (b : X))
    {p : C(E, X)} (z : Pullback q p) :
    (⟨(⟨p z.1.2, pullback_snd_mem hq z⟩, z.1.2), hq _⟩ : Pullback q p) = z :=
  Subtype.ext (Prod.ext (Subtype.ext (pullback_fst_val hq z)) rfl)

/-- The pullback of a map `p : E → X` along the inclusion of a subset `S ⊆ X` is the restriction
of `E` over `S`. -/
def pullbackSubtypeHomeo {S : Set X} (q : C(↥S, X)) (hq : ∀ b : ↥S, q b = (b : X))
    (p : C(E, X)) : Pullback q p ≃ₜ {e : E // p e ∈ S} where
  toFun z := ⟨z.1.2, pullback_snd_mem hq z⟩
  invFun e := ⟨(⟨p e.1, e.2⟩, e.1), hq _⟩
  left_inv z := pullback_left_inv hq z
  right_inv _ := rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (((p.continuous.comp continuous_subtype_val).subtype_mk _).prodMk
    continuous_subtype_val).subtype_mk _

variable {x₀ : X} {D : Set X} {b₀ : ↥D}

/-- The part of the path space of `(X, x₀)` lying over a subset `S` of `X`. -/
def PathSpaceOver (X : Type u) [TopologicalSpace X] (x₀ : X) (S : Set X) : Type u :=
  {γ : PathSpace X x₀ // ev₁ X x₀ γ ∈ S}

instance (X : Type u) [TopologicalSpace X] (x₀ : X) (S : Set X) :
    TopologicalSpace (PathSpaceOver X x₀ S) :=
  inferInstanceAs (TopologicalSpace {γ : PathSpace X x₀ // ev₁ X x₀ γ ∈ S})

/-- The based family of paths in `X` obtained from contraction data on `D`, restricted to a
subset `D' ⊆ D`. -/
def discFamily (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    BasedPathFamily ↥D' X (b₀ : X) where
  curve := ⟨fun z => (c.curve (⟨z.1.1, hD' z.1.2⟩, z.2) : X),
    continuous_subtype_val.comp (c.curve.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd))⟩
  curve_zero t := congrArg Subtype.val (c.curve_zero ⟨t.1, hD' t.2⟩)

@[simp] theorem discFamily_curve (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (b : ↥D') (s : I) :
    (discFamily c hD').curve (b, s) = (c.curve (⟨b.1, hD' b.2⟩, s) : X) := rfl

theorem discFamily_endpt (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) (b : ↥D') :
    (discFamily c hD').endpt b = (b : X) := congrArg Subtype.val (c.curve_one _)

/-- The total space of the restricted path fibration, identified with `p⁻¹(D')`. -/
noncomputable def discTotalHomeo (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    BasedPathFamily.Total (discFamily c hD') x₀ ≃ₜ PathSpaceOver X x₀ D' :=
  pullbackSubtypeHomeo _ (discFamily_endpt c hD') _

/-- The identification of the total space with `p⁻¹(D')`, as a continuous map. -/
noncomputable def discTotalCM (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(BasedPathFamily.Total (discFamily c hD') x₀, PathSpaceOver X x₀ D') :=
  ⟨discTotalHomeo c hD', (discTotalHomeo (x₀ := x₀) c hD').continuous⟩

/-- The inverse identification, as a continuous map. -/
noncomputable def discTotalCMsymm (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(PathSpaceOver X x₀ D', BasedPathFamily.Total (discFamily c hD') x₀) :=
  ⟨(discTotalHomeo (x₀ := x₀) c hD').symm, (discTotalHomeo (x₀ := x₀) c hD').symm.continuous⟩

/-- **The trivialisation over a contractible piece of the base**: `(γ, b) ↦ γ ⬝ c_b`. -/
noncomputable def trivialiseOver (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(PathFibre X x₀ (b₀ : X) × ↥D', PathSpaceOver X x₀ D') :=
  (discTotalCM c hD').comp (BasedPathFamily.trivialise (discFamily c hD') x₀)

/-- **The inverse trivialisation**: `δ ↦ (δ ⬝ c_{ev₁ δ}⁻¹, ev₁ δ)`. -/
noncomputable def untrivialiseOver (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(PathSpaceOver X x₀ D', PathFibre X x₀ (b₀ : X) × ↥D') :=
  (BasedPathFamily.untrivialise (discFamily c hD') x₀).comp (discTotalCMsymm c hD')

theorem trivialiseOver_val (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (p : PathFibre X x₀ (b₀ : X) × ↥D') (t : I) :
    (trivialiseOver c hD' p).1.1 t =
      BasedPathFamily.trivialiseCurve (discFamily c hD') x₀ (p, t) := rfl

theorem trivialiseOver_apply (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (γ : PathFibre X x₀ (b₀ : X)) (b : ↥D') (t : I) :
    (trivialiseOver c hD' (γ, b)).1.1 t =
      if (t : ℝ) ≤ 1 / 2 then γ.1.1 (projI (2 * (t : ℝ)))
      else (c.curve (⟨b.1, hD' b.2⟩, projI (2 * (t : ℝ) - 1)) : X) := by
  rw [trivialiseOver_val, BasedPathFamily.trivialiseCurve, fconcat_apply]
  rfl

@[simp] theorem ev₁_trivialiseOver (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (γ : PathFibre X x₀ (b₀ : X)) (b : ↥D') :
    ev₁ X x₀ (trivialiseOver c hD' (γ, b)).1 = (b : X) := by
  show BasedPathFamily.trivialiseCurve (discFamily c hD') x₀ ((γ, b), 1) = (b : X)
  rw [BasedPathFamily.trivialiseCurve_one, discFamily_endpt]

@[simp] theorem untrivialiseOver_snd (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (δ : PathSpaceOver X x₀ D') : ((untrivialiseOver c hD' δ).2 : X) = ev₁ X x₀ δ.1 := rfl

/-- The homotopy `untrivialiseOver ∘ trivialiseOver ≃ id`, as a map. -/
noncomputable def homotopyRightOverMap (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(I × (PathFibre X x₀ (b₀ : X) × ↥D'), PathFibre X x₀ (b₀ : X) × ↥D') :=
  BasedPathFamily.homotopyRightMap (discFamily c hD') x₀

theorem homotopyRightOverMap_zero (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (p : PathFibre X x₀ (b₀ : X) × ↥D') :
    homotopyRightOverMap c hD' (0, p) = untrivialiseOver c hD' (trivialiseOver c hD' p) := by
  rw [homotopyRightOverMap, BasedPathFamily.homotopyRightMap_zero]
  exact congrArg _ ((discTotalHomeo (x₀ := x₀) c hD').symm_apply_apply _).symm

/-- **`untrivialiseOver ∘ trivialiseOver` is homotopic to the identity.** -/
noncomputable def homotopyRightOver (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    ContinuousMap.Homotopy ((untrivialiseOver c hD').comp (trivialiseOver c hD'))
      (ContinuousMap.id (PathFibre X x₀ (b₀ : X) × ↥D')) where
  toContinuousMap := homotopyRightOverMap c hD'
  map_zero_left := homotopyRightOverMap_zero c hD'
  map_one_left := BasedPathFamily.homotopyRightMap_one (discFamily c hD') x₀

/-- **The homotopy `untrivialiseOver ∘ trivialiseOver ≃ id` lies over the base**: it never moves
the `D'`-coordinate. -/
@[simp] theorem homotopyRightOver_snd (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (z : I × (PathFibre X x₀ (b₀ : X) × ↥D')) :
    (homotopyRightOver c hD' z).2 = z.2.2 := rfl

/-- The homotopy `trivialiseOver ∘ untrivialiseOver ≃ id`, as a map. -/
noncomputable def homotopyLeftOverMap (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    C(I × PathSpaceOver X x₀ D', PathSpaceOver X x₀ D') :=
  (discTotalCM c hD').comp ((BasedPathFamily.homotopyLeftMap (discFamily c hD') x₀).comp
    ((ContinuousMap.id I).prodMap (discTotalCMsymm c hD')))

theorem homotopyLeftOverMap_one (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (δ : PathSpaceOver X x₀ D') : homotopyLeftOverMap c hD' (1, δ) = δ := by
  rw [homotopyLeftOverMap]
  show discTotalCM c hD'
      (BasedPathFamily.homotopyLeftMap (discFamily c hD') x₀ (1, discTotalCMsymm c hD' δ)) = δ
  rw [BasedPathFamily.homotopyLeftMap_one]
  exact (discTotalHomeo (x₀ := x₀) c hD').apply_symm_apply δ

/-- **`trivialiseOver ∘ untrivialiseOver` is homotopic to the identity.** -/
noncomputable def homotopyLeftOver (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    ContinuousMap.Homotopy ((trivialiseOver c hD').comp (untrivialiseOver c hD'))
      (ContinuousMap.id (PathSpaceOver X x₀ D')) where
  toContinuousMap := homotopyLeftOverMap c hD'
  map_zero_left δ := congrArg (discTotalCM c hD')
    (BasedPathFamily.homotopyLeftMap_zero (discFamily c hD') x₀ (discTotalCMsymm c hD' δ))
  map_one_left := homotopyLeftOverMap_one c hD'

/-- **The homotopy `trivialiseOver ∘ untrivialiseOver ≃ id` lies over the base**: the end point of
the path is constant throughout the homotopy. -/
theorem homotopyLeftOver_ev₁ (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D)
    (z : I × PathSpaceOver X x₀ D') :
    ev₁ X x₀ (homotopyLeftOver c hD' z).1 = ev₁ X x₀ z.2.1 :=
  pullback_fst_val (discFamily_endpt c hD') _

/-- **Over a contractible piece of the base the path fibration is trivial**: `p⁻¹(D') ≃ₕ F × D'`
for any `D' ⊆ D`, where `D` carries contraction data. The two homotopies are
`Submission.homotopyLeftOver` and `Submission.homotopyRightOver`, both of which lie over the
base. -/
noncomputable def homotopyEquivOverDisc (c : ContractionData ↥D b₀) {D' : Set X} (hD' : D' ⊆ D) :
    ContinuousMap.HomotopyEquiv (PathSpaceOver X x₀ D') (PathFibre X x₀ (b₀ : X) × ↥D') where
  toFun := untrivialiseOver c hD'
  invFun := trivialiseOver c hD'
  left_inv := ⟨homotopyLeftOver c hD'⟩
  right_inv := ⟨homotopyRightOver c hD'⟩

/-- **Restricting a trivialisation to a smaller piece of the base.** Since `D₊ ∩ D₋ ⊆ D₊`, the
trivialisation over `D₊` restricts to one over `D₊ ∩ D₋`; this is what Mayer–Vietoris needs. -/
theorem trivialiseOver_restrict (c : ContractionData ↥D b₀) {D' D'' : Set X} (hD' : D' ⊆ D)
    (hD'' : D'' ⊆ D') (γ : PathFibre X x₀ (b₀ : X)) (b : ↥D'') :
    (trivialiseOver (x₀ := x₀) c (hD''.trans hD') (γ, b)).1 =
      (trivialiseOver (x₀ := x₀) c hD' (γ, ⟨b.1, hD'' b.2⟩)).1 :=
  rfl

/-- **Restricting the inverse trivialisation to a smaller piece of the base.** -/
theorem untrivialiseOver_restrict (c : ContractionData ↥D b₀) {D' D'' : Set X} (hD' : D' ⊆ D)
    (hD'' : D'' ⊆ D') (δ : PathSpaceOver X x₀ D'') :
    (untrivialiseOver (x₀ := x₀) c (hD''.trans hD') δ).1 =
      (untrivialiseOver (x₀ := x₀) c hD' ⟨δ.1, hD'' δ.2⟩).1 :=
  rfl

end Disc

end Submission
