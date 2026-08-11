/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Path
import Submission.Homotopy.Fibration

/-!
# The path fibration

For a based space `(X, x₀)` we introduce the space `PathSpace X x₀` of paths starting at `x₀`,
carrying the compact-open topology, together with the endpoint evaluation
`ev₁ : PathSpace X x₀ → X`.

## Main results

* `Submission.PathSpace.instContractibleSpace`: the path space is contractible.
* `Submission.hasHLP_ev₁`: `ev₁` has the homotopy lifting property with respect to *every* space,
  i.e. it is a Hurewicz fibration.
* `Submission.isSerreFibration_ev₁`: in particular `ev₁` is a Serre fibration.
* `Submission.fibreEv₁Homeomorph`: the fibre of `ev₁` over `x₀` is the loop space `Path x₀ x₀`.
-/

namespace Submission

open unitInterval

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-! ### The path space -/

/-- The space of paths in `X` starting at `x₀`, with the compact-open topology. -/
def PathSpace (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  {γ : C(unitInterval, X) // γ 0 = x₀}

instance (X : Type*) [TopologicalSpace X] (x₀ : X) : TopologicalSpace (PathSpace X x₀) :=
  inferInstanceAs (TopologicalSpace {γ : C(unitInterval, X) // γ 0 = x₀})

namespace PathSpace

/-- A point of the path space starts at the basepoint. -/
@[simp] theorem source (γ : PathSpace X x₀) : γ.1 0 = x₀ := γ.2

/-- The inclusion of the path space into `C(I, X)` is continuous. -/
theorem continuous_val : Continuous (Subtype.val : PathSpace X x₀ → C(unitInterval, X)) :=
  continuous_subtype_val

/-- Two elements of the path space agreeing pointwise are equal. -/
theorem ext {γ δ : PathSpace X x₀} (h : ∀ t, γ.1 t = δ.1 t) : γ = δ :=
  Subtype.ext (ContinuousMap.ext h)

/-- The constant path at the basepoint. -/
def const (X : Type*) [TopologicalSpace X] (x₀ : X) : PathSpace X x₀ :=
  ⟨ContinuousMap.const _ x₀, rfl⟩

/-- The constant path takes the value `x₀` everywhere. -/
@[simp] theorem const_apply (t : unitInterval) : (PathSpace.const X x₀).1 t = x₀ := rfl

end PathSpace

/-- Evaluation of a path at its endpoint. -/
def ev₁ (X : Type*) [TopologicalSpace X] (x₀ : X) : C(PathSpace X x₀, X) :=
  ⟨fun γ => γ.1 1, (continuous_eval_const (1 : unitInterval)).comp PathSpace.continuous_val⟩

/-- `ev₁` evaluates a path at `1`. -/
@[simp] theorem ev₁_apply (γ : PathSpace X x₀) : ev₁ X x₀ γ = γ.1 1 := rfl

/-! ### Contractibility of the path space -/

/-- Multiplication `I × I → I`, as a continuous map. -/
def mulCM : C(unitInterval × unitInterval, unitInterval) :=
  ⟨fun p => ⟨(p.1 : ℝ) * (p.2 : ℝ), unitInterval.mul_mem p.1.2 p.2.2⟩, by fun_prop⟩

/-- `1` is a left unit for `mulCM`. -/
@[simp] theorem mulCM_one_left (t : unitInterval) : mulCM (1, t) = t :=
  Subtype.ext (by simp [mulCM])

/-- `0` is a left absorbing element for `mulCM`. -/
@[simp] theorem mulCM_zero_left (t : unitInterval) : mulCM (0, t) = 0 :=
  Subtype.ext (by simp [mulCM])

/-- `0` is a right absorbing element for `mulCM`. -/
@[simp] theorem mulCM_zero_right (s : unitInterval) : mulCM (s, 0) = 0 :=
  Subtype.ext (by simp [mulCM])

/-- The uncurried contraction of the path space: `((s, γ), t) ↦ γ (σ s * t)`. -/
def contractionAux (X : Type*) [TopologicalSpace X] (x₀ : X) :
    C((unitInterval × PathSpace X x₀) × unitInterval, X) :=
  ⟨fun q => q.1.2.1 (mulCM (σ q.1.1, q.2)),
    Continuous.eval (PathSpace.continuous_val.comp (continuous_snd.comp continuous_fst))
      (mulCM.continuous.comp
        ((unitInterval.continuous_symm.comp (continuous_fst.comp continuous_fst)).prodMk
          continuous_snd))⟩

/-- The contraction of `PathSpace X x₀` onto the constant path: at time `s` the path `γ` is
replaced by its restriction to `[0, σ s]`, reparametrised to `[0, 1]`. -/
def pathSpaceContraction (X : Type*) [TopologicalSpace X] (x₀ : X) :
    C(unitInterval × PathSpace X x₀, PathSpace X x₀) :=
  ⟨fun z => ⟨ContinuousMap.curry (contractionAux X x₀) z, by simp [contractionAux]⟩,
    (ContinuousMap.curry (contractionAux X x₀)).continuous.subtype_mk _⟩

/-- The value of the contraction at a point of the path space. -/
@[simp] theorem pathSpaceContraction_apply (s : unitInterval) (γ : PathSpace X x₀)
    (t : unitInterval) :
    (pathSpaceContraction X x₀ (s, γ)).1 t = γ.1 (mulCM (σ s, t)) := rfl

/-- The path space of a based space is contractible. -/
instance PathSpace.instContractibleSpace : ContractibleSpace (PathSpace X x₀) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨PathSpace.const X x₀, ⟨⟨pathSpaceContraction X x₀, fun γ => ?_, fun γ => ?_⟩⟩⟩
  · exact PathSpace.ext fun t => by simp
  · exact PathSpace.ext fun t => by simp

/-! ### `ev₁` is a fibration -/

/-- The retraction `ℝ → I` which is the identity on `I`, `0` below `0` and `1` above `1`. -/
noncomputable def projI : C(ℝ, unitInterval) := ⟨Set.projIcc 0 1 zero_le_one, continuous_projIcc⟩

/-- `projI` is the identity on `I`. -/
@[simp] theorem projI_coe (t : unitInterval) : projI (t : ℝ) = t :=
  Set.projIcc_val zero_le_one t

/-- `projI` sends `0` to `0`. -/
@[simp] theorem projI_zero : projI 0 = 0 := Subtype.ext (by simp [projI])

/-- `projI` sends `1` to `1`. -/
@[simp] theorem projI_one : projI 1 = 1 := Subtype.ext (by simp [projI])

variable {A : Type*} [TopologicalSpace A]

/-- The reparametrisation used in the lifting formula for `ev₁`: on the point `((s, a), t)` it
returns `t * (1 + s)`. -/
def reparam (q : (unitInterval × A) × unitInterval) : ℝ := (q.2 : ℝ) * (1 + (q.1.1 : ℝ))

/-- The reparametrisation is continuous. -/
theorem continuous_reparam : Continuous (reparam : (unitInterval × A) × unitInterval → ℝ) := by
  unfold reparam; fun_prop

/-- The explicit lift of a homotopy `H` through `ev₁`, starting from the family of paths `f`.
On `[0, 1/(1+s)]` it traverses the path `f a`, and on `[1/(1+s), 1]` it traverses the piece of
the homotopy `H` over the interval `[0, s]`. -/
noncomputable def liftAux (f : C(A, PathSpace X x₀)) (H : C(unitInterval × A, X)) :
    (unitInterval × A) × unitInterval → X := fun q =>
  if reparam q ≤ 1 then (f q.1.2).1 (projI (reparam q))
  else H (projI (reparam q - 1), q.1.2)

/-- The lifting formula is continuous: the two branches agree on the overlap. -/
theorem continuous_liftAux (f : C(A, PathSpace X x₀)) (H : C(unitInterval × A, X))
    (h0 : ∀ a, H (0, a) = ev₁ X x₀ (f a)) : Continuous (liftAux f H) := by
  refine Continuous.if_le ?_ ?_ continuous_reparam continuous_const ?_
  · exact Continuous.eval
      (PathSpace.continuous_val.comp (f.continuous.comp (continuous_snd.comp continuous_fst)))
      (projI.continuous.comp continuous_reparam)
  · exact H.continuous.comp
      ((projI.continuous.comp (continuous_reparam.sub continuous_const)).prodMk
        (continuous_snd.comp continuous_fst))
  · intro q hq
    rw [hq]
    simpa using (h0 q.1.2).symm

/-- The lift of `H` through `ev₁`, as a continuous family of paths. -/
noncomputable def lift (f : C(A, PathSpace X x₀)) (H : C(unitInterval × A, X))
    (h0 : ∀ a, H (0, a) = ev₁ X x₀ (f a)) : C(unitInterval × A, C(unitInterval, X)) :=
  ContinuousMap.curry ⟨liftAux f H, continuous_liftAux f H h0⟩

/-- The value of the lift, in terms of `liftAux`. -/
theorem lift_apply (f : C(A, PathSpace X x₀)) (H : C(unitInterval × A, X))
    (h0 : ∀ a, H (0, a) = ev₁ X x₀ (f a)) (z : unitInterval × A) (t : unitInterval) :
    lift f H h0 z t = liftAux f H (z, t) := rfl

/-- Every path in the lifted family starts at the basepoint. -/
theorem lift_zero (f : C(A, PathSpace X x₀)) (H : C(unitInterval × A, X))
    (h0 : ∀ a, H (0, a) = ev₁ X x₀ (f a)) (z : unitInterval × A) : lift f H h0 z 0 = x₀ := by
  have hr : reparam (z, (0 : unitInterval)) = 0 := by simp [reparam]
  rw [lift_apply, liftAux, hr, if_pos zero_le_one]
  simp

/-- `ev₁` has the homotopy lifting property with respect to every space: it is a Hurewicz
fibration. -/
theorem hasHLP_ev₁ (X : Type*) [TopologicalSpace X] (x₀ : X) (A : Type*) [TopologicalSpace A] :
    HasHLP (ev₁ X x₀) A := by
  intro f H h0
  refine ⟨⟨fun z => ⟨lift f H h0 z, lift_zero f H h0 z⟩,
    (lift f H h0).continuous.subtype_mk _⟩, fun a => ?_, fun z => ?_⟩
  · refine PathSpace.ext fun t => ?_
    have hr : reparam (((0 : unitInterval), a), t) = (t : ℝ) := by simp [reparam]
    show liftAux f H _ = _
    rw [liftAux, hr, if_pos t.2.2]
    simp
  · obtain ⟨s, a⟩ := z
    show liftAux f H ((s, a), (1 : unitInterval)) = H (s, a)
    have hr : reparam ((s, a), (1 : unitInterval)) = 1 + (s : ℝ) := by simp [reparam]
    rw [liftAux, hr]
    by_cases hs : (1 : ℝ) + (s : ℝ) ≤ 1
    · have hs0 : (s : ℝ) = 0 := le_antisymm (by linarith) s.2.1
      have hs1 : s = 0 := Subtype.ext (by simpa using hs0)
      subst hs1
      rw [if_pos hs]
      simpa using (h0 a).symm
    · rw [if_neg hs]
      have h1 : (1 : ℝ) + (s : ℝ) - 1 = (s : ℝ) := by ring
      rw [h1, projI_coe]

/-- `ev₁` is a Serre fibration. -/
theorem isSerreFibration_ev₁ (X : Type*) [TopologicalSpace X] (x₀ : X) :
    IsSerreFibration (ev₁ X x₀) := fun _ => hasHLP_ev₁ X x₀ _

/-! ### The fibre of the path fibration -/

/-- The fibre of `ev₁` over the basepoint is the loop space `Path x₀ x₀`. -/
def fibreEv₁Homeomorph (X : Type*) [TopologicalSpace X] (x₀ : X) :
    {γ : PathSpace X x₀ // ev₁ X x₀ γ = x₀} ≃ₜ Path x₀ x₀ where
  toFun γ := { toContinuousMap := γ.1.1, source' := γ.1.2, target' := γ.2 }
  invFun γ := ⟨⟨γ.toContinuousMap, γ.source'⟩, γ.target'⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_induced_rng.2 (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := (continuous_induced_dom.subtype_mk _).subtype_mk _

end Submission
