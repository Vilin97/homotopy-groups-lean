/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UnitInterval

/-!
# Serre fibrations

Mathlib has no notion of a fibration, so we develop the small amount of point-set theory that the
computation of `π_{n+1}(Sⁿ)` needs.

## Main definitions

* `Submission.HasHLP p A`: the map `p : C(E, B)` has the *homotopy lifting property* with respect
  to the space `A`.
* `Submission.IsSerreFibration p`: `p` has the homotopy lifting property with respect to every
  cube `Fin n → I`.
* `Submission.Pullback g p`: the fibre product `{(b, e) : B' × E // g b = p e}` of `g : C(B', B)`
  and `p : C(E, B)`, with the subspace topology.

## Main results

* `Submission.IsSerreFibration.comp`: Serre fibrations are stable under composition.
* `Submission.IsSerreFibration.pullback`: Serre fibrations are stable under base change.
* `Submission.IsSerreFibration.of_homeomorph`: a homeomorphism is a Serre fibration.
* `Submission.isSerreFibration_fst`: a projection `X × F → X` is a Serre fibration.
-/

namespace Submission

open unitInterval

variable {B B' D E E' : Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalSpace E']

/-- `p : C(E, B)` has the homotopy lifting property with respect to `A`: every homotopy in `B`
parametrised by `A` whose initial stage lifts through `p` can itself be lifted through `p`. -/
def HasHLP (p : C(E, B)) (A : Type*) [TopologicalSpace A] : Prop :=
  ∀ (f : C(A, E)) (H : C(unitInterval × A, B)),
    (∀ a, H (0, a) = p (f a)) →
    ∃ H' : C(unitInterval × A, E), (∀ a, H' (0, a) = f a) ∧ ∀ z, p (H' z) = H z

/-- A Serre fibration: a map with the homotopy lifting property for all cubes `Fin n → I`. -/
def IsSerreFibration (p : C(E, B)) : Prop := ∀ n : ℕ, HasHLP p (Fin n → unitInterval)

section Congr

variable {A A' : Type*} [TopologicalSpace A] [TopologicalSpace A']

/-- The homotopy lifting property only depends on the underlying function of `p`. -/
theorem HasHLP.congr {p q : C(E, B)} (hp : HasHLP p A) (h : ∀ e, p e = q e) : HasHLP q A := by
  intro f H h0
  obtain ⟨H', hH'0, hH'⟩ := hp f H fun a => (h0 a).trans (h (f a)).symm
  exact ⟨H', hH'0, fun z => (h (H' z)).symm.trans (hH' z)⟩

/-- Being a Serre fibration only depends on the underlying function of `p`. -/
theorem IsSerreFibration.congr {p q : C(E, B)} (hp : IsSerreFibration p) (h : ∀ e, p e = q e) :
    IsSerreFibration q := fun n => (hp n).congr h

/-- The homotopy lifting property transports along a homeomorphism of parameter spaces. -/
theorem HasHLP.param_homeomorph {p : C(E, B)} (hp : HasHLP p A) (e : A' ≃ₜ A) : HasHLP p A' := by
  intro f H h0
  have hc : Continuous fun z : unitInterval × A => (z.1, e.symm z.2) :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  have hc' : Continuous fun z : unitInterval × A' => (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  obtain ⟨K, hK0, hK⟩ := hp (f.comp ⟨e.symm, e.symm.continuous⟩) (H.comp ⟨_, hc⟩)
    fun a => h0 (e.symm a)
  refine ⟨K.comp ⟨_, hc'⟩, fun a => ?_, fun z => ?_⟩
  · simpa using hK0 (e a)
  · simpa using hK (z.1, e z.2)

end Congr

section Basic

variable {A : Type*} [TopologicalSpace A]

/-- A map with a two-sided continuous inverse has the homotopy lifting property. -/
theorem HasHLP.of_inverse {p : C(E, B)} (s : C(B, E)) (hsp : ∀ x, s (p x) = x)
    (hps : ∀ b, p (s b) = b) : HasHLP p A := by
  intro f H h0
  refine ⟨s.comp H, fun a => ?_, fun z => ?_⟩
  · simpa [h0 a] using hsp (f a)
  · simpa using hps (H z)

/-- A homeomorphism has the homotopy lifting property. -/
theorem HasHLP.of_homeomorph (e : E ≃ₜ B) : HasHLP (e : C(E, B)) A :=
  HasHLP.of_inverse (e.symm : C(B, E)) e.symm_apply_apply e.apply_symm_apply

/-- A homeomorphism is a Serre fibration. -/
theorem IsSerreFibration.of_homeomorph (e : E ≃ₜ B) : IsSerreFibration (e : C(E, B)) :=
  fun _ => HasHLP.of_homeomorph e

/-- The identity has the homotopy lifting property. -/
theorem HasHLP.id : HasHLP (ContinuousMap.id E) A :=
  HasHLP.of_inverse (ContinuousMap.id E) (fun _ => rfl) (fun _ => rfl)

/-- The identity is a Serre fibration. -/
theorem isSerreFibration_id : IsSerreFibration (ContinuousMap.id E) := fun _ => HasHLP.id

/-- Any map into a subsingleton has the homotopy lifting property. -/
theorem HasHLP.of_subsingleton [Subsingleton B] (p : C(E, B)) : HasHLP p A :=
  fun f _ _ => ⟨f.comp ContinuousMap.snd, fun _ => rfl, fun _ => Subsingleton.elim _ _⟩

/-- Any map into a subsingleton is a Serre fibration. -/
theorem isSerreFibration_of_subsingleton [Subsingleton B] (p : C(E, B)) : IsSerreFibration p :=
  fun _ => HasHLP.of_subsingleton p

/-- Any map out of an empty space has the homotopy lifting property. -/
theorem HasHLP.of_isEmpty [IsEmpty E] (p : C(E, B)) : HasHLP p A := by
  intro f _ _
  have hA : IsEmpty A := ⟨fun a => IsEmpty.false (f a)⟩
  exact ⟨⟨fun z => hA.elim z.2, continuous_of_const fun z _ => hA.elim z.2⟩,
    fun a => hA.elim a, fun z => hA.elim z.2⟩

/-- Any map out of an empty space is a Serre fibration. -/
theorem isSerreFibration_of_isEmpty [IsEmpty E] (p : C(E, B)) : IsSerreFibration p :=
  fun _ => HasHLP.of_isEmpty p

/-- The first projection of a product has the homotopy lifting property. -/
theorem HasHLP.fst {F : Type*} [TopologicalSpace F] :
    HasHLP (ContinuousMap.fst : C(E × F, E)) A := by
  intro f H h0
  refine ⟨⟨fun z => (H z, (f z.2).2), H.continuous.prodMk
    (continuous_snd.comp (f.continuous.comp continuous_snd))⟩, fun a => ?_, fun _ => rfl⟩
  exact Prod.ext (h0 a) rfl

/-- The first projection of a product is a Serre fibration. -/
theorem isSerreFibration_fst {F : Type*} [TopologicalSpace F] :
    IsSerreFibration (ContinuousMap.fst : C(E × F, E)) := fun _ => HasHLP.fst

end Basic

section Comp

variable {A : Type*} [TopologicalSpace A]

/-- The homotopy lifting property is stable under composition. -/
theorem HasHLP.comp {p : C(E, B)} {q : C(B, D)} (hp : HasHLP p A) (hq : HasHLP q A) :
    HasHLP (q.comp p) A := by
  intro f H h0
  obtain ⟨H₁, hH₁0, hH₁⟩ := hq (p.comp f) H h0
  obtain ⟨H', hH'0, hH'⟩ := hp f H₁ hH₁0
  refine ⟨H', hH'0, fun z => ?_⟩
  simpa [hH'] using hH₁ z

/-- Serre fibrations are stable under composition. -/
theorem IsSerreFibration.comp {p : C(E, B)} {q : C(B, D)} (hp : IsSerreFibration p)
    (hq : IsSerreFibration q) : IsSerreFibration (q.comp p) := fun n => (hp n).comp (hq n)

/-- Precomposing a Serre fibration with a homeomorphism gives a Serre fibration. -/
theorem IsSerreFibration.comp_homeomorph {p : C(E, B)} (hp : IsSerreFibration p) (e : E' ≃ₜ E) :
    IsSerreFibration (p.comp (e : C(E', E))) :=
  (IsSerreFibration.of_homeomorph e).comp hp

end Comp

section Pullback

/-- The pullback (fibre product) of `p : C(E, B)` along `g : C(B', B)`, as a subspace of
`B' × E`. -/
def Pullback (g : C(B', B)) (p : C(E, B)) : Type _ := {z : B' × E // g z.1 = p z.2}

instance (g : C(B', B)) (p : C(E, B)) : TopologicalSpace (Pullback g p) :=
  inferInstanceAs (TopologicalSpace {z : B' × E // g z.1 = p z.2})

namespace Pullback

variable (g : C(B', B)) (p : C(E, B))

/-- The projection from the pullback of `p` along `g` to the new base `B'`. -/
def fst : C(Pullback g p, B') := ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The projection from the pullback of `p` along `g` to the original total space `E`. -/
def snd : C(Pullback g p, E) := ⟨fun z => z.1.2, continuous_snd.comp continuous_subtype_val⟩

/-- The first projection of the pullback, in terms of the underlying pair. -/
@[simp] theorem fst_apply (z : Pullback g p) : fst g p z = z.1.1 := rfl

/-- The second projection of the pullback, in terms of the underlying pair. -/
@[simp] theorem snd_apply (z : Pullback g p) : snd g p z = z.1.2 := rfl

/-- The defining relation of the pullback. -/
theorem comm (z : Pullback g p) : g (fst g p z) = p (snd g p z) := z.2

end Pullback

variable {A : Type*} [TopologicalSpace A]

/-- The homotopy lifting property is stable under base change. -/
theorem HasHLP.pullback {g : C(B', B)} {p : C(E, B)} (hp : HasHLP p A) :
    HasHLP (Pullback.fst g p) A := by
  intro f H h0
  have key : ∀ a, (g.comp H) (0, a) = p ((Pullback.snd g p).comp f a) := by
    intro a
    simpa [h0 a] using (f a).2
  obtain ⟨K, hK0, hK⟩ := hp ((Pullback.snd g p).comp f) (g.comp H) key
  refine ⟨⟨fun z => ⟨(H z, K z), (hK z).symm⟩,
    (H.continuous.prodMk K.continuous).subtype_mk _⟩, fun a => ?_, fun _ => rfl⟩
  exact Subtype.ext (Prod.ext (h0 a) (hK0 a))

/-- Serre fibrations are stable under base change. -/
theorem IsSerreFibration.pullback {g : C(B', B)} {p : C(E, B)} (hp : IsSerreFibration p) :
    IsSerreFibration (Pullback.fst g p) := fun n => (hp n).pullback

end Pullback

end Submission
