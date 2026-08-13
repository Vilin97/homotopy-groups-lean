/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.ReducedSuspension
import Submission.Model.Suspension

/-!
# From unreduced to reduced suspension

For a pointed space `(X, x₀)`, reduced suspension is obtained from unreduced suspension by also
collapsing the basepoint meridian.  This file constructs that quotient map, gives reduced
suspension its expected functorial action on based maps, and proves their naturality square.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission

open unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]

namespace ReducedSusp

/-- The universal property of reduced suspension: a continuous cylinder map which is constant
on the collapsed locus descends to reduced suspension. -/
def lift (x₀ : X) (f : C(I × X, Y))
    (hcollapsed : ∀ p : I × X, ReducedSuspCollapsed x₀ p → f p = f (0, x₀)) :
    C(ReducedSusp X x₀, Y) :=
  ⟨Quotient.lift f (by
      intro a b hab
      rcases hab with rfl | ⟨ha, hb⟩
      · rfl
      · exact (hcollapsed a ha).trans (hcollapsed b hb).symm),
    f.continuous.quotient_lift _⟩

@[simp]
theorem lift_mk (x₀ : X) (f : C(I × X, Y))
    (hcollapsed : ∀ p : I × X, ReducedSuspCollapsed x₀ p → f p = f (0, x₀))
    (p : I × X) :
    lift x₀ f hcollapsed (mk x₀ p) = f p :=
  rfl

/-- A based map induces a map of reduced suspensions. -/
def map (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀) :
    C(ReducedSusp X x₀, ReducedSusp Y y₀) :=
  lift x₀
    ⟨fun p ↦ mk y₀ (p.1, f p.2), (mk y₀).continuous.comp (by fun_prop)⟩
    (by
      rintro ⟨t, x⟩ (ht | ht | hx)
      · change t = 0 at ht
        change mk y₀ (t, f x) = mk y₀ (0, f x₀)
        rw [ht, mk_zero, mk_zero]
      · change t = 1 at ht
        change mk y₀ (t, f x) = mk y₀ (0, f x₀)
        rw [ht, mk_one, mk_zero]
      · change x = x₀ at hx
        change mk y₀ (t, f x) = mk y₀ (0, f x₀)
        rw [hx, hf, mk_base, mk_zero])

@[simp]
theorem map_mk (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
    (p : I × X) :
    map x₀ y₀ f hf (mk x₀ p) = mk y₀ (p.1, f p.2) :=
  rfl

@[simp]
theorem map_base (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀) :
    map x₀ y₀ f hf (base x₀) = base y₀ := by
  change mk y₀ (0, f x₀) = base y₀
  rw [hf, mk_zero]

@[simp]
theorem map_id (x₀ : X) :
    map x₀ x₀ (ContinuousMap.id X) rfl = ContinuousMap.id (ReducedSusp X x₀) := by
  apply ContinuousMap.ext
  intro q
  induction q using ind x₀ with
  | h p => rfl

@[simp]
theorem map_comp (x₀ : X) (y₀ : Y) (z₀ : Z)
    (f : C(X, Y)) (g : C(Y, Z)) (hf : f x₀ = y₀) (hg : g y₀ = z₀) :
    map x₀ z₀ (g.comp f) (by simp [hf, hg]) =
      (map y₀ z₀ g hg).comp (map x₀ y₀ f hf) := by
  apply ContinuousMap.ext
  intro q
  induction q using ind x₀ with
  | h p => rfl

end ReducedSusp

namespace Susp

/-- Collapse the basepoint meridian in unreduced suspension to obtain reduced suspension. -/
def toReduced (x₀ : X) : C(Susp X, ReducedSusp X x₀) :=
  lift (ReducedSusp.mk x₀)
    (fun x y ↦ by rw [ReducedSusp.mk_zero, ReducedSusp.mk_zero])
    (fun x y ↦ by rw [ReducedSusp.mk_one, ReducedSusp.mk_one])

@[simp]
theorem toReduced_mk (x₀ : X) (p : I × X) :
    toReduced x₀ (mk p) = ReducedSusp.mk x₀ p :=
  rfl

@[simp]
theorem toReduced_basepoint_meridian (x₀ : X) (t : I) :
    toReduced x₀ (mk (t, x₀)) = ReducedSusp.base x₀ := by
  rw [toReduced_mk, ReducedSusp.mk_base]

/-- The quotient from unreduced to reduced suspension is onto. -/
theorem toReduced_surjective (x₀ : X) : Function.Surjective (toReduced x₀) := by
  intro q
  induction q using ReducedSusp.ind x₀ with
  | h p => exact ⟨mk p, rfl⟩

/-- The quotient from unreduced to reduced suspension is a quotient map. -/
theorem isQuotientMap_toReduced (x₀ : X) :
    Topology.IsQuotientMap (toReduced x₀) := by
  apply Topology.IsQuotientMap.of_comp_isQuotientMap Susp.isQuotientMap_mk
  have hcomp :
      (toReduced x₀ : Susp X → ReducedSusp X x₀) ∘ (mk : I × X → Susp X) =
        (ReducedSusp.mk x₀ : I × X → ReducedSusp X x₀) := by
    funext p
    rfl
  rw [hcomp]
  exact ReducedSusp.isQuotientMap_mk x₀

/-- Collapsing the basepoint meridian is natural with respect to based maps. -/
theorem toReduced_naturality (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀) :
    (ReducedSusp.map x₀ y₀ f hf).comp (toReduced x₀) =
      (toReduced y₀).comp (Susp.map f) := by
  apply ContinuousMap.ext
  intro q
  induction q using Susp.ind with
  | h p => rfl

end Susp

end Submission
