/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Constructions.SumProd

/-!
# Monomorphisms into topological pushouts

The forgetful functor from topological spaces to types preserves pushouts.  Since
monomorphisms in both categories are precisely the injective maps, a pushout structure map is
a monomorphism whenever the opposite leg of the span is one.
-/

open CategoryTheory CategoryTheory.Limits Topology

noncomputable section

namespace Submission

universe u

variable {A X Y : TopCat.{u}}

/-- The sum of two quotient maps is a quotient map. -/
theorem IsQuotientMap.sumMap
    {X₁ Y₁ X₂ Y₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace X₂] [TopologicalSpace Y₂]
    {f : X₁ → Y₁} {g : X₂ → Y₂}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    IsQuotientMap (Sum.map f g) := by
  rw [isQuotientMap_iff]
  constructor
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    rw [isOpen_sum_iff, isOpen_sum_iff]
    change (IsOpen (f ⁻¹' (Sum.inl ⁻¹' U)) ∧ IsOpen (g ⁻¹' (Sum.inr ⁻¹' U))) ↔ _
    rw [hf.isOpen_preimage, hg.isOpen_preimage]
  · exact hf.surjective.sumMap hg.surjective

/-- The map from the disjoint union of the two summands onto their topological pushout. -/
def pushoutSumDesc (f : A ⟶ X) (g : A ⟶ Y) :
    (X : Type u) ⊕ (Y : Type u) →
      ((show TopCat.{u} from CategoryTheory.Limits.pushout f g) : Type u) :=
  Sum.elim (pushout.inl f g) (pushout.inr f g)

@[simp]
theorem pushoutSumDesc_inl (f : A ⟶ X) (g : A ⟶ Y) (x : X) :
    pushoutSumDesc f g (Sum.inl x) = pushout.inl f g x := rfl

@[simp]
theorem pushoutSumDesc_inr (f : A ⟶ X) (g : A ⟶ Y) (y : Y) :
    pushoutSumDesc f g (Sum.inr y) = pushout.inr f g y := rfl

/-- A topological pushout carries the quotient topology induced from the disjoint union of its
two summands. -/
theorem pushoutSumDesc_isQuotientMap (f : A ⟶ X) (g : A ⟶ Y) :
    IsQuotientMap (pushoutSumDesc f g) := by
  rw [isQuotientMap_iff]
  constructor
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    rw [isOpen_sum_iff]
    constructor
    · rintro ⟨hX, hY⟩
      refine (TopCat.isOpen_iff_of_isColimit _ (pushoutIsPushout f g) U).2 ?_
      rintro (_ | _ | _)
      · exact hX.preimage f.hom.continuous
      · exact hX
      · exact hY
    · intro hU
      exact ⟨hU.preimage (pushout.inl f g).hom.continuous,
        hU.preimage (pushout.inr f g).hom.continuous⟩
  · have hpo := (IsPushout.of_isColimit (pushoutIsPushout f g)).map (forget TopCat)
    intro z
    rcases Types.eq_or_eq_of_isPushout hpo z with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr y, hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equality between two points in the left summand of an arbitrary pushout cocone in
`Type`.  Apart from equality in the summand itself, such points can only be identified by
two elements of the gluing space with the same image in the right summand. -/
theorem pushoutCocone_inl_eq_inl_iff_of_isColimit
    {S X₁ X₂ : Type u} {f : S ⟶ X₁} {g : S ⟶ X₂}
    {c : PushoutCocone f g} (hc : IsColimit c)
    (hf : Function.Injective f) (x y : X₁) :
    c.inl x = c.inl y ↔ x = y ∨
      ∃ (s t : S) (_ : g s = g t), x = f s ∧ y = f t := by
  let e : c ≅ Types.Pushout.cocone f g := Cocone.ext
    (IsColimit.coconePointUniqueUpToIso hc (Types.Pushout.isColimitCocone f g)) (by simp)
  haveI : Mono f := (mono_iff_injective f).mpr hf
  constructor
  · intro h
    have hcanon :
        (Types.Pushout.cocone f g).inl x = (Types.Pushout.cocone f g).inl y := by
      convert! congr_arg e.hom.hom h
      · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm x
      · exact ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm y
    change (Quot.mk _ (Sum.inl x) : Types.Pushout f g) =
      Quot.mk _ (Sum.inl y) at hcanon
    rw [Types.Pushout.quot_mk_eq_iff, Types.Pushout.inl_rel'_inl_iff] at hcanon
    exact hcanon
  · intro h
    have hcanon :
        (Types.Pushout.cocone f g).inl x = (Types.Pushout.cocone f g).inl y := by
      change (Quot.mk _ (Sum.inl x) : Types.Pushout f g) =
        Quot.mk _ (Sum.inl y)
      rw [Types.Pushout.quot_mk_eq_iff, Types.Pushout.inl_rel'_inl_iff]
      exact h
    convert! congr_arg e.inv.hom hcanon

/-- The left structure map of a topological pushout is a monomorphism when the right leg is. -/
instance mono_pushout_inl_topCat (f : A ⟶ X) (g : A ⟶ Y) [Mono g] :
    Mono (pushout.inl f g) := by
  rw [TopCat.mono_iff_injective]
  have h := ((IsPushout.of_isColimit (pushoutIsPushout f g)).flip.map (forget TopCat))
  have hg : Function.Injective g := (TopCat.mono_iff_injective _).mp inferInstance
  exact Types.pushoutCocone_inr_injective_of_isColimit h.isColimit (by simpa using hg)

/-- The right structure map of a topological pushout is a monomorphism when the left leg is. -/
instance mono_pushout_inr_topCat (f : A ⟶ X) (g : A ⟶ Y) [Mono f] :
    Mono (pushout.inr f g) := by
  rw [TopCat.mono_iff_injective]
  have h := (IsPushout.of_isColimit (pushoutIsPushout f g)).map (forget TopCat)
  have hf : Function.Injective f := (TopCat.mono_iff_injective _).mp inferInstance
  exact Types.pushoutCocone_inr_injective_of_isColimit h.isColimit (by simpa using hf)

end Submission
