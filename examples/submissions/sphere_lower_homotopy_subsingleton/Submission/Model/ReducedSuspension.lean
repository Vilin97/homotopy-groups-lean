/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Reduced suspension of a pointed space

This file defines the reduced suspension of a pointed topological space as the quotient of
`I × X` which identifies both ends of the interval and the meridian through the basepoint.
The quotient map and its basic universal properties are exposed for later constructions on
homotopy groups.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission

open unitInterval

universe u

variable {X : Type u}

/-- The subset of the cylinder collapsed in the reduced suspension. -/
def ReducedSuspCollapsed (x₀ : X) (p : I × X) : Prop :=
  p.1 = 0 ∨ p.1 = 1 ∨ p.2 = x₀

/-- The equivalence relation underlying reduced suspension. -/
def ReducedSuspRel (x₀ : X) (a b : I × X) : Prop :=
  a = b ∨ ReducedSuspCollapsed x₀ a ∧ ReducedSuspCollapsed x₀ b

theorem reducedSuspRel_equivalence (x₀ : X) : Equivalence (ReducedSuspRel x₀) where
  refl _ := Or.inl rfl
  symm := by
    intro a b h
    rcases h with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hb, ha⟩
  trans := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨ha, hb⟩
    · exact hbc
    · rcases hbc with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩

/-- The setoid on the cylinder whose quotient is reduced suspension. -/
def reducedSuspSetoid (x₀ : X) : Setoid (I × X) :=
  ⟨ReducedSuspRel x₀, reducedSuspRel_equivalence x₀⟩

/-- The reduced suspension of the pointed space `(X, x₀)`. -/
def ReducedSusp (X : Type u) [TopologicalSpace X] (x₀ : X) : Type u :=
  Quotient (reducedSuspSetoid x₀)

variable [TopologicalSpace X]

instance instTopologicalSpaceReducedSusp (x₀ : X) : TopologicalSpace (ReducedSusp X x₀) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

namespace ReducedSusp

variable {x₀ : X}

/-- The quotient map from the cylinder to reduced suspension. -/
def mk (x₀ : X) : C(I × X, ReducedSusp X x₀) :=
  ⟨fun p => Quotient.mk (reducedSuspSetoid x₀) p, continuous_quot_mk⟩

/-- The distinguished point of reduced suspension. -/
def base (x₀ : X) : ReducedSusp X x₀ :=
  mk x₀ (0, x₀)

theorem mk_eq_base_of_collapsed (x₀ : X) {p : I × X}
    (hp : ReducedSuspCollapsed x₀ p) : mk x₀ p = base x₀ := by
  apply Quotient.sound
  exact Or.inr ⟨hp, Or.inl rfl⟩

@[simp]
theorem mk_zero (x₀ x : X) : mk x₀ (0, x) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inl rfl)

@[simp]
theorem mk_one (x₀ x : X) : mk x₀ (1, x) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inr (Or.inl rfl))

@[simp]
theorem mk_base (x₀ : X) (t : I) : mk x₀ (t, x₀) = base x₀ :=
  mk_eq_base_of_collapsed x₀ (Or.inr (Or.inr rfl))

theorem mk_surjective (x₀ : X) : Function.Surjective (mk x₀ : I × X → ReducedSusp X x₀) :=
  Quotient.mk_surjective

theorem isQuotientMap_mk (x₀ : X) :
    Topology.IsQuotientMap (mk x₀ : I × X → ReducedSusp X x₀) :=
  isQuotientMap_quot_mk

theorem mk_eq_mk (x₀ : X) {a b : I × X} :
    mk x₀ a = mk x₀ b ↔ ReducedSuspRel x₀ a b :=
  Quotient.eq_iff_equiv

@[elab_as_elim]
theorem ind (x₀ : X) {motive : ReducedSusp X x₀ → Prop}
    (h : ∀ p : I × X, motive (mk x₀ p)) (q : ReducedSusp X x₀) : motive q :=
  Quotient.ind h q

instance instCompactSpace [CompactSpace X] : CompactSpace (ReducedSusp X x₀) :=
  Quotient.compactSpace

theorem preimage_image_mk_of_collapsed_subset (x₀ : X) (U : Set (I × X))
    (hU : {p | ReducedSuspCollapsed x₀ p} ⊆ U) :
    (mk x₀ : I × X → ReducedSusp X x₀) ⁻¹' (mk x₀ '' U) = U := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    rcases (mk_eq_mk x₀).mp hpq with h | ⟨_, hp⟩
    · simpa [h] using hq
    · exact hU hp
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem preimage_image_mk_of_disjoint_collapsed (x₀ : X) (U : Set (I × X))
    (hU : Disjoint U {p | ReducedSuspCollapsed x₀ p}) :
    (mk x₀ : I × X → ReducedSusp X x₀) ⁻¹' (mk x₀ '' U) = U := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    rcases (mk_eq_mk x₀).mp hpq with h | ⟨hq', _⟩
    · simpa [h] using hq
    · exact (Set.disjoint_left.mp hU hq hq').elim
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Reduced suspension is Hausdorff when its source is compact Hausdorff. -/
instance instT2Space [T2Space X] [CompactSpace X] : T2Space (ReducedSusp X x₀) := by
  let A : Set (I × X) := {p | ReducedSuspCollapsed x₀ p}
  have hA : IsClosed A := by
    dsimp [A, ReducedSuspCollapsed]
    exact (isClosed_eq continuous_fst continuous_const).union
      ((isClosed_eq continuous_fst continuous_const).union
        (isClosed_eq continuous_snd continuous_const))
  refine ⟨fun q q' hne => ?_⟩
  induction q using ind x₀ with
  | h p =>
    induction q' using ind x₀ with
    | h p' =>
      have hpp' : p ≠ p' := fun h => hne (congrArg (mk x₀) h)
      by_cases hp'A : p' ∈ A
      · have hpA : p ∉ A := by
          intro hpA
          apply hne
          apply (mk_eq_mk x₀).mpr
          exact Or.inr ⟨hpA, hp'A⟩
        have hd : Disjoint ({p} : Set (I × X)) A := by
          rw [Set.disjoint_left]
          intro z hz hza
          exact hpA (by simpa using hz ▸ hza)
        obtain ⟨U, V, hU, hV, hpU, hAV, hUV⟩ :=
          normal_separation isClosed_singleton hA hd
        have hUA : Disjoint U A := by
          rw [Set.disjoint_left]
          intro z hzU hzA
          exact Set.disjoint_left.mp hUV hzU (hAV hzA)
        refine ⟨mk x₀ '' U, mk x₀ '' V, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← (isQuotientMap_mk x₀).isCoinducing.isOpen_preimage,
            preimage_image_mk_of_disjoint_collapsed x₀ U hUA]
          exact hU
        · rw [← (isQuotientMap_mk x₀).isCoinducing.isOpen_preimage,
            preimage_image_mk_of_collapsed_subset x₀ V hAV]
          exact hV
        · exact ⟨p, hpU (Set.mem_singleton p), rfl⟩
        · exact ⟨p', hAV hp'A, rfl⟩
        · rw [Set.disjoint_left]
          intro z hzU hzV
          induction z using ind x₀ with
          | h r =>
            have hrU : r ∈ U := by
              rw [← preimage_image_mk_of_disjoint_collapsed x₀ U hUA]
              exact hzU
            have hrV : r ∈ V := by
              rw [← preimage_image_mk_of_collapsed_subset x₀ V hAV]
              exact hzV
            exact Set.disjoint_left.mp hUV hrU hrV
      · have hd : Disjoint (A ∪ {p}) ({p'} : Set (I × X)) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          have hz' : z = p' := Set.mem_singleton_iff.mp hz'
          subst z
          rcases hz with hzA | hzP
          · exact hp'A hzA
          · exact hpp' (Set.mem_singleton_iff.mp hzP).symm
        obtain ⟨U, V, hU, hV, hApU, hp'V, hUV⟩ :=
          normal_separation (hA.union isClosed_singleton) isClosed_singleton hd
        have hAU : A ⊆ U := fun z hz => hApU (Or.inl hz)
        have hVA : Disjoint V A := by
          rw [Set.disjoint_left]
          intro z hzV hzA
          exact Set.disjoint_left.mp hUV (hAU hzA) hzV
        refine ⟨mk x₀ '' U, mk x₀ '' V, ?_, ?_, ?_, ?_, ?_⟩
        · rw [← (isQuotientMap_mk x₀).isCoinducing.isOpen_preimage,
            preimage_image_mk_of_collapsed_subset x₀ U hAU]
          exact hU
        · rw [← (isQuotientMap_mk x₀).isCoinducing.isOpen_preimage,
            preimage_image_mk_of_disjoint_collapsed x₀ V hVA]
          exact hV
        · exact ⟨p, hApU (Or.inr (Set.mem_singleton p)), rfl⟩
        · exact ⟨p', hp'V (Set.mem_singleton p'), rfl⟩
        · rw [Set.disjoint_left]
          intro z hzU hzV
          induction z using ind x₀ with
          | h r =>
            have hrU : r ∈ U := by
              rw [← preimage_image_mk_of_collapsed_subset x₀ U hAU]
              exact hzU
            have hrV : r ∈ V := by
              rw [← preimage_image_mk_of_disjoint_collapsed x₀ V hVA]
              exact hzV
            exact Set.disjoint_left.mp hUV hrU hrV

/-- The open-cylinder part of reduced suspension, before taking the one-point compactification. -/
abbrev Punctured (x₀ : X) :=
  {p : I × X // ¬ReducedSuspCollapsed x₀ p}

/-- Embed the open cylinder into reduced suspension. -/
def puncturedMap (x₀ : X) : Punctured x₀ → ReducedSusp X x₀ :=
  fun p => mk x₀ p.1

theorem isOpenEmbedding_puncturedMap [T2Space X] [CompactSpace X] (x₀ : X) :
    Topology.IsOpenEmbedding (puncturedMap x₀) := by
  let A : Set (I × X) := {p | ReducedSuspCollapsed x₀ p}
  have hA : IsClosed A := by
    dsimp [A, ReducedSuspCollapsed]
    exact (isClosed_eq continuous_fst continuous_const).union
      ((isClosed_eq continuous_fst continuous_const).union
        (isClosed_eq continuous_snd continuous_const))
  have hB : IsOpen {p : I × X | ¬ReducedSuspCollapsed x₀ p} := by
    rw [show {p : I × X | ¬ReducedSuspCollapsed x₀ p} = Aᶜ by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, A]]
    exact hA.isOpen_compl
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact (mk x₀).continuous.comp continuous_subtype_val
  · intro p q hpq
    apply Subtype.ext
    rcases (mk_eq_mk x₀).mp hpq with hpq | ⟨hp, _⟩
    · exact hpq
    · exact (p.property hp).elim
  · intro U hU
    let V : Set (I × X) := Subtype.val '' U
    have hV : IsOpen V := by
      apply hB.isOpenMap_subtype_val
      exact hU
    have hVA : Disjoint V A := by
      rw [Set.disjoint_left]
      rintro p ⟨q, hq, rfl⟩ hpA
      exact q.property hpA
    have himage : puncturedMap x₀ '' U = mk x₀ '' V := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨p, ⟨q, hq, hp⟩, rfl⟩
        subst p
        exact ⟨q, hq, rfl⟩
    rw [himage]
    rw [← (isQuotientMap_mk x₀).isCoinducing.isOpen_preimage,
      preimage_image_mk_of_disjoint_collapsed x₀ V hVA]
    exact hV

theorem range_puncturedMap [T2Space X] [CompactSpace X] (x₀ : X) :
    Set.range (puncturedMap x₀) = ({base x₀} : Set (ReducedSusp X x₀))ᶜ := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hp
    change mk x₀ p.1 = mk x₀ (0, x₀) at hp
    rcases (mk_eq_mk x₀).mp hp with hp | ⟨hp, _⟩
    · exact p.property (hp ▸ Or.inl rfl)
    · exact p.property hp
  · intro hq
    induction q using ind x₀ with
    | h p =>
      have hp : ¬ReducedSuspCollapsed x₀ p := by
        intro hp
        exact hq (mk_eq_base_of_collapsed x₀ hp)
      exact ⟨⟨p, hp⟩, rfl⟩

/-- Reduced suspension is the one-point compactification of its open-cylinder locus. -/
noncomputable def onePointHomeomorph [T2Space X] [CompactSpace X] (x₀ : X) :
    OnePoint (Punctured x₀) ≃ₜ ReducedSusp X x₀ :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (base x₀) (puncturedMap x₀)
    (isOpenEmbedding_puncturedMap x₀).isEmbedding (range_puncturedMap x₀)

@[simp]
theorem onePointHomeomorph_symm_base [T2Space X] [CompactSpace X] (x₀ : X) :
    (onePointHomeomorph x₀).symm (base x₀) = OnePoint.infty := by
  apply (onePointHomeomorph x₀).injective
  simp [onePointHomeomorph]

end ReducedSusp

end Submission
