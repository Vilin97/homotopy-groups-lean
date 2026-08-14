/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarAffineHomeomorphism
import Submission.SelectedFacesOrderedRealization

/-!
# Local realization invariance for a bistellar replacement

This file transports the explicit affine bistellar homeomorphism to selected face carriers and
then to finite ordered simplicial-set realizations.  A disjoint cover `A ∪ B = univ` identifies the
ambient vertices with the sum of the two core subtypes.  Under that coordinate equivalence, the
old local ball is the union of faces omitting vertices of `B`, and the new local ball is the union
of faces omitting vertices of `A`.

The resulting homeomorphism fixes the common affine boundary pointwise.  This is the concrete
local input for the global pushout gluing theorem; transporting the facewise fixed formula through
the ordered realization comparison is the remaining compatibility step.

## Main results

* `Submission.FiniteOrderedComplex.finsetFaceCarrierBistellarHomeomorph` and its pointwise fixed
  boundary theorem;
* `Submission.FiniteOrderedComplex.selectedFacesOrderedBistellarHomeomorph`;
* `Submission.FiniteOrderedComplex.bistellarLocalOrderedRealizationHomeomorph`.
-/

noncomputable section

open scoped BigOperators

namespace Submission.FiniteOrderedComplex

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- A disjoint cover identifies the sum of the two subtypes with the ambient finite type. -/
def finsetSumEquivOfDisjointUnion (A B : Finset γ) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) : (↥A ⊕ ↥B) ≃ γ where
  toFun
    | Sum.inl a => a.1
    | Sum.inr b => b.1
  invFun x := if hx : x ∈ A then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, by
    have hxUnion : x ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ x
    exact (Finset.mem_union.mp hxUnion).resolve_left hx⟩
  left_inv x := by
    cases x with
    | inl a => simp [a.2]
    | inr b =>
        have hbA : b.1 ∉ A := fun hbA => (Finset.disjoint_left.mp hdisj) hbA b.2
        simp [hbA]
  right_inv x := by
    by_cases hx : x ∈ A <;> simp [hx]

@[simp]
theorem finsetSumEquivOfDisjointUnion_inl (A B : Finset γ) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) (a : A) :
    finsetSumEquivOfDisjointUnion A B hdisj hcover (Sum.inl a) = a.1 := rfl

@[simp]
theorem finsetSumEquivOfDisjointUnion_inr (A B : Finset γ) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) (b : B) :
    finsetSumEquivOfDisjointUnion A B hdisj hcover (Sum.inr b) = b.1 := rfl

@[simp]
theorem finsetSumEquivOfDisjointUnion_symm_apply_left
    (A B : Finset γ) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) (a : γ) (ha : a ∈ A) :
    (finsetSumEquivOfDisjointUnion A B hdisj hcover).symm a =
      Sum.inl ⟨a, ha⟩ := by
  simp [finsetSumEquivOfDisjointUnion, ha]

@[simp]
theorem finsetSumEquivOfDisjointUnion_symm_apply_right
    (A B : Finset γ) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) (b : γ) (hb : b ∈ B) :
    (finsetSumEquivOfDisjointUnion A B hdisj hcover).symm b =
      Sum.inr ⟨b, hb⟩ := by
  have hbA : b ∉ A := fun hbA => (Finset.disjoint_left.mp hdisj) hbA hb
  simp [finsetSumEquivOfDisjointUnion, hbA]

/-- Reindexing barycentric coordinates along an equivalence is a homeomorphism of standard
simplices. -/
def stdSimplexEquivHomeomorph {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : stdSimplex ℝ α ≃ₜ stdSimplex ℝ β where
  toFun := stdSimplex.map e
  invFun := stdSimplex.map e.symm
  left_inv x := by
    rw [stdSimplex.map_comp_apply]
    rw [e.symm_comp_self, stdSimplex.map_id_apply]
  right_inv x := by
    rw [stdSimplex.map_comp_apply]
    rw [e.self_comp_symm, stdSimplex.map_id_apply]
  continuous_toFun := stdSimplex.continuous_map e
  continuous_invFun := stdSimplex.continuous_map e.symm

@[simp]
theorem stdSimplexEquivHomeomorph_apply_apply {α β : Type*}
    [Fintype α] [Fintype β] (e : α ≃ β) (x : stdSimplex ℝ α) (b : β) :
    stdSimplexEquivHomeomorph e x b = x (e.symm b) := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ e x) b = _
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_single (e.symm b)
  · intro a ha hne
    rw [Finset.mem_filter] at ha
    exact False.elim (hne (e.injective (ha.2.trans (e.apply_symm_apply b).symm)))
  · intro hnot
    apply False.elim
    apply hnot
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, e.apply_symm_apply b⟩

/-- Points of a standard simplex with a vanishing coordinate selected by `I`. -/
abbrev finsetFaceCarrier (I : Finset γ) : Type _ :=
  {x : stdSimplex ℝ γ // ∃ i : I, x.1 i.1 = 0}

/-- Reindex the old affine bistellar carrier into the ambient finite type. -/
def affineBistellarOldToRightCarrier (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (x : affineBistellarOld A B) : finsetFaceCarrier B :=
  ⟨stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover) x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b, ?_⟩
    change stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover) x.1 b.1 = 0
    rw [stdSimplexEquivHomeomorph_apply_apply,
      finsetSumEquivOfDisjointUnion_symm_apply_right A B hdisj hcover b.1 b.2]
    exact hb⟩

/-- Reindex the right selected-face carrier back to the old affine model. -/
def rightCarrierToAffineBistellarOld (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (x : finsetFaceCarrier B) : affineBistellarOld A B :=
  ⟨(stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).symm x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b, ?_⟩
    change stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover).symm x.1 (Sum.inr b) = 0
    rw [stdSimplexEquivHomeomorph_apply_apply]
    exact hb⟩

/-- After reindexing a disjoint cover, the old affine bistellar carrier is the union of faces
selected by the right finset. -/
def affineBistellarOldHomeomorphRightCarrier (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ) :
    affineBistellarOld A B ≃ₜ finsetFaceCarrier B where
  toFun := affineBistellarOldToRightCarrier A B hdisj hcover
  invFun := rightCarrierToAffineBistellarOld A B hdisj hcover
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).right_inv x.1
  continuous_toFun := Continuous.subtype_mk
    ((stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).continuous.comp
        continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).symm.continuous.comp
        continuous_subtype_val) _

/-- Reindex the new affine bistellar carrier into the ambient finite type. -/
def affineBistellarNewToLeftCarrier (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (x : affineBistellarNew A B) : finsetFaceCarrier A :=
  ⟨stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover) x.1, by
    obtain ⟨a, ha⟩ := x.2
    refine ⟨a, ?_⟩
    change stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover) x.1 a.1 = 0
    rw [stdSimplexEquivHomeomorph_apply_apply,
      finsetSumEquivOfDisjointUnion_symm_apply_left A B hdisj hcover a.1 a.2]
    exact ha⟩

/-- Reindex the left selected-face carrier back to the new affine model. -/
def leftCarrierToAffineBistellarNew (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (x : finsetFaceCarrier A) : affineBistellarNew A B :=
  ⟨(stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).symm x.1, by
    obtain ⟨a, ha⟩ := x.2
    refine ⟨a, ?_⟩
    change stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover).symm x.1 (Sum.inl a) = 0
    rw [stdSimplexEquivHomeomorph_apply_apply]
    exact ha⟩

/-- After reindexing a disjoint cover, the new affine bistellar carrier is the union of faces
selected by the left finset. -/
def affineBistellarNewHomeomorphLeftCarrier (A B : Finset γ)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ) :
    affineBistellarNew A B ≃ₜ finsetFaceCarrier A where
  toFun := affineBistellarNewToLeftCarrier A B hdisj hcover
  invFun := leftCarrierToAffineBistellarNew A B hdisj hcover
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).right_inv x.1
  continuous_toFun := Continuous.subtype_mk
    ((stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).continuous.comp
        continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((stdSimplexEquivHomeomorph
      (finsetSumEquivOfDisjointUnion A B hdisj hcover)).symm.continuous.comp
        continuous_subtype_val) _

/-- The two selected affine face unions of a nontrivial partition are homeomorphic. -/
def finsetFaceCarrierBistellarHomeomorph (A B : Finset γ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    finsetFaceCarrier B ≃ₜ finsetFaceCarrier A := by
  letI : Nonempty A := hA.to_subtype
  letI : Nonempty B := hB.to_subtype
  exact (affineBistellarOldHomeomorphRightCarrier A B hdisj hcover).symm.trans
    ((affineBistellarHomeomorph A B).trans
      (affineBistellarNewHomeomorphLeftCarrier A B hdisj hcover))

/-- The selected-face bistellar homeomorphism fixes the common boundary pointwise. -/
theorem finsetFaceCarrierBistellarHomeomorph_fixed
    (A B : Finset γ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisj : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (x : finsetFaceCarrier B) (a : A) (ha : x.1 a.1 = 0) :
    (finsetFaceCarrierBistellarHomeomorph A B hA hB hdisj hcover x).1 = x.1 := by
  letI : Nonempty A := hA.to_subtype
  letI : Nonempty B := hB.to_subtype
  let e := finsetSumEquivOfDisjointUnion A B hdisj hcover
  let eOld := affineBistellarOldHomeomorphRightCarrier A B hdisj hcover
  let xOld : affineBistellarOld A B := eOld.symm x
  have hleft : xOld.1 (Sum.inl a) = 0 := by
    change stdSimplexEquivHomeomorph e.symm x.1 (Sum.inl a) = 0
    rw [stdSimplexEquivHomeomorph_apply_apply]
    change x.1 (e (Sum.inl a)) = 0
    rw [finsetSumEquivOfDisjointUnion_inl]
    exact ha
  have hfix := affineBistellarHomeomorph_fixed_of_left_zero A B xOld a hleft
  change stdSimplexEquivHomeomorph e
      (affineBistellarHomeomorph A B xOld).1 = x.1
  rw [hfix]
  exact congrArg Subtype.val (eOld.apply_symm_apply x)

/-- The ordered realizations of the two selected face unions of a partition are homeomorphic. -/
def selectedFacesOrderedBistellarHomeomorph {n : ℕ}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    SSet.toTop.obj (orderedSSet (selectedFaceFacets B)) ≃ₜ
      SSet.toTop.obj (orderedSSet (selectedFaceFacets A)) :=
  (selectedFacesOrderedRealizationHomeomorphCarrier B).trans
    ((finsetFaceCarrierBistellarHomeomorph A B hA hB hdisj hcover).trans
      (selectedFacesOrderedRealizationHomeomorphCarrier A).symm)

/-- Under a disjoint full cover, the old bistellar facets are precisely the faces selected by the
right core. -/
theorem bistellarOldFacets_eq_selectedFaceFacets {n : ℕ}
    (A B : Finset (Fin (n + 2))) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    bistellarOldFacets A B = selectedFaceFacets B := by
  apply Finset.image_congr
  intro b hb
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (hxA | ⟨hxb, hxB⟩)
    · exact fun hxb => (Finset.disjoint_left.mp hdisj) hxA (hxb ▸ hb)
    · exact hxb
  · intro hxb
    have hxUnion : x ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxUnion with hxA | hxB
    · exact Or.inl hxA
    · exact Or.inr ⟨hxb, hxB⟩

/-- Under a disjoint full cover, the new bistellar facets are precisely the faces selected by the
left core. -/
theorem bistellarNewFacets_eq_selectedFaceFacets {n : ℕ}
    (A B : Finset (Fin (n + 2))) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    bistellarNewFacets A B = selectedFaceFacets A := by
  apply Finset.image_congr
  intro a ha
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (⟨hxa, hxA⟩ | hxB)
    · exact hxa
    · exact fun hxa => (Finset.disjoint_left.mp hdisj) (hxa ▸ ha) hxB
  · intro hxa
    have hxUnion : x ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hxUnion with hxA | hxB
    · exact Or.inl ⟨hxa, hxA⟩
    · exact Or.inr hxB

/-- A bistellar replacement on the full finite vertex set preserves the homeomorphism type of its
local ordered realization. -/
def bistellarLocalOrderedRealizationHomeomorph {n : ℕ}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≃ₜ
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)) := by
  rw [bistellarOldFacets_eq_selectedFaceFacets A B hdisj hcover,
    bistellarNewFacets_eq_selectedFaceFacets A B hdisj hcover]
  exact selectedFacesOrderedBistellarHomeomorph A B hA hB hdisj hcover

end Submission.FiniteOrderedComplex
