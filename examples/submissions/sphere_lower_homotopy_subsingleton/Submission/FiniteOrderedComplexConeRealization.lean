/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierHomeomorph

/-!
# Realization of finite simplicial cones

Coning every facet of a finite complex by one vertex has the same affine carrier as the radial
cone from that vertex to the original facet-family carrier.  Combining this set-level identity
with the general realization/carrier homeomorphism identifies the realization of the finite
simplicial cone with the abstract topological cone on the original realization.

## Main results

* `facetFamilyCarrier_cone_eq_affineConeCarrier`: equality of the coned and radial affine
  carriers;
* `conedOrderedRealizationHomeomorphTopologicalCone`: the exact finite/abstract cone comparison.
-/

noncomputable section

open scoped Topology TopCat

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The affine carrier obtained by inserting an apex in every facet is exactly the radial affine
cone on the original carrier. -/
theorem facetFamilyCarrier_cone_eq_affineConeCarrier
    (facets : Finset (Finset V)) (apex : V)
    (hfacets : ∃ facet ∈ facets, facet.Nonempty) :
    facetFamilyCarrier (facets.image (fun facet ↦ insert apex facet)) =
      {x : stdSimplex ℝ V |
        ∃ a : facetFamilyCarrier facets, ∃ t : TopCat.I.{0},
          x = affineConePoint (facetFamilyCarrier facets) apex a t} := by
  ext x
  constructor
  · intro hx
    obtain ⟨coneFacet, hconeFacet, hxsupport⟩ :=
      (mem_facetFamilyCarrier_iff _ x).mp hx
    obtain ⟨facet, hfacet, rfl⟩ := Finset.mem_image.mp hconeFacet
    let r : ℝ := x apex
    have hr0 : 0 ≤ r := x.2.1 apex
    have hr1 : r ≤ 1 := stdSimplex.le_one x apex
    by_cases hr : r = 1
    · let a : facetFamilyCarrier facets :=
        ⟨(facetFamilyCarrier_nonempty facets hfacets).choose,
          (facetFamilyCarrier_nonempty facets hfacets).choose_spec⟩
      let t : TopCat.I.{0} := 1
      refine ⟨a, t, ?_⟩
      apply Subtype.ext
      rw [affineConePoint_one]
      funext v
      by_cases hv : v = apex
      · subst v
        change x apex = (Pi.single apex (1 : ℝ) : V → ℝ) apex
        rw [Pi.single_eq_same]
        exact hr
      · change x v = (Pi.single apex (1 : ℝ) : V → ℝ) v
        rw [Pi.single_eq_of_ne hv]
        have hsumErase : ∑ w ∈ Finset.univ.erase apex, x w = 0 := by
          have htotal : (∑ w, x w) = 1 := x.2.2
          have herase := Finset.sum_erase_add Finset.univ x
            (Finset.mem_univ apex)
          linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun w _ ↦ x.2.1 w)).mp hsumErase v
            (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 hr
      have hdenom : 0 < 1 - r := sub_pos.mpr hrlt
      let av : V → ℝ := fun v ↦ if v = apex then 0 else x v / (1 - r)
      have havnonneg : ∀ v, 0 ≤ av v := by
        intro v
        dsimp [av]
        split_ifs
        · exact le_rfl
        · exact div_nonneg (x.2.1 v) hdenom.le
      have hsumErase : ∑ v ∈ Finset.univ.erase apex, x v = 1 - r := by
        have herase := Finset.sum_erase_add Finset.univ x
          (Finset.mem_univ apex)
        have htotal : (∑ v, x v) = 1 := x.2.2
        linarith
      have havsum : ∑ v, av v = 1 := by
        rw [← Finset.sum_erase_add Finset.univ av (Finset.mem_univ apex)]
        have hapexzero : av apex = 0 := by simp [av]
        rw [hapexzero, add_zero]
        simp_rw [av]
        rw [Finset.sum_congr rfl (fun v hv ↦ if_neg (Finset.ne_of_mem_erase hv))]
        rw [← Finset.sum_div, hsumErase]
        exact div_self (ne_of_gt hdenom)
      let aPoint : stdSimplex ℝ V := ⟨av, havnonneg, havsum⟩
      have hasupport : ∀ v, v ∉ facet → aPoint v = 0 := by
        intro v hv
        change av v = 0
        dsimp [av]
        by_cases hva : v = apex
        · simp [hva]
        · rw [if_neg hva]
          rw [hxsupport v]
          · exact zero_div _
          · simp [hva, hv]
      let a : facetFamilyCarrier facets :=
        ⟨aPoint, (mem_facetFamilyCarrier_iff facets aPoint).mpr
          ⟨facet, hfacet, hasupport⟩⟩
      let t : TopCat.I.{0} := TopCat.I.homeomorph.symm ⟨r, hr0, hr1⟩
      refine ⟨a, t, ?_⟩
      apply Subtype.ext
      funext v
      symm
      change affineConePoint (facetFamilyCarrier facets) apex a t v = x v
      rw [affineConePoint_apply]
      change (1 - r) * av v + r * (stdSimplex.vertex apex : V → ℝ) v = x v
      by_cases hv : v = apex
      · subst v
        simp [av, stdSimplex.vertex_coe, Pi.single_eq_same, r]
      · rw [show av v = x v / (1 - r) by simp [av, hv]]
        rw [stdSimplex.vertex_coe, Pi.single_eq_of_ne hv, mul_zero, add_zero]
        exact mul_div_cancel₀ (x v) (ne_of_gt hdenom)
  · rintro ⟨a, t, rfl⟩
    obtain ⟨facet, hfacet, hasupport⟩ :=
      (mem_facetFamilyCarrier_iff facets a.1).mp a.2
    rw [mem_facetFamilyCarrier_iff]
    refine ⟨insert apex facet, Finset.mem_image.mpr ⟨facet, hfacet, rfl⟩, ?_⟩
    intro v hv
    rw [affineConePoint_apply]
    have hvapex : v ≠ apex := fun h ↦ hv (h ▸ Finset.mem_insert_self _ _)
    have hvfacet : v ∉ facet := fun h ↦ hv (Finset.mem_insert_of_mem h)
    rw [hasupport v hvfacet, stdSimplex.vertex_coe,
      Pi.single_eq_of_ne hvapex, mul_zero, mul_zero, add_zero]

/-- The coned facet-family carrier is homeomorphic to the radial affine-cone carrier. -/
def facetFamilyConeCarrierHomeomorph
    (facets : Finset (Finset V)) (apex : V)
    (hfacets : ∃ facet ∈ facets, facet.Nonempty) :
    facetFamilyCarrier (facets.image (fun facet ↦ insert apex facet)) ≃ₜ
      affineConeCarrier (facetFamilyCarrier facets) apex :=
  Homeomorph.setCongr
    (facetFamilyCarrier_cone_eq_affineConeCarrier facets apex hfacets)

/-- The realization of a finite facetwise cone is homeomorphic to the abstract topological cone
on the realization of its base. -/
def conedOrderedRealizationHomeomorphTopologicalCone
    [LinearOrder V] (facets : Finset (Finset V)) (apex : V)
    (hapex : ∀ facet ∈ facets, apex ∉ facet)
    (hfacets : ∃ facet ∈ facets, facet.Nonempty) :
    SSet.toTop.obj
        (orderedSSet (facets.image (fun facet ↦ insert apex facet))) ≃ₜ
      topologicalCone (SSet.toTop.obj (orderedSSet facets)) :=
  (orderedRealizationHomeomorphFacetFamilyCarrier
      (facets.image (fun facet ↦ insert apex facet))).trans
    ((facetFamilyConeCarrierHomeomorph facets apex hfacets).trans
      ((affineTopologicalConeHomeomorphCarrier
        (facetFamilyCarrier facets) apex
          (facetFamilyCarrier_apex_eq_zero facets apex hapex)
          (facetFamilyCarrier_nonempty facets hfacets)).symm.trans
        (TopCat.homeoOfIso (topologicalConeIso
          (TopCat.isoOfHomeo
            (orderedRealizationHomeomorphFacetFamilyCarrier facets))).symm)))

end Submission.FiniteOrderedComplex
