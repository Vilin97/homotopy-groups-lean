/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierFunctorial
import Mathlib.Topology.Homotopy.Equiv

/-!
# Elementary collapses of finite ordered-complex carriers

An elementary simplicial collapse removes a free codimension-one face together with its unique
coface. This file gives a direct barycentric strong deformation retract between the corresponding
finite affine carriers.

The retraction subtracts the minimum coordinate on the free face from each of its vertices and
transfers the removed mass to the opposite vertex. On every other facet one free-face coordinate
is already zero, so the formula is the identity there. A straight-line homotopy remains in each
original supporting facet and packages the collapse as a homotopy equivalence.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped unitInterval Topology Topology.Homotopy

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [LinearOrder V]

def elementaryCollapseSimplex (freeFace : Finset V) (vertex : V) : Finset V :=
  insert vertex freeFace

def elementaryCollapseFacets (facets : Finset (Finset V))
    (freeFace : Finset V) (vertex : V) : Finset (Finset V) :=
  (facets.erase (elementaryCollapseSimplex freeFace vertex)).erase freeFace ∪
    (((elementaryCollapseSimplex freeFace vertex).powersetCard freeFace.card).erase freeFace)

def elementaryCollapseMin (freeFace : Finset V) (hfree : freeFace.Nonempty)
    (x : stdSimplex ℝ V) : ℝ :=
  freeFace.inf' hfree fun v ↦ x v

omit [LinearOrder V] in
theorem elementaryCollapseMin_nonneg (freeFace : Finset V)
    (hfree : freeFace.Nonempty) (x : stdSimplex ℝ V) :
    0 ≤ elementaryCollapseMin freeFace hfree x := by
  apply Finset.le_inf'
  intro v hv
  exact x.2.1 v

omit [LinearOrder V] in
theorem elementaryCollapseMin_le (freeFace : Finset V)
    (hfree : freeFace.Nonempty) (x : stdSimplex ℝ V)
    (v : V) (hv : v ∈ freeFace) :
    elementaryCollapseMin freeFace hfree x ≤ x v :=
  Finset.inf'_le _ hv

omit [LinearOrder V] in
theorem exists_mem_eq_elementaryCollapseMin (freeFace : Finset V)
    (hfree : freeFace.Nonempty) (x : stdSimplex ℝ V) :
    ∃ v ∈ freeFace, x v = elementaryCollapseMin freeFace hfree x := by
  obtain ⟨v, hv, hmin⟩ :=
    Finset.exists_mem_eq_inf' (s := freeFace) hfree fun v ↦ x v
  exact ⟨v, hv, hmin.symm⟩

omit [LinearOrder V] in
theorem elementaryCollapseMin_eq_zero_of_coord_eq_zero
    (freeFace : Finset V) (hfree : freeFace.Nonempty)
    (x : stdSimplex ℝ V) (v : V) (hv : v ∈ freeFace)
    (hxv : x v = 0) :
    elementaryCollapseMin freeFace hfree x = 0 := by
  apply le_antisymm
  · exact (elementaryCollapseMin_le freeFace hfree x v hv).trans_eq hxv
  · exact elementaryCollapseMin_nonneg freeFace hfree x

omit [LinearOrder V] in
theorem continuous_elementaryCollapseMin (freeFace : Finset V)
    (hfree : freeFace.Nonempty) :
    Continuous (elementaryCollapseMin freeFace hfree) := by
  change Continuous (fun x : stdSimplex ℝ V ↦
    freeFace.inf' hfree fun v ↦ x.1 v)
  have hcoord (v : V) : Continuous (fun x : stdSimplex ℝ V ↦ x.1 v) :=
    (continuous_apply v : Continuous (fun f : V → ℝ ↦ f v)).comp
      continuous_subtype_val
  exact Continuous.finset_inf'_apply hfree
    (fun v _ ↦ hcoord v)

def elementaryCollapseCoord (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (x : stdSimplex ℝ V) (w : V) : ℝ :=
  if w = vertex then
    x w + freeFace.card * elementaryCollapseMin freeFace hfree x
  else if w ∈ freeFace then
    x w - elementaryCollapseMin freeFace hfree x
  else x w

theorem elementaryCollapseCoord_nonneg (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (x : stdSimplex ℝ V) (w : V) :
    0 ≤ elementaryCollapseCoord freeFace vertex hfree x w := by
  simp only [elementaryCollapseCoord]
  split_ifs with hw hmem
  · exact add_nonneg (x.2.1 w)
      (mul_nonneg (Nat.cast_nonneg _) (elementaryCollapseMin_nonneg freeFace hfree x))
  · exact sub_nonneg.mpr (elementaryCollapseMin_le freeFace hfree x w hmem)
  · exact x.2.1 w

theorem elementaryCollapseCoord_sum (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (x : stdSimplex ℝ V) :
    ∑ w, elementaryCollapseCoord freeFace vertex hfree x w = 1 := by
  let m := elementaryCollapseMin freeFace hfree x
  have hcoord (w : V) :
      elementaryCollapseCoord freeFace vertex hfree x w =
        x w + (if w = vertex then freeFace.card * m else 0) -
          (if w ∈ freeFace then m else 0) := by
    simp only [elementaryCollapseCoord, m]
    by_cases hw : w = vertex
    · simp [hw, hv]
    · by_cases hmem : w ∈ freeFace <;> simp [hw, hmem]
  calc
    ∑ w, elementaryCollapseCoord freeFace vertex hfree x w =
        ∑ w, (x w + (if w = vertex then freeFace.card * m else 0) -
          (if w ∈ freeFace then m else 0)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hcoord w
    _ = (∑ w, x w) + freeFace.card * m - ∑ w ∈ freeFace, m := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp
    _ = 1 := by simp

def elementaryCollapseSimplexMap (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace) :
    C(stdSimplex ℝ V, stdSimplex ℝ V) where
  toFun x := ⟨elementaryCollapseCoord freeFace vertex hfree x,
    elementaryCollapseCoord_nonneg freeFace vertex hfree x,
    elementaryCollapseCoord_sum freeFace vertex hfree hv x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    simp only [elementaryCollapseCoord]
    split_ifs
    · exact ((continuous_apply w).comp continuous_subtype_val).add
        (continuous_const.mul (continuous_elementaryCollapseMin freeFace hfree))
    · exact ((continuous_apply w).comp continuous_subtype_val).sub
        (continuous_elementaryCollapseMin freeFace hfree)
    · exact (continuous_apply w).comp continuous_subtype_val

theorem elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (x : stdSimplex ℝ V)
    (v : V) (hvfree : v ∈ freeFace) (hxv : x v = 0) :
    elementaryCollapseSimplexMap freeFace vertex hfree hv x = x := by
  have hmin := elementaryCollapseMin_eq_zero_of_coord_eq_zero
    freeFace hfree x v hvfree hxv
  apply stdSimplex.ext
  funext w
  change elementaryCollapseCoord freeFace vertex hfree x w = x w
  simp only [elementaryCollapseCoord, hmin, mul_zero, add_zero, sub_zero]
  split_ifs <;> rfl

theorem elementaryCollapseSimplexMap_supported_on_simplex
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (x : stdSimplex ℝ V)
    (hx : x ∈ simplexFaceCarrier (elementaryCollapseSimplex freeFace vertex)) :
    elementaryCollapseSimplexMap freeFace vertex hfree hv x ∈
      simplexFaceCarrier (elementaryCollapseSimplex freeFace vertex) := by
  intro w hw
  have hwvertex : w ≠ vertex := by
    intro h
    exact hw (h ▸ Finset.mem_insert_self vertex freeFace)
  have hwfree : w ∉ freeFace := by
    intro h
    exact hw (Finset.mem_insert_of_mem h)
  change elementaryCollapseCoord freeFace vertex hfree x w = 0
  simp only [elementaryCollapseCoord, if_neg hwvertex, if_neg hwfree]
  exact hx w hw

theorem elementaryCollapseSimplexMap_has_zero_free_coord
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (x : stdSimplex ℝ V) :
    ∃ v ∈ freeFace,
      elementaryCollapseSimplexMap freeFace vertex hfree hv x v = 0 := by
  obtain ⟨v, hvfree, hmin⟩ :=
    exists_mem_eq_elementaryCollapseMin freeFace hfree x
  refine ⟨v, hvfree, ?_⟩
  have hvvertex : v ≠ vertex := fun h ↦ hv (h ▸ hvfree)
  change elementaryCollapseCoord freeFace vertex hfree x v = 0
  simp only [elementaryCollapseCoord, if_neg hvvertex, if_pos hvfree]
  exact sub_eq_zero.mpr hmin

omit [Fintype V] in
theorem erase_free_vertex_mem_elementaryCollapseFacets
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hv : vertex ∉ freeFace) (u : V) (hu : u ∈ freeFace) :
    (elementaryCollapseSimplex freeFace vertex).erase u ∈
      elementaryCollapseFacets facets freeFace vertex := by
  apply Finset.mem_union_right
  apply Finset.mem_erase.mpr
  constructor
  · intro h
    apply hv
    rw [← h]
    have hvu : vertex ≠ u := by
      intro hvu
      apply hv
      rw [hvu]
      exact hu
    simp [elementaryCollapseSimplex, hvu]
  · apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.erase_subset _ _
    · simp [elementaryCollapseSimplex, hv, hu]

omit [Fintype V] in
theorem facetFamilyLE_elementaryCollapseFacets
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets) :
    FacetFamilyLE (elementaryCollapseFacets facets freeFace vertex) facets := by
  intro facet hfacet
  rw [elementaryCollapseFacets, Finset.mem_union] at hfacet
  rcases hfacet with hfacet | hfacet
  · exact ⟨facet, (Finset.mem_erase.mp (Finset.mem_erase.mp hfacet).2).2,
      Finset.Subset.rfl⟩
  · rw [Finset.mem_erase] at hfacet
    exact ⟨elementaryCollapseSimplex freeFace vertex, hsimplex,
      (Finset.mem_powersetCard.mp hfacet.2).1⟩

theorem elementaryCollapseSimplexMap_mem_carrier
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (x : stdSimplex ℝ V) (hx : x ∈ facetFamilyCarrier facets) :
    elementaryCollapseSimplexMap freeFace vertex hfree hv x ∈
      facetFamilyCarrier (elementaryCollapseFacets facets freeFace vertex) := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff facets x).mp hx
  by_cases hcontains : freeFace ⊆ facet
  · have hfacetEq := hunique facet hfacet hcontains
    have hfacetSubset : facet ⊆
        elementaryCollapseSimplex freeFace vertex := by
      rcases hfacetEq with hfacetEq | hfacetEq
      · rw [hfacetEq]
        exact Finset.subset_insert vertex freeFace
      · rw [hfacetEq]
    have hsimplexSupport : x ∈
        simplexFaceCarrier (elementaryCollapseSimplex freeFace vertex) := by
      intro w hw
      exact hsupport w (fun hwfacet ↦ hw (hfacetSubset hwfacet))
    have houtSupport := elementaryCollapseSimplexMap_supported_on_simplex
      freeFace vertex hfree hv x hsimplexSupport
    obtain ⟨u, hufree, hzero⟩ :=
      elementaryCollapseSimplexMap_has_zero_free_coord
        freeFace vertex hfree hv x
    refine (mem_facetFamilyCarrier_iff _ _).mpr
      ⟨(elementaryCollapseSimplex freeFace vertex).erase u,
        erase_free_vertex_mem_elementaryCollapseFacets
          facets freeFace vertex hv u hufree, ?_⟩
    intro w hw
    by_cases hwsimplex : w ∈ elementaryCollapseSimplex freeFace vertex
    · have hwu : w = u := by
        by_contra hne
        exact hw (Finset.mem_erase.mpr ⟨hne, hwsimplex⟩)
      exact hwu ▸ hzero
    · exact houtSupport w hwsimplex
  · obtain ⟨u, hufree, hunotmem⟩ := Finset.not_subset.mp hcontains
    have hxzero : x u = 0 := hsupport u hunotmem
    have hmapEq := elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
      freeFace vertex hfree hv x u hufree hxzero
    have hfacetNe : facet ≠ elementaryCollapseSimplex freeFace vertex := by
      intro h
      apply hcontains
      intro w hw
      rw [h]
      exact Finset.mem_insert_of_mem hw
    have hfacetNeFree : facet ≠ freeFace := by
      intro h
      apply hcontains
      rw [h]
    refine (mem_facetFamilyCarrier_iff _ _).mpr
      ⟨facet, Finset.mem_union_left _
        (Finset.mem_erase.mpr
          ⟨hfacetNeFree, Finset.mem_erase.mpr ⟨hfacetNe, hfacet⟩⟩), ?_⟩
    intro w hw
    rw [hmapEq]
    exact hsupport w hw

def elementaryCollapseCarrierMap
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex) :
    C(facetFamilyCarrier facets,
      facetFamilyCarrier (elementaryCollapseFacets facets freeFace vertex)) where
  toFun x := ⟨elementaryCollapseSimplexMap freeFace vertex hfree hv x.1,
    elementaryCollapseSimplexMap_mem_carrier
      facets freeFace vertex hfree hv hunique x.1 x.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((elementaryCollapseSimplexMap freeFace vertex hfree hv).continuous.comp
      continuous_subtype_val) _

theorem exists_free_coord_eq_zero_of_mem_elementaryCollapseCarrier
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (x : stdSimplex ℝ V)
    (hx : x ∈ facetFamilyCarrier
      (elementaryCollapseFacets facets freeFace vertex)) :
    ∃ u ∈ freeFace, x u = 0 := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff _ x).mp hx
  rw [elementaryCollapseFacets, Finset.mem_union] at hfacet
  rcases hfacet with hfacet | hfacet
  · obtain ⟨hfacetNeFree, hfacetErase⟩ := Finset.mem_erase.mp hfacet
    obtain ⟨hfacetNeSimplex, hfacetOld⟩ := Finset.mem_erase.mp hfacetErase
    have hnotSubset : ¬freeFace ⊆ facet := by
      intro hsubset
      rcases hunique facet hfacetOld hsubset with hfacetEq | hfacetEq
      · exact hfacetNeFree hfacetEq
      · exact hfacetNeSimplex hfacetEq
    obtain ⟨u, hufree, hunotmem⟩ := Finset.not_subset.mp hnotSubset
    exact ⟨u, hufree, hsupport u hunotmem⟩
  · rw [Finset.mem_erase] at hfacet
    have hpowerset := Finset.mem_powersetCard.mp hfacet.2
    have hnotSubset : ¬freeFace ⊆ facet := by
      intro hsubset
      apply hfacet.1
      exact (Finset.eq_of_subset_of_card_le hsubset hpowerset.2.le).symm
    obtain ⟨u, hufree, hunotmem⟩ := Finset.not_subset.mp hnotSubset
    exact ⟨u, hufree, hsupport u hunotmem⟩

def elementaryCollapseCarrierIncl
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets) :
    C(facetFamilyCarrier (elementaryCollapseFacets facets freeFace vertex),
      facetFamilyCarrier facets) :=
  ⟨facetFamilyCarrierMapOfFacetFamilyLE
      (facetFamilyLE_elementaryCollapseFacets facets freeFace vertex hsimplex),
    continuous_facetFamilyCarrierMapOfFacetFamilyLE
      (facetFamilyLE_elementaryCollapseFacets facets freeFace vertex hsimplex)⟩

theorem elementaryCollapseCarrierMap_inclusion_apply
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (x : facetFamilyCarrier
      (elementaryCollapseFacets facets freeFace vertex)) :
    elementaryCollapseCarrierMap facets freeFace vertex hfree hv hunique
      (elementaryCollapseCarrierIncl facets freeFace vertex hsimplex x) = x := by
  apply Subtype.ext
  change elementaryCollapseSimplexMap freeFace vertex hfree hv x.1 = x.1
  exact elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
    freeFace vertex hfree hv x.1
    (exists_free_coord_eq_zero_of_mem_elementaryCollapseCarrier
      facets freeFace vertex hunique x.1 x.2).choose
    (exists_free_coord_eq_zero_of_mem_elementaryCollapseCarrier
      facets freeFace vertex hunique x.1 x.2).choose_spec.1
    (exists_free_coord_eq_zero_of_mem_elementaryCollapseCarrier
      facets freeFace vertex hunique x.1 x.2).choose_spec.2

theorem elementaryCollapseSimplexMap_common_support
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (x : stdSimplex ℝ V) (facet : Finset V) (hfacet : facet ∈ facets)
    (hsupport : x ∈ simplexFaceCarrier facet) :
    ∃ support ∈ facets,
      x ∈ simplexFaceCarrier support ∧
        elementaryCollapseSimplexMap freeFace vertex hfree hv x ∈
          simplexFaceCarrier support := by
  by_cases hcontains : freeFace ⊆ facet
  · have hfacetEq := hunique facet hfacet hcontains
    have hfacetSubset : facet ⊆
        elementaryCollapseSimplex freeFace vertex := by
      rcases hfacetEq with hfacetEq | hfacetEq
      · rw [hfacetEq]
        exact Finset.subset_insert vertex freeFace
      · rw [hfacetEq]
    have hsimplexSupport : x ∈
        simplexFaceCarrier (elementaryCollapseSimplex freeFace vertex) := by
      intro w hw
      exact hsupport w (fun hwfacet ↦ hw (hfacetSubset hwfacet))
    exact ⟨elementaryCollapseSimplex freeFace vertex, hsimplex,
      hsimplexSupport,
      elementaryCollapseSimplexMap_supported_on_simplex
        freeFace vertex hfree hv x hsimplexSupport⟩
  · obtain ⟨u, hufree, hunotmem⟩ := Finset.not_subset.mp hcontains
    have hxzero : x u = 0 := hsupport u hunotmem
    refine ⟨facet, hfacet, hsupport, ?_⟩
    rw [elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
      freeFace vertex hfree hv x u hufree hxzero]
    exact hsupport

def elementaryCollapseDeformCoord
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V) (w : V) : ℝ :=
  (1 - (t : ℝ)) *
      elementaryCollapseSimplexMap freeFace vertex hfree hv x w +
    (t : ℝ) * x w

theorem elementaryCollapseDeformCoord_nonneg
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V) (w : V) :
    0 ≤ elementaryCollapseDeformCoord freeFace vertex hfree hv t x w := by
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr t.2.2)
      ((elementaryCollapseSimplexMap freeFace vertex hfree hv x).2.1 w))
    (mul_nonneg t.2.1 (x.2.1 w))

theorem elementaryCollapseDeformCoord_sum
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V) :
    ∑ w, elementaryCollapseDeformCoord freeFace vertex hfree hv t x w = 1 := by
  simp only [elementaryCollapseDeformCoord, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [show (∑ w, elementaryCollapseSimplexMap
      freeFace vertex hfree hv x w) = 1 by
        exact (elementaryCollapseSimplexMap freeFace vertex hfree hv x).2.2]
  rw [show (∑ w, x w) = 1 by exact x.2.2]
  ring

def elementaryCollapseSimplexDeformation
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) :
    C(I × stdSimplex ℝ V, stdSimplex ℝ V) where
  toFun p := ⟨elementaryCollapseDeformCoord
      freeFace vertex hfree hv p.1 p.2,
    elementaryCollapseDeformCoord_nonneg
      freeFace vertex hfree hv p.1 p.2,
    elementaryCollapseDeformCoord_sum
      freeFace vertex hfree hv p.1 p.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    unfold elementaryCollapseDeformCoord
    have ht : Continuous (fun p : I × stdSimplex ℝ V ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : I × stdSimplex ℝ V ↦ p.2 w) :=
      ((continuous_apply w).comp continuous_subtype_val).comp continuous_snd
    have hcollapse : Continuous (fun p : I × stdSimplex ℝ V ↦
        elementaryCollapseSimplexMap freeFace vertex hfree hv p.2 w) :=
      ((continuous_apply w).comp continuous_subtype_val).comp
        ((elementaryCollapseSimplexMap freeFace vertex hfree hv).continuous.comp
          continuous_snd)
    exact ((continuous_const.sub ht).mul hcollapse).add (ht.mul hx)

theorem elementaryCollapseSimplexDeformation_zero
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (x : stdSimplex ℝ V) :
    elementaryCollapseSimplexDeformation freeFace vertex hfree hv (0, x) =
      elementaryCollapseSimplexMap freeFace vertex hfree hv x := by
  apply stdSimplex.ext
  funext w
  change elementaryCollapseDeformCoord freeFace vertex hfree hv 0 x w = _
  simp [elementaryCollapseDeformCoord]

theorem elementaryCollapseSimplexDeformation_one
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (x : stdSimplex ℝ V) :
    elementaryCollapseSimplexDeformation freeFace vertex hfree hv (1, x) = x := by
  apply stdSimplex.ext
  funext w
  change elementaryCollapseDeformCoord freeFace vertex hfree hv 1 x w = _
  simp [elementaryCollapseDeformCoord]

/-- The elementary deformation fixes a point whenever one of its free-face coordinates already
vanishes. -/
theorem elementaryCollapseSimplexDeformation_eq_self_of_coord_eq_zero
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V)
    (u : V) (hu : u ∈ freeFace) (hx : x u = 0) :
    elementaryCollapseSimplexDeformation
        freeFace vertex hfree hv (t, x) = x := by
  have hmap := elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
    freeFace vertex hfree hv x u hu hx
  apply stdSimplex.ext
  funext w
  change (1 - (t : ℝ)) *
        elementaryCollapseSimplexMap freeFace vertex hfree hv x w +
      (t : ℝ) * x w = x w
  rw [hmap]
  ring

/-- The minimum free-face coordinate along the elementary collapse deformation is the original
minimum scaled by the homotopy parameter. -/
theorem elementaryCollapseMin_deformation
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V) :
    elementaryCollapseMin freeFace hfree
        (elementaryCollapseSimplexDeformation
          freeFace vertex hfree hv (t, x)) =
      (t : ℝ) * elementaryCollapseMin freeFace hfree x := by
  let m := elementaryCollapseMin freeFace hfree x
  apply le_antisymm
  · obtain ⟨u, hufree, hu⟩ :=
      exists_mem_eq_elementaryCollapseMin freeFace hfree x
    refine (elementaryCollapseMin_le freeFace hfree _ u hufree).trans_eq ?_
    have huvertex : u ≠ vertex := fun huv ↦ hv (huv ▸ hufree)
    change elementaryCollapseDeformCoord
      freeFace vertex hfree hv t x u = (t : ℝ) * m
    change (1 - (t : ℝ)) *
        elementaryCollapseCoord freeFace vertex hfree x u +
      (t : ℝ) * x u = (t : ℝ) * m
    have hcoord : elementaryCollapseCoord freeFace vertex hfree x u =
        x u - m := by
      simp [elementaryCollapseCoord, huvertex, hufree, m]
    rw [hcoord]
    change x u = m at hu
    rw [hu]
    ring
  · apply Finset.le_inf'
    intro w hw
    have hwvertex : w ≠ vertex := fun hwv ↦ hv (hwv ▸ hw)
    have hmin := elementaryCollapseMin_le freeFace hfree x w hw
    change (t : ℝ) * m ≤
      elementaryCollapseDeformCoord freeFace vertex hfree hv t x w
    change (t : ℝ) * m ≤
      (1 - (t : ℝ)) *
          elementaryCollapseCoord freeFace vertex hfree x w +
        (t : ℝ) * x w
    have hcoord : elementaryCollapseCoord freeFace vertex hfree x w =
        x w - m := by
      simp [elementaryCollapseCoord, hwvertex, hw, m]
    rw [hcoord]
    change m ≤ x w at hmin
    nlinarith [t.2.1, t.2.2]

/-- The elementary retraction is constant along its deformation back to the identity. -/
theorem elementaryCollapseSimplexMap_deformation
    (freeFace : Finset V) (vertex : V) (hfree : freeFace.Nonempty)
    (hv : vertex ∉ freeFace) (t : I) (x : stdSimplex ℝ V) :
    elementaryCollapseSimplexMap freeFace vertex hfree hv
        (elementaryCollapseSimplexDeformation
          freeFace vertex hfree hv (t, x)) =
      elementaryCollapseSimplexMap freeFace vertex hfree hv x := by
  apply stdSimplex.ext
  funext w
  change elementaryCollapseCoord freeFace vertex hfree
      (elementaryCollapseSimplexDeformation
        freeFace vertex hfree hv (t, x)) w =
    elementaryCollapseCoord freeFace vertex hfree x w
  unfold elementaryCollapseCoord
  rw [elementaryCollapseMin_deformation freeFace vertex hfree hv t x]
  by_cases hwv : w = vertex
  · subst w
    simp
    change elementaryCollapseDeformCoord freeFace vertex hfree hv t x vertex +
        freeFace.card * ((t : ℝ) * elementaryCollapseMin freeFace hfree x) =
      x vertex + freeFace.card * elementaryCollapseMin freeFace hfree x
    change (1 - (t : ℝ)) *
          elementaryCollapseCoord freeFace vertex hfree x vertex +
        (t : ℝ) * x vertex +
          freeFace.card * ((t : ℝ) * elementaryCollapseMin freeFace hfree x) = _
    rw [show elementaryCollapseCoord freeFace vertex hfree x vertex =
        x vertex + freeFace.card * elementaryCollapseMin freeFace hfree x by
      simp [elementaryCollapseCoord]]
    ring
  · by_cases hw : w ∈ freeFace
    · simp only [if_neg hwv, if_pos hw]
      change elementaryCollapseDeformCoord freeFace vertex hfree hv t x w -
          (t : ℝ) * elementaryCollapseMin freeFace hfree x =
        x w - elementaryCollapseMin freeFace hfree x
      change (1 - (t : ℝ)) *
            elementaryCollapseCoord freeFace vertex hfree x w +
          (t : ℝ) * x w -
            (t : ℝ) * elementaryCollapseMin freeFace hfree x = _
      rw [show elementaryCollapseCoord freeFace vertex hfree x w =
          x w - elementaryCollapseMin freeFace hfree x by
        simp [elementaryCollapseCoord, hwv, hw]]
      ring
    · simp only [if_neg hwv, if_neg hw]
      change elementaryCollapseDeformCoord freeFace vertex hfree hv t x w = x w
      change (1 - (t : ℝ)) *
            elementaryCollapseCoord freeFace vertex hfree x w +
          (t : ℝ) * x w = x w
      rw [show elementaryCollapseCoord freeFace vertex hfree x w = x w by
        simp [elementaryCollapseCoord, hwv, hw]]
      ring

theorem elementaryCollapseSimplexDeformation_mem_carrier
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (t : I) (x : stdSimplex ℝ V) (hx : x ∈ facetFamilyCarrier facets) :
    elementaryCollapseSimplexDeformation freeFace vertex hfree hv (t, x) ∈
      facetFamilyCarrier facets := by
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff facets x).mp hx
  obtain ⟨support, hsupportFacet, hxSupport, hcollapseSupport⟩ :=
    elementaryCollapseSimplexMap_common_support
      facets freeFace vertex hfree hv hsimplex hunique x facet hfacet hsupport
  refine (mem_facetFamilyCarrier_iff facets _).mpr
    ⟨support, hsupportFacet, ?_⟩
  intro w hw
  change elementaryCollapseDeformCoord freeFace vertex hfree hv t x w = 0
  rw [elementaryCollapseDeformCoord, hcollapseSupport w hw, hxSupport w hw]
  ring

def elementaryCollapseCarrierDeformation
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex) :
    ContinuousMap.Homotopy
      ((elementaryCollapseCarrierIncl facets freeFace vertex hsimplex).comp
        (elementaryCollapseCarrierMap facets freeFace vertex hfree hv hunique))
      (ContinuousMap.id (facetFamilyCarrier facets)) where
  toFun p := ⟨elementaryCollapseSimplexDeformation
      freeFace vertex hfree hv (p.1, p.2.1),
    elementaryCollapseSimplexDeformation_mem_carrier
      facets freeFace vertex hfree hv hsimplex hunique p.1 p.2.1 p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (elementaryCollapseSimplexDeformation
      freeFace vertex hfree hv).continuous.comp
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  map_zero_left x := by
    apply Subtype.ext
    exact elementaryCollapseSimplexDeformation_zero
      freeFace vertex hfree hv x.1
  map_one_left x := by
    apply Subtype.ext
    exact elementaryCollapseSimplexDeformation_one
      freeFace vertex hfree hv x.1

/-- The carrier deformation fixes a point whenever one of its free-face coordinates already
vanishes. -/
theorem elementaryCollapseCarrierDeformation_eq_self_of_coord_eq_zero
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (t : I) (x : facetFamilyCarrier facets)
    (u : V) (hu : u ∈ freeFace) (hx : x.1 u = 0) :
    elementaryCollapseCarrierDeformation facets freeFace vertex
        hfree hv hsimplex hunique (t, x) = x := by
  apply Subtype.ext
  exact elementaryCollapseSimplexDeformation_eq_self_of_coord_eq_zero
    freeFace vertex hfree hv t x.1 u hu hx

/-- On affine carriers, the elementary retraction remains constant throughout its deformation
back to the identity. -/
theorem elementaryCollapseCarrierMap_deformation
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex)
    (t : I) (x : facetFamilyCarrier facets) :
    elementaryCollapseCarrierMap facets freeFace vertex hfree hv hunique
        (elementaryCollapseCarrierDeformation facets freeFace vertex
          hfree hv hsimplex hunique (t, x)) =
      elementaryCollapseCarrierMap facets freeFace vertex hfree hv hunique x := by
  apply Subtype.ext
  exact elementaryCollapseSimplexMap_deformation freeFace vertex hfree hv t x.1

def elementaryCollapseCarrierHomotopyEquiv
    (facets : Finset (Finset V)) (freeFace : Finset V) (vertex : V)
    (hfree : freeFace.Nonempty) (hv : vertex ∉ freeFace)
    (hsimplex : elementaryCollapseSimplex freeFace vertex ∈ facets)
    (hunique : ∀ facet ∈ facets, freeFace ⊆ facet →
      facet = freeFace ∨ facet = elementaryCollapseSimplex freeFace vertex) :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier facets)
      (facetFamilyCarrier
        (elementaryCollapseFacets facets freeFace vertex)) where
  toFun := elementaryCollapseCarrierMap
    facets freeFace vertex hfree hv hunique
  invFun := elementaryCollapseCarrierIncl
    facets freeFace vertex hsimplex
  left_inv := ⟨elementaryCollapseCarrierDeformation
    facets freeFace vertex hfree hv hsimplex hunique⟩
  right_inv := by
    have hcomp :
        (elementaryCollapseCarrierMap
            facets freeFace vertex hfree hv hunique).comp
          (elementaryCollapseCarrierIncl
            facets freeFace vertex hsimplex) =
          ContinuousMap.id
            (facetFamilyCarrier
              (elementaryCollapseFacets facets freeFace vertex)) := by
      apply ContinuousMap.ext
      intro x
      exact elementaryCollapseCarrierMap_inclusion_apply
        facets freeFace vertex hfree hv hsimplex hunique x
    rw [hcomp]

/-! ## Finite collapse certificates -/

/-- The free face and opposite vertex specifying one elementary collapse. -/
structure ElementaryCollapseMoveData (V : Type) where
  freeFace : Finset V
  vertex : V
deriving DecidableEq

/-- The facet family obtained by applying a finite sequence of elementary collapses. -/
def applyElementaryCollapseMoves (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) : Finset (Finset V) :=
  moves.foldl
    (fun current move ↦
      elementaryCollapseFacets current move.freeFace move.vertex) facets

omit [Fintype V] in
/-- Applying concatenated collapse lists is the same as applying the second list to the endpoint
of the first. -/
theorem applyElementaryCollapseMoves_append (facets : Finset (Finset V))
    (moves₁ moves₂ : List (ElementaryCollapseMoveData V)) :
    applyElementaryCollapseMoves facets (moves₁ ++ moves₂) =
      applyElementaryCollapseMoves
        (applyElementaryCollapseMoves facets moves₁) moves₂ := by
  simp [applyElementaryCollapseMoves, List.foldl_append]

/-- A move is valid when its free face is nonempty, its opposite vertex is new, and the resulting
simplex is the unique listed facet containing that free face. -/
def IsValidElementaryCollapseMove (facets : Finset (Finset V))
    (move : ElementaryCollapseMoveData V) : Prop :=
  move.freeFace.Nonempty ∧
    move.vertex ∉ move.freeFace ∧
    elementaryCollapseSimplex move.freeFace move.vertex ∈ facets ∧
    ∀ facet : {facet : Finset V // facet ∈ facets},
      move.freeFace ⊆ facet.1 →
        facet.1 = move.freeFace ∨
          facet.1 = elementaryCollapseSimplex move.freeFace move.vertex

instance (facets : Finset (Finset V)) (move : ElementaryCollapseMoveData V) :
    Decidable (IsValidElementaryCollapseMove facets move) :=
  inferInstanceAs (Decidable
    (move.freeFace.Nonempty ∧
      move.vertex ∉ move.freeFace ∧
      elementaryCollapseSimplex move.freeFace move.vertex ∈ facets ∧
      ∀ facet : {facet : Finset V // facet ∈ facets},
        move.freeFace ⊆ facet.1 →
          facet.1 = move.freeFace ∨
            facet.1 = elementaryCollapseSimplex move.freeFace move.vertex))

/-- Every move in a collapse sequence is valid for the facet family produced by the preceding
moves. -/
def IsValidElementaryCollapseMoveSequence (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) : Prop :=
  match moves with
  | [] => True
  | move :: rest =>
      IsValidElementaryCollapseMove facets move ∧
        IsValidElementaryCollapseMoveSequence
          (elementaryCollapseFacets facets move.freeFace move.vertex) rest

def isValidElementaryCollapseMoveSequenceDecidable
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) :
    Decidable (IsValidElementaryCollapseMoveSequence facets moves) :=
  match moves with
  | [] => isTrue trivial
  | move :: rest =>
      @instDecidableAnd
        (IsValidElementaryCollapseMove facets move)
        (IsValidElementaryCollapseMoveSequence
          (elementaryCollapseFacets facets move.freeFace move.vertex) rest)
        (inferInstanceAs (Decidable (IsValidElementaryCollapseMove facets move)))
        (isValidElementaryCollapseMoveSequenceDecidable
          (elementaryCollapseFacets facets move.freeFace move.vertex) rest)

instance (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) :
    Decidable (IsValidElementaryCollapseMoveSequence facets moves) :=
  isValidElementaryCollapseMoveSequenceDecidable facets moves

omit [Fintype V] in
/-- A concatenated collapse sequence is valid exactly when its first part is valid and its second
part is valid at the first part's endpoint. -/
theorem isValidElementaryCollapseMoveSequence_append_iff
    (facets : Finset (Finset V))
    (moves₁ moves₂ : List (ElementaryCollapseMoveData V)) :
    IsValidElementaryCollapseMoveSequence facets (moves₁ ++ moves₂) ↔
      IsValidElementaryCollapseMoveSequence facets moves₁ ∧
        IsValidElementaryCollapseMoveSequence
          (applyElementaryCollapseMoves facets moves₁) moves₂ := by
  induction moves₁ generalizing facets with
  | nil =>
      simp only [List.nil_append, IsValidElementaryCollapseMoveSequence,
        applyElementaryCollapseMoves, List.foldl_nil, true_and]
  | cons move moves₁ ih =>
      simp only [List.cons_append, IsValidElementaryCollapseMoveSequence,
        applyElementaryCollapseMoves, List.foldl_cons, ih, and_assoc]

omit [Fintype V] in
/-- A face of the complex after one elementary collapse was already a face before the
collapse. -/
theorem isFace_of_isFace_elementaryCollapseFacets
    (facets : Finset (Finset V)) (move : ElementaryCollapseMoveData V)
    (hvalid : IsValidElementaryCollapseMove facets move)
    (face : Finset V)
    (hface : IsFace
      (elementaryCollapseFacets facets move.freeFace move.vertex) face) :
    IsFace facets face := by
  obtain ⟨facet, hfacet, hfaceFacet⟩ := hface
  obtain ⟨oldFacet, holdFacet, hfacetOld⟩ :=
    facetFamilyLE_elementaryCollapseFacets facets move.freeFace move.vertex
      hvalid.2.2.1 facet hfacet
  exact ⟨oldFacet, holdFacet, hfaceFacet.trans hfacetOld⟩

omit [Fintype V] in
/-- A valid elementary collapse removes every face containing its free face. -/
theorem not_freeFace_subset_of_isFace_elementaryCollapseFacets
    (facets : Finset (Finset V)) (move : ElementaryCollapseMoveData V)
    (hvalid : IsValidElementaryCollapseMove facets move)
    (face : Finset V)
    (hface : IsFace
      (elementaryCollapseFacets facets move.freeFace move.vertex) face) :
    ¬move.freeFace ⊆ face := by
  intro hfreeFace
  obtain ⟨facet, hfacet, hfaceFacet⟩ := hface
  have hfreeFacet : move.freeFace ⊆ facet := hfreeFace.trans hfaceFacet
  rw [elementaryCollapseFacets, Finset.mem_union] at hfacet
  rcases hfacet with hfacet | hfacet
  · obtain ⟨hfacetNeFree, hfacetErase⟩ := Finset.mem_erase.mp hfacet
    obtain ⟨hfacetNeSimplex, hfacetOld⟩ := Finset.mem_erase.mp hfacetErase
    rcases hvalid.2.2.2 ⟨facet, hfacetOld⟩ hfreeFacet with hfacetEq | hfacetEq
    · exact hfacetNeFree hfacetEq
    · exact hfacetNeSimplex hfacetEq
  · rw [Finset.mem_erase] at hfacet
    have hpowerset := Finset.mem_powersetCard.mp hfacet.2
    apply hfacet.1
    exact (Finset.eq_of_subset_of_card_le hfreeFacet hpowerset.2.le).symm

omit [Fintype V] in
/-- Every face surviving a valid collapse sequence was already a face before the sequence. -/
theorem isFace_of_isFace_applyElementaryCollapseMoves
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (face : Finset V)
    (hface : IsFace (applyElementaryCollapseMoves facets moves) face) :
    IsFace facets face := by
  induction moves generalizing facets with
  | nil =>
      exact hface
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      change IsFace
        (applyElementaryCollapseMoves
          (elementaryCollapseFacets facets move.freeFace move.vertex) rest) face at hface
      exact isFace_of_isFace_elementaryCollapseFacets facets move hvalid'.1 face
        (ih (elementaryCollapseFacets facets move.freeFace move.vertex)
          hvalid'.2 hface)

omit [Fintype V] in
/-- A valid collapse sequence is automatically relative to each face that survives in its
endpoint. -/
theorem elementaryCollapseMoveSequence_relative_of_isFace_result
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (face : Finset V)
    (hface : IsFace (applyElementaryCollapseMoves facets moves) face) :
    ∀ move ∈ moves, ¬move.freeFace ⊆ face := by
  induction moves generalizing facets with
  | nil =>
      simp
  | cons first rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets first ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets first.freeFace first.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      change IsFace
        (applyElementaryCollapseMoves
          (elementaryCollapseFacets facets first.freeFace first.vertex) rest) face at hface
      have hfaceAfter : IsFace
          (elementaryCollapseFacets facets first.freeFace first.vertex) face :=
        isFace_of_isFace_applyElementaryCollapseMoves
          (elementaryCollapseFacets facets first.freeFace first.vertex)
          rest hvalid'.2 face hface
      intro move hmove
      simp only [List.mem_cons] at hmove
      rcases hmove with hmove | hmove
      · subst move
        exact not_freeFace_subset_of_isFace_elementaryCollapseFacets
          facets first hvalid'.1 face hfaceAfter
      · exact ih
          (elementaryCollapseFacets facets first.freeFace first.vertex)
          hvalid'.2 hface move hmove

/-- A valid finite sequence of elementary simplicial collapses induces a homotopy equivalence of
affine carriers. -/
noncomputable def elementaryCollapseMoveSequenceCarrierHomotopyEquiv
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves) :
    ContinuousMap.HomotopyEquiv
      (facetFamilyCarrier facets)
      (facetFamilyCarrier (applyElementaryCollapseMoves facets moves)) := by
  induction moves generalizing facets with
  | nil =>
      change ContinuousMap.HomotopyEquiv
        (facetFamilyCarrier facets) (facetFamilyCarrier facets)
      exact ContinuousMap.HomotopyEquiv.refl _
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      change ContinuousMap.HomotopyEquiv
        (facetFamilyCarrier facets)
        (facetFamilyCarrier
          (applyElementaryCollapseMoves
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest))
      exact (elementaryCollapseCarrierHomotopyEquiv
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)).trans
        (ih (elementaryCollapseFacets facets move.freeFace move.vertex) hvalid'.2)

/-- The explicit deformation from inclusion-after-retraction back to the identity associated to
a finite sequence of elementary collapses. -/
noncomputable def elementaryCollapseMoveSequenceCarrierDeformation
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves) :
    ContinuousMap.Homotopy
      ((elementaryCollapseMoveSequenceCarrierHomotopyEquiv
          facets moves hvalid).invFun.comp
        (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
          facets moves hvalid).toFun)
      (ContinuousMap.id (facetFamilyCarrier facets)) := by
  induction moves generalizing facets with
  | nil =>
      exact ContinuousMap.Homotopy.refl _
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      let e₁ := elementaryCollapseCarrierHomotopyEquiv
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      let e₂ := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2
      let H₂ := ih
        (elementaryCollapseFacets facets move.freeFace move.vertex) hvalid'.2
      let Hfirst := (ContinuousMap.Homotopy.refl e₁.invFun).comp
        (H₂.compContinuousMap e₁.toFun)
      let H₁ := elementaryCollapseCarrierDeformation
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      change ContinuousMap.Homotopy
        ((e₁.trans e₂).invFun.comp (e₁.trans e₂).toFun)
        (ContinuousMap.id (facetFamilyCarrier facets))
      simpa only [e₂, ContinuousMap.HomotopyEquiv.trans,
        ContinuousMap.comp_assoc] using Hfirst.trans H₁

/-- The sequence retraction remains constant throughout the explicit deformation supplied by
the collapse certificate.  Thus a certified collapse is a strong deformation retraction in the
direction needed by pushout gluing. -/
theorem elementaryCollapseMoveSequenceCarrierDeformation_toFun
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (t : I) (x : facetFamilyCarrier facets) :
    (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        facets moves hvalid).toFun
        (elementaryCollapseMoveSequenceCarrierDeformation
          facets moves hvalid (t, x)) =
      (elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        facets moves hvalid).toFun x := by
  induction moves generalizing facets t with
  | nil => rfl
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      let e₁ := elementaryCollapseCarrierHomotopyEquiv
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      let e₂ := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2
      let H₂ := elementaryCollapseMoveSequenceCarrierDeformation
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2
      let Hfirst := (ContinuousMap.Homotopy.refl e₁.invFun).comp
        (H₂.compContinuousMap e₁.toFun)
      let H₁ := elementaryCollapseCarrierDeformation
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      change (e₁.trans e₂).toFun ((Hfirst.trans H₁) (t, x)) =
        (e₁.trans e₂).toFun x
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs with ht
      · change e₂.toFun
            (e₁.toFun (e₁.invFun
              (H₂ (⟨2 * t.1, _⟩, e₁.toFun x)))) =
          e₂.toFun (e₁.toFun x)
        rw [show e₁.toFun (e₁.invFun
            (H₂ (⟨2 * t.1, _⟩, e₁.toFun x))) =
            H₂ (⟨2 * t.1, _⟩, e₁.toFun x) by
          exact elementaryCollapseCarrierMap_inclusion_apply
            facets move.freeFace move.vertex
            hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
            (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩) _]
        exact ih (elementaryCollapseFacets facets move.freeFace move.vertex)
          hvalid'.2 ⟨2 * t.1, _⟩ (e₁.toFun x)
      · change e₂.toFun
            (e₁.toFun
              (H₁ (⟨2 * t.1 - 1, _⟩, x))) =
          e₂.toFun (e₁.toFun x)
        exact congrArg e₂.toFun
          (elementaryCollapseCarrierMap_deformation
            facets move.freeFace move.vertex
            hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
            (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
            ⟨2 * t.1 - 1, _⟩ x)

/-- A relative collapse sequence fixes every point supported on the protected vertex set at
every time of its explicit deformation. -/
theorem elementaryCollapseMoveSequenceCarrierDeformation_eq_self_of_support
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (support : Finset V)
    (hrelative : ∀ move ∈ moves, ¬move.freeFace ⊆ support)
    (t : I) (x : facetFamilyCarrier facets)
    (hx : ∀ v, v ∉ support → x.1 v = 0) :
    elementaryCollapseMoveSequenceCarrierDeformation
        facets moves hvalid (t, x) = x := by
  induction moves generalizing facets t with
  | nil => rfl
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      have hmoveRelative : ¬move.freeFace ⊆ support :=
        hrelative move (by simp)
      obtain ⟨u, hufree, hunotSupport⟩ :=
        Finset.not_subset.mp hmoveRelative
      have hxzero : x.1 u = 0 := hx u hunotSupport
      let e₁ := elementaryCollapseCarrierHomotopyEquiv
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      let e₂ := elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2
      let H₂ := elementaryCollapseMoveSequenceCarrierDeformation
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2
      let Hfirst := (ContinuousMap.Homotopy.refl e₁.invFun).comp
        (H₂.compContinuousMap e₁.toFun)
      let H₁ := elementaryCollapseCarrierDeformation
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
      have hmap : (e₁.toFun x).1 = x.1 := by
        change elementaryCollapseSimplexMap move.freeFace move.vertex
            hvalid'.1.1 hvalid'.1.2.1 x.1 = x.1
        exact elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
          move.freeFace move.vertex hvalid'.1.1 hvalid'.1.2.1
          x.1 u hufree hxzero
      have hmapSupport : ∀ v, v ∉ support → (e₁.toFun x).1 v = 0 := by
        intro v hv
        rw [hmap]
        exact hx v hv
      have hrestRelative : ∀ next ∈ rest,
          ¬next.freeFace ⊆ support := by
        intro next hnext
        exact hrelative next (by simp [hnext])
      change (Hfirst.trans H₁) (t, x) = x
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs with ht
      · change e₁.invFun
            (H₂ (⟨2 * t.1, _⟩, e₁.toFun x)) = x
        rw [ih
          (elementaryCollapseFacets facets move.freeFace move.vertex)
          hvalid'.2 hrestRelative ⟨2 * t.1, _⟩
          (e₁.toFun x) hmapSupport]
        apply Subtype.ext
        exact hmap
      · exact elementaryCollapseCarrierDeformation_eq_self_of_coord_eq_zero
          facets move.freeFace move.vertex
          hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
          (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)
          ⟨2 * t.1 - 1, _⟩ x u hufree hxzero

/-- The inverse supplied by a finite elementary-collapse sequence is the canonical carrier
inclusion: it preserves every ambient barycentric coordinate. -/
theorem elementaryCollapseMoveSequenceCarrierHomotopyEquiv_invFun_val
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (x : facetFamilyCarrier (applyElementaryCollapseMoves facets moves)) :
    ((elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      facets moves hvalid).invFun x).1 = x.1 := by
  induction moves generalizing facets with
  | nil => rfl
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      change ((elementaryCollapseCarrierHomotopyEquiv
        facets move.freeFace move.vertex
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1
        (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩)).invFun
          ((elementaryCollapseMoveSequenceCarrierHomotopyEquiv
            (elementaryCollapseFacets facets move.freeFace move.vertex)
            rest hvalid'.2).invFun x)).1 = x.1
      exact ih
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        hvalid'.2 x

/-- A relative elementary-collapse sequence fixes every point supported on the protected vertex
set.  It is enough that each free face contain a vertex outside that support. -/
theorem elementaryCollapseMoveSequenceCarrierHomotopyEquiv_toFun_val_eq_of_support
    (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V))
    (hvalid : IsValidElementaryCollapseMoveSequence facets moves)
    (support : Finset V)
    (hrelative : ∀ move ∈ moves, ¬move.freeFace ⊆ support)
    (x : facetFamilyCarrier facets)
    (hx : ∀ v, v ∉ support → x.1 v = 0) :
    ((elementaryCollapseMoveSequenceCarrierHomotopyEquiv
      facets moves hvalid).toFun x).1 = x.1 := by
  induction moves generalizing facets with
  | nil => rfl
  | cons move rest ih =>
      have hvalid' : IsValidElementaryCollapseMove facets move ∧
          IsValidElementaryCollapseMoveSequence
            (elementaryCollapseFacets facets move.freeFace move.vertex) rest := by
        simpa only [IsValidElementaryCollapseMoveSequence] using hvalid
      have hmoveRelative : ¬move.freeFace ⊆ support :=
        hrelative move (by simp)
      obtain ⟨u, hufree, hunotSupport⟩ :=
        Finset.not_subset.mp hmoveRelative
      have hmap : elementaryCollapseSimplexMap move.freeFace move.vertex
          hvalid'.1.1 hvalid'.1.2.1 x.1 = x.1 :=
        elementaryCollapseSimplexMap_eq_self_of_coord_eq_zero
          move.freeFace move.vertex hvalid'.1.1 hvalid'.1.2.1 x.1
          u hufree (hx u hunotSupport)
      let y := elementaryCollapseCarrierMap
        facets move.freeFace move.vertex hvalid'.1.1 hvalid'.1.2.1
          (fun facet hfacet ↦ hvalid'.1.2.2.2 ⟨facet, hfacet⟩) x
      have hy : y.1 = x.1 := hmap
      have hySupport : ∀ v, v ∉ support → y.1 v = 0 := by
        intro v hv
        rw [hy]
        exact hx v hv
      have hrestRelative : ∀ next ∈ rest,
          ¬next.freeFace ⊆ support := by
        intro next hnext
        exact hrelative next (by simp [hnext])
      change ((elementaryCollapseMoveSequenceCarrierHomotopyEquiv
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        rest hvalid'.2).toFun y).1 = x.1
      exact (ih
        (elementaryCollapseFacets facets move.freeFace move.vertex)
        hvalid'.2 hrestRelative y hySupport).trans hy

end Submission.FiniteOrderedComplex
