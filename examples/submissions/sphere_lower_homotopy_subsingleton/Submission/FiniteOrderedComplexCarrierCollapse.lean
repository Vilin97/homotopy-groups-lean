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

/-- The facet family obtained by applying a finite sequence of elementary collapses. -/
def applyElementaryCollapseMoves (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) : Finset (Finset V) :=
  moves.foldl
    (fun current move ↦
      elementaryCollapseFacets current move.freeFace move.vertex) facets

/-- A move is valid when its free face is nonempty, its opposite vertex is new, and the resulting
simplex is the unique listed facet containing that free face. -/
def IsValidElementaryCollapseMove (facets : Finset (Finset V))
    (move : ElementaryCollapseMoveData V) : Prop :=
  move.freeFace.Nonempty ∧
    move.vertex ∉ move.freeFace ∧
    elementaryCollapseSimplex move.freeFace move.vertex ∈ facets ∧
    ∀ facet ∈ facets, move.freeFace ⊆ facet →
      facet = move.freeFace ∨
        facet = elementaryCollapseSimplex move.freeFace move.vertex

instance (facets : Finset (Finset V)) (move : ElementaryCollapseMoveData V) :
    Decidable (IsValidElementaryCollapseMove facets move) := by
  unfold IsValidElementaryCollapseMove
  infer_instance

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

instance (facets : Finset (Finset V))
    (moves : List (ElementaryCollapseMoveData V)) :
    Decidable (IsValidElementaryCollapseMoveSequence facets moves) := by
  induction moves generalizing facets with
  | nil =>
      simpa only [IsValidElementaryCollapseMoveSequence] using
        (isTrue trivial : Decidable True)
  | cons move rest ih =>
      unfold IsValidElementaryCollapseMoveSequence
      letI := ih (elementaryCollapseFacets facets move.freeFace move.vertex)
      infer_instance

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
        hvalid'.1.1 hvalid'.1.2.1 hvalid'.1.2.2.1 hvalid'.1.2.2.2).trans
        (ih (elementaryCollapseFacets facets move.freeFace move.vertex) hvalid'.2)

end Submission.FiniteOrderedComplex
