/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.AffineCone

/-!
# Affine carriers of finite facet families

A finite family of vertex sets determines the union of the corresponding closed faces of a
standard simplex.  This file packages that union as `facetFamilyCarrier`, proves it closed and
compact, and records the hypotheses that place it in the face opposite a chosen cone vertex.
The resulting compact base can then be fed directly to the radial affine-cone homeomorphism.
-/

noncomputable section

open scoped Topology TopCat

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The closed standard-simplex face supported on a finite vertex set. -/
def simplexFaceCarrier (facet : Finset V) : Set (stdSimplex ℝ V) :=
  {x | ∀ v, v ∉ facet → x v = 0}

omit [DecidableEq V] in
/-- A coordinate face of a finite standard simplex is closed. -/
theorem isClosed_simplexFaceCarrier (facet : Finset V) :
    IsClosed (simplexFaceCarrier facet) := by
  rw [show simplexFaceCarrier facet =
      ⋂ v : {v : V // v ∉ facet}, {x : stdSimplex ℝ V | x v.1 = 0} by
    ext x
    simp [simplexFaceCarrier]]
  apply isClosed_iInter
  intro v
  exact isClosed_eq
    ((continuous_apply v.1).comp continuous_subtype_val) continuous_const

/-- Embed the simplex indexed by the vertices of a face into the ambient standard simplex. -/
noncomputable def simplexFaceEmbedding (facet : Finset V) :
    stdSimplex ℝ facet → simplexFaceCarrier facet := fun x =>
  ⟨stdSimplex.map Subtype.val x, by
    intro v hv
    change (FunOnFinite.linearMap ℝ ℝ (fun i : facet ↦ i.1) x) v = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    exact False.elim (hv (hi.2 ▸ i.2))⟩

/-- Restrict an ambient simplex point supported on a face to the coordinates of that face. -/
noncomputable def simplexFaceRestriction (facet : Finset V) :
    simplexFaceCarrier facet → stdSimplex ℝ facet := fun x =>
  ⟨fun v ↦ x.1 v.1, by
    constructor
    · intro v
      exact x.1.2.1 v.1
    · rw [← Finset.sum_subtype facet (by simp)]
      rw [← x.1.2.2]
      apply Finset.sum_subset (Finset.subset_univ facet)
      intro v _ hv
      exact x.2 v hv⟩

/-- Restricting a face embedding recovers the original barycentric coordinates. -/
@[simp]
theorem simplexFaceRestriction_embedding (facet : Finset V)
    (x : stdSimplex ℝ facet) :
    simplexFaceRestriction facet (simplexFaceEmbedding facet x) = x := by
  apply stdSimplex.ext
  funext i
  change (FunOnFinite.linearMap ℝ ℝ (fun j : facet ↦ j.1) x) i.1 = x i
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [Finset.mem_filter] at hj
    exact False.elim (hji (Subtype.ext hj.2))
  · intro hi
    exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))

/-- Embedding the coordinate restriction of a supported point recovers that ambient point. -/
@[simp]
theorem simplexFaceEmbedding_restriction (facet : Finset V)
    (x : simplexFaceCarrier facet) :
    simplexFaceEmbedding facet (simplexFaceRestriction facet x) = x := by
  apply Subtype.ext
  apply stdSimplex.ext
  funext v
  change (FunOnFinite.linearMap ℝ ℝ (fun j : facet ↦ j.1)
      (simplexFaceRestriction facet x)) v = x.1 v
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hv : v ∈ facet
  · let i : facet := ⟨v, hv⟩
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [Finset.mem_filter] at hj
      exact False.elim (hji (Subtype.ext hj.2))
    · intro hi
      exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
  · rw [Finset.filter_eq_empty_iff.mpr]
    · exact (x.2 v hv).symm
    · intro i _
      exact fun hiv ↦ hv (hiv ▸ i.2)

omit [DecidableEq V] in
/-- Coordinate restriction from an ambient simplex face is continuous. -/
theorem continuous_simplexFaceRestriction (facet : Finset V) :
    Continuous (simplexFaceRestriction facet) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  exact (continuous_apply v.1).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- A coordinate face of an ambient standard simplex is homeomorphic to the standard simplex on
its own vertex subtype. -/
def simplexFaceHomeomorph (facet : Finset V) :
    stdSimplex ℝ facet ≃ₜ simplexFaceCarrier facet where
  toFun := simplexFaceEmbedding facet
  invFun := simplexFaceRestriction facet
  left_inv := simplexFaceRestriction_embedding facet
  right_inv := simplexFaceEmbedding_restriction facet
  continuous_toFun := Continuous.subtype_mk
    (stdSimplex.continuous_map Subtype.val) _
  continuous_invFun := continuous_simplexFaceRestriction facet

/-- The inverse face homeomorphism reads off the coordinates indexed by the face. -/
@[simp]
theorem simplexFaceHomeomorph_symm_apply_apply (facet : Finset V)
    (x : simplexFaceCarrier facet) (v : facet) :
    (simplexFaceHomeomorph facet).symm x v = x.1 v.1 := rfl

/-- The affine union of the simplex faces indexed by a finite facet family. -/
def facetFamilyCarrier (facets : Finset (Finset V)) : Set (stdSimplex ℝ V) :=
  ⋃ facet : facets, simplexFaceCarrier facet.1

omit [DecidableEq V] in
/-- Membership in a facet-family carrier is equivalent to support in one listed facet. -/
theorem mem_facetFamilyCarrier_iff (facets : Finset (Finset V))
    (x : stdSimplex ℝ V) :
    x ∈ facetFamilyCarrier facets ↔
      ∃ facet ∈ facets, ∀ v, v ∉ facet → x v = 0 := by
  simp [facetFamilyCarrier, simplexFaceCarrier]

omit [DecidableEq V] in
/-- A finite union of closed simplex faces is closed. -/
theorem isClosed_facetFamilyCarrier (facets : Finset (Finset V)) :
    IsClosed (facetFamilyCarrier facets) := by
  apply isClosed_iUnion_of_finite
  intro facet
  exact isClosed_simplexFaceCarrier facet.1

omit [DecidableEq V] in
/-- A finite facet-family carrier is compact. -/
theorem isCompact_facetFamilyCarrier (facets : Finset (Finset V)) :
    IsCompact (facetFamilyCarrier facets) :=
  (isClosed_facetFamilyCarrier facets).isCompact

/-- The subtype of a finite facet-family carrier is a compact space. -/
noncomputable instance facetFamilyCarrierCompactSpace
    (facets : Finset (Finset V)) : CompactSpace (facetFamilyCarrier facets) :=
  isCompact_iff_compactSpace.mp (isCompact_facetFamilyCarrier facets)

omit [DecidableEq V] in
/-- If no base facet contains the apex, every carrier point has zero apex coordinate. -/
theorem facetFamilyCarrier_apex_eq_zero
    (facets : Finset (Finset V)) (apex : V)
    (hapex : ∀ facet ∈ facets, apex ∉ facet) :
    ∀ x ∈ facetFamilyCarrier facets, x apex = 0 := by
  intro x hx
  obtain ⟨facet, hfacet, hsupport⟩ :=
    (mem_facetFamilyCarrier_iff facets x).mp hx
  exact hsupport apex (hapex facet hfacet)

/-- A family containing a nonempty facet has a nonempty affine carrier. -/
theorem facetFamilyCarrier_nonempty
    (facets : Finset (Finset V))
    (hfacets : ∃ facet ∈ facets, facet.Nonempty) :
    (facetFamilyCarrier facets).Nonempty := by
  obtain ⟨facet, hfacet, v, hv⟩ := hfacets
  refine ⟨stdSimplex.vertex v, (mem_facetFamilyCarrier_iff facets _).mpr
    ⟨facet, hfacet, ?_⟩⟩
  intro w hw
  rw [stdSimplex.vertex_coe]
  simp only [Pi.single_apply]
  rw [if_neg]
  exact fun hvw ↦ hw (hvw ▸ hv)

/-- The abstract cone on a nonempty facet-family carrier is its radial affine cone. -/
def facetFamilyTopologicalConeHomeomorphCarrier
    (facets : Finset (Finset V)) (apex : V)
    (hapex : ∀ facet ∈ facets, apex ∉ facet)
    (hfacets : ∃ facet ∈ facets, facet.Nonempty) :
    topologicalCone (TopCat.of (facetFamilyCarrier facets)) ≃ₜ
      affineConeCarrier (facetFamilyCarrier facets) apex :=
  affineTopologicalConeHomeomorphCarrier
    (facetFamilyCarrier facets) apex
    (facetFamilyCarrier_apex_eq_zero facets apex hapex)
    (facetFamilyCarrier_nonempty facets hfacets)

end Submission.FiniteOrderedComplex
