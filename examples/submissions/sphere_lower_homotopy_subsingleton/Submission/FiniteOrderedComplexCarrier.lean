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
