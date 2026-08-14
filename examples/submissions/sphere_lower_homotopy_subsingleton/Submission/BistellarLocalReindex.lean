/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarLocalCompatibility
import Submission.Cohomology.FiniteOrderedComplexReindex

/-!
# Reindexing local bistellar realizations

A valid bistellar move may use vertices in any linearly ordered type.  This file indexes the
finite union of its two cores increasingly by `Fin (dimension + 2)`, proves that both local facet
families are the corresponding mapped standard families, and transports the explicit standard
local homeomorphism to the actual ordered complex.

## Main results

* `Submission.FiniteOrderedComplex.bistellarOldReindexIso` and
  `Submission.FiniteOrderedComplex.bistellarNewReindexIso`;
* `Submission.FiniteOrderedComplex.bistellarMoveLocalRealizationHomeomorph`.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.FiniteOrderedComplex

variable {V W : Type} [LinearOrder V] [LinearOrder W]

/-- Vertices of a subcore, indexed increasingly inside a finite ambient vertex set. -/
def coreIndex {n : ℕ} (vertices core : Finset V)
    (hcard : vertices.card = n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ vertices.orderEmbOfFin hcard i ∈ core

theorem map_coreIndex {n : ℕ} (vertices core : Finset V)
    (hcard : vertices.card = n) (hsub : core ⊆ vertices) :
    (coreIndex vertices core hcard).map
      (vertices.orderEmbOfFin hcard).toEmbedding = core := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    have hxv := hsub hx
    rw [← Finset.image_orderEmbOfFin_univ vertices hcard] at hxv
    rcases Finset.mem_image.mp hxv with ⟨i, _, rfl⟩
    exact Finset.mem_map.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem coreIndex_nonempty {n : ℕ} (vertices core : Finset V)
    (hcard : vertices.card = n) (hsub : core ⊆ vertices)
    (hcore : core.Nonempty) :
    (coreIndex vertices core hcard).Nonempty := by
  rw [← Finset.map_nonempty]
  rw [map_coreIndex vertices core hcard hsub]
  exact hcore

theorem coreIndex_disjoint {n : ℕ} (vertices A B : Finset V)
    (hcard : vertices.card = n) (hdisj : Disjoint A B) :
    Disjoint (coreIndex vertices A hcard) (coreIndex vertices B hcard) := by
  rw [Finset.disjoint_left]
  intro i hiA hiB
  exact (Finset.disjoint_left.mp hdisj)
    (Finset.mem_filter.mp hiA).2 (Finset.mem_filter.mp hiB).2

theorem coreIndex_union {n : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = n) :
    coreIndex (A ∪ B) A hcard ∪ coreIndex (A ∪ B) B hcard =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  have hi : (A ∪ B).orderEmbOfFin hcard i ∈ A ∪ B :=
    Finset.orderEmbOfFin_mem (A ∪ B) hcard i
  rcases Finset.mem_union.mp hi with hiA | hiB
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiA⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiB⟩)

theorem mapFacets_bistellarOldFacets (e : V ↪ W) (A B : Finset V) :
    mapFacets e (bistellarOldFacets A B) =
      bistellarOldFacets (A.map e) (B.map e) := by
  ext facet
  simp [mapFacets, bistellarOldFacets, Finset.map_union, Finset.map_erase]

theorem mapFacets_bistellarNewFacets (e : V ↪ W) (A B : Finset V) :
    mapFacets e (bistellarNewFacets A B) =
      bistellarNewFacets (A.map e) (B.map e) := by
  ext facet
  simp [mapFacets, bistellarNewFacets, Finset.map_union, Finset.map_erase]

/-- The old core of a move, indexed inside its ordered union of vertices. -/
abbrev indexedOldCore {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) : Finset (Fin (dimension + 2)) :=
  coreIndex (A ∪ B) A hcard

/-- The new core of a move, indexed inside its ordered union of vertices. -/
abbrev indexedNewCore {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) : Finset (Fin (dimension + 2)) :=
  coreIndex (A ∪ B) B hcard

theorem map_indexedOldCore {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    (indexedOldCore A B hcard).map
      ((A ∪ B).orderEmbOfFin hcard).toEmbedding = A :=
  map_coreIndex (A ∪ B) A hcard Finset.subset_union_left

theorem map_indexedNewCore {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    (indexedNewCore A B hcard).map
      ((A ∪ B).orderEmbOfFin hcard).toEmbedding = B :=
  map_coreIndex (A ∪ B) B hcard Finset.subset_union_right

theorem indexedOldCore_nonempty {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) (hA : A.Nonempty) :
    (indexedOldCore A B hcard).Nonempty :=
  coreIndex_nonempty (A ∪ B) A hcard Finset.subset_union_left hA

theorem indexedNewCore_nonempty {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) (hB : B.Nonempty) :
    (indexedNewCore A B hcard).Nonempty :=
  coreIndex_nonempty (A ∪ B) B hcard Finset.subset_union_right hB

theorem indexedCores_disjoint {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) (hdisj : Disjoint A B) :
    Disjoint (indexedOldCore A B hcard) (indexedNewCore A B hcard) :=
  coreIndex_disjoint (A ∪ B) A B hcard hdisj

theorem indexedCores_union {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    indexedOldCore A B hcard ∪ indexedNewCore A B hcard = Finset.univ :=
  coreIndex_union A B hcard

/-- Reindex the standard old local bistellar complex onto the actual ordered move vertices. -/
def bistellarOldReindexIso {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    orderedSSet (bistellarOldFacets
      (indexedOldCore A B hcard) (indexedNewCore A B hcard)) ≅
      orderedSSet (bistellarOldFacets A B) :=
  orderedSSetMapFacetsIso ((A ∪ B).orderEmbOfFin hcard) _ ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex (by
      rw [mapFacets_bistellarOldFacets,
        map_indexedOldCore, map_indexedNewCore]))

/-- Reindex the standard new local bistellar complex onto the actual ordered move vertices. -/
def bistellarNewReindexIso {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    orderedSSet (bistellarNewFacets
      (indexedOldCore A B hcard) (indexedNewCore A B hcard)) ≅
      orderedSSet (bistellarNewFacets A B) :=
  orderedSSetMapFacetsIso ((A ∪ B).orderEmbOfFin hcard) _ ≪≫
    SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex (by
      rw [mapFacets_bistellarNewFacets,
        map_indexedOldCore, map_indexedNewCore]))

/-- The local realization homeomorphism depends only on two nonempty, disjoint cores of the
prescribed total cardinality. -/
def bistellarLocalRealizationHomeomorph
    {dimension : ℕ} (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcard : (A ∪ B).card = dimension + 2) :
    SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≃ₜ
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
      (bistellarOldReindexIso A B hcard).symm)).trans
    ((bistellarLocalOrderedRealizationHomeomorph
      (indexedOldCore A B hcard)
      (indexedNewCore A B hcard)
      (indexedOldCore_nonempty A B hcard hA)
      (indexedNewCore_nonempty A B hcard hB)
      (indexedCores_disjoint A B hcard hdisj)
      (indexedCores_union A B hcard)).trans
        (TopCat.homeoOfIso (SSet.toTop.mapIso
          (bistellarNewReindexIso A B hcard))))

/-- Every valid bistellar replacement has homeomorphic old and new local realizations. -/
def bistellarMoveLocalRealizationHomeomorph
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≃ₜ
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)) :=
  bistellarLocalRealizationHomeomorph A B h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

end Submission.FiniteOrderedComplex
