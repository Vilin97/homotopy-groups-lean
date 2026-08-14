/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarOrderedCompatibility

/-!
# Gluing-compatible local bistellar homeomorphisms

The pointwise boundary theorem for the standard selected-face model is stable under arbitrary
precomposition by simplicial maps that agree in the ambient nerve.  This file proves that
naturality statement, reindexes it to every valid bistellar move, and constructs a local
homeomorphism satisfying exactly the compatibility equation needed by the global pushout gluing
theorem.

## Main results

* `Submission.FiniteOrderedComplex.selectedFacesOrderedBistellarHomeomorph_natural_of_ambient`;
* `Submission.FiniteOrderedComplex.bistellarMoveCompatibleLocalRealizationHomeomorph`;
* `Submission.FiniteOrderedComplex.bistellarMoveCompatibleLocalRealizationHomeomorph_natural_of_ambient`.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.FiniteOrderedComplex

/-- Boundary compatibility holds after precomposition by any pair of maps with the same ambient
simplex map. -/
theorem selectedFacesOrderedBistellarHomeomorph_natural_of_ambient
    {n : ℕ} {X : SSet}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ)
    (f : X ⟶ orderedSSet (selectedFaceFacets B))
    (g : X ⟶ orderedSSet (selectedFaceFacets A))
    (hfg : f ≫ (orderedSubcomplex (selectedFaceFacets B)).ι =
      g ≫ (orderedSubcomplex (selectedFaceFacets A)).ι) :
    SSet.toTop.map f ≫ (TopCat.isoOfHomeo
        (selectedFacesOrderedBistellarHomeomorph A B hA hB hdisj hcover)).hom =
      SSet.toTop.map g := by
  let common : (CategoryTheory.nerve (Fin (n + 2))).Subcomplex :=
    orderedSubcomplex (selectedFaceFacets B) ⊓
      orderedSubcomplex (selectedFaceFacets A)
  let oldIncl : (common : SSet) ⟶ orderedSSet (selectedFaceFacets B) :=
    SSet.Subcomplex.homOfLE
      (show common ≤ orderedSubcomplex (selectedFaceFacets B) from inf_le_left)
  let newIncl : (common : SSet) ⟶ orderedSSet (selectedFaceFacets A) :=
    SSet.Subcomplex.homOfLE
      (show common ≤ orderedSubcomplex (selectedFaceFacets A) from inf_le_right)
  let k : X ⟶ (common : SSet) :=
    { app := fun Δ ↦ ↾fun x ↦ ⟨(f.app Δ x).1, ⟨(f.app Δ x).2, by
          have hx := congrArg (fun q ↦ q.app Δ x) hfg
          change (f.app Δ x).1 = (g.app Δ x).1 at hx
          rw [hx]
          exact (g.app Δ x).2⟩⟩
      naturality := by
        intro Δ Δ' φ
        ext x
        apply Subtype.ext
        change (f.app Δ' (X.map φ x)).1 =
          ((orderedSSet (selectedFaceFacets B)).map φ (f.app Δ x)).1
        exact congrArg Subtype.val
          (ConcreteCategory.congr_hom (f.naturality φ) x) }
  have hkOld : k ≫ oldIncl = f := by
    ext Δ x
    rfl
  have hkNew : k ≫ newIncl = g := by
    ext Δ x
    apply Subtype.ext
    have hx := congrArg (fun q ↦ q.app Δ x) hfg
    exact hx
  rw [← hkOld, ← hkNew, Functor.map_comp, Functor.map_comp, Category.assoc]
  rw [selectedFacesOrderedBistellarHomeomorph_common
    A B hA hB hdisj hcover]

variable {V : Type} [LinearOrder V]

@[reassoc (attr := simp)]
theorem bistellarOldReindexIso_hom_ι {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    (bistellarOldReindexIso A B hcard).hom ≫
        (orderedSubcomplex (bistellarOldFacets A B)).ι =
      (orderedSubcomplex (bistellarOldFacets
          (indexedOldCore A B hcard) (indexedNewCore A B hcard))).ι ≫
        nerveOrderEmb ((A ∪ B).orderEmbOfFin hcard) := by
  simp [bistellarOldReindexIso, orderedSSetMapFacetsIso_hom_ι]

@[reassoc (attr := simp)]
theorem bistellarNewReindexIso_hom_ι {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) :
    (bistellarNewReindexIso A B hcard).hom ≫
        (orderedSubcomplex (bistellarNewFacets A B)).ι =
      (orderedSubcomplex (bistellarNewFacets
          (indexedOldCore A B hcard) (indexedNewCore A B hcard))).ι ≫
        nerveOrderEmb ((A ∪ B).orderEmbOfFin hcard) := by
  simp [bistellarNewReindexIso, orderedSSetMapFacetsIso_hom_ι]

/-- Reindex the selected-face presentation of the old standard local ball. -/
def bistellarOldSelectedReindexIso {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) (hdisj : Disjoint A B) :
    orderedSSet (selectedFaceFacets (indexedNewCore A B hcard)) ≅
      orderedSSet (bistellarOldFacets A B) :=
  SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      (bistellarOldFacets_eq_selectedFaceFacets
        (indexedOldCore A B hcard) (indexedNewCore A B hcard)
        (indexedCores_disjoint A B hcard hdisj)
        (indexedCores_union A B hcard)).symm) ≪≫
    bistellarOldReindexIso A B hcard

/-- Reindex the selected-face presentation of the new standard local ball. -/
def bistellarNewSelectedReindexIso {dimension : ℕ} (A B : Finset V)
    (hcard : (A ∪ B).card = dimension + 2) (hdisj : Disjoint A B) :
    orderedSSet (selectedFaceFacets (indexedOldCore A B hcard)) ≅
      orderedSSet (bistellarNewFacets A B) :=
  SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      (bistellarNewFacets_eq_selectedFaceFacets
        (indexedOldCore A B hcard) (indexedNewCore A B hcard)
        (indexedCores_disjoint A B hcard hdisj)
        (indexedCores_union A B hcard)).symm) ≪≫
    bistellarNewReindexIso A B hcard

@[reassoc (attr := simp)]
theorem bistellarOldSelectedReindexIso_hom_ι {dimension : ℕ}
    (A B : Finset V) (hcard : (A ∪ B).card = dimension + 2)
    (hdisj : Disjoint A B) :
    (bistellarOldSelectedReindexIso A B hcard hdisj).hom ≫
        (orderedSubcomplex (bistellarOldFacets A B)).ι =
      (orderedSubcomplex
          (selectedFaceFacets (indexedNewCore A B hcard))).ι ≫
        nerveOrderEmb ((A ∪ B).orderEmbOfFin hcard) := by
  simp [bistellarOldSelectedReindexIso]

@[reassoc (attr := simp)]
theorem bistellarNewSelectedReindexIso_hom_ι {dimension : ℕ}
    (A B : Finset V) (hcard : (A ∪ B).card = dimension + 2)
    (hdisj : Disjoint A B) :
    (bistellarNewSelectedReindexIso A B hcard hdisj).hom ≫
        (orderedSubcomplex (bistellarNewFacets A B)).ι =
      (orderedSubcomplex
          (selectedFaceFacets (indexedOldCore A B hcard))).ι ≫
        nerveOrderEmb ((A ∪ B).orderEmbOfFin hcard) := by
  simp [bistellarNewSelectedReindexIso]

/-- The local realization homeomorphism, expressed through the selected-face standard model. -/
def bistellarMoveCompatibleLocalRealizationHomeomorph
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) :
    SSet.toTop.obj (orderedSSet (bistellarOldFacets A B)) ≃ₜ
      SSet.toTop.obj (orderedSSet (bistellarNewFacets A B)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
      (bistellarOldSelectedReindexIso A B h.2.2.2.2.1 h.2.2.2.1).symm)).trans
    ((selectedFacesOrderedBistellarHomeomorph
      (indexedOldCore A B h.2.2.2.2.1)
      (indexedNewCore A B h.2.2.2.2.1)
      (indexedOldCore_nonempty A B h.2.2.2.2.1 h.2.1)
      (indexedNewCore_nonempty A B h.2.2.2.2.1 h.2.2.1)
      (indexedCores_disjoint A B h.2.2.2.2.1 h.2.2.2.1)
      (indexedCores_union A B h.2.2.2.2.1)).trans
        (TopCat.homeoOfIso (SSet.toTop.mapIso
          (bistellarNewSelectedReindexIso A B
            h.2.2.2.2.1 h.2.2.2.1))))

/-- The reindexed local homeomorphism is compatible with any pair of maps that agree in the
ambient ordered nerve. -/
theorem bistellarMoveCompatibleLocalRealizationHomeomorph_natural_of_ambient
    {facets : Finset (Finset V)} {dimension : ℕ} {A B : Finset V}
    (h : IsBistellarMove facets dimension A B) {X : SSet}
    (f : X ⟶ orderedSSet (bistellarOldFacets A B))
    (g : X ⟶ orderedSSet (bistellarNewFacets A B))
    (hfg : f ≫ (orderedSubcomplex (bistellarOldFacets A B)).ι =
      g ≫ (orderedSubcomplex (bistellarNewFacets A B)).ι) :
    SSet.toTop.map f ≫ (TopCat.isoOfHomeo
        (bistellarMoveCompatibleLocalRealizationHomeomorph h)).hom =
      SSet.toTop.map g := by
  let oldIso := bistellarOldSelectedReindexIso A B h.2.2.2.2.1 h.2.2.2.1
  let newIso := bistellarNewSelectedReindexIso A B h.2.2.2.2.1 h.2.2.2.1
  let f₀ := f ≫ oldIso.inv
  let g₀ := g ≫ newIso.inv
  have hfg₀ :
      f₀ ≫ (orderedSubcomplex
          (selectedFaceFacets (indexedNewCore A B h.2.2.2.2.1))).ι =
        g₀ ≫ (orderedSubcomplex
          (selectedFaceFacets (indexedOldCore A B h.2.2.2.2.1))).ι := by
    rw [← cancel_mono (nerveOrderEmb
      ((A ∪ B).orderEmbOfFin h.2.2.2.2.1))]
    simp only [f₀, g₀, Category.assoc]
    rw [← bistellarOldSelectedReindexIso_hom_ι
        A B h.2.2.2.2.1 h.2.2.2.1,
      ← bistellarNewSelectedReindexIso_hom_ι
        A B h.2.2.2.2.1 h.2.2.2.1]
    change f ≫ oldIso.inv ≫ oldIso.hom ≫
        (orderedSubcomplex (bistellarOldFacets A B)).ι =
      g ≫ newIso.inv ≫ newIso.hom ≫
        (orderedSubcomplex (bistellarNewFacets A B)).ι
    simp only [Iso.inv_hom_id_assoc]
    exact hfg
  have hstandard := selectedFacesOrderedBistellarHomeomorph_natural_of_ambient
    (indexedOldCore A B h.2.2.2.2.1)
    (indexedNewCore A B h.2.2.2.2.1)
    (indexedOldCore_nonempty A B h.2.2.2.2.1 h.2.1)
    (indexedNewCore_nonempty A B h.2.2.2.2.1 h.2.2.1)
    (indexedCores_disjoint A B h.2.2.2.2.1 h.2.2.2.1)
    (indexedCores_union A B h.2.2.2.2.1) f₀ g₀ hfg₀
  change SSet.toTop.map f ≫
      SSet.toTop.map oldIso.inv ≫
        (TopCat.isoOfHomeo (selectedFacesOrderedBistellarHomeomorph
          (indexedOldCore A B h.2.2.2.2.1)
          (indexedNewCore A B h.2.2.2.2.1)
          (indexedOldCore_nonempty A B h.2.2.2.2.1 h.2.1)
          (indexedNewCore_nonempty A B h.2.2.2.2.1 h.2.2.1)
          (indexedCores_disjoint A B h.2.2.2.2.1 h.2.2.2.1)
          (indexedCores_union A B h.2.2.2.2.1))).hom ≫
            SSet.toTop.map newIso.hom = SSet.toTop.map g
  rw [← Category.assoc, ← Functor.map_comp]
  change SSet.toTop.map f₀ ≫
      (TopCat.isoOfHomeo (selectedFacesOrderedBistellarHomeomorph
        (indexedOldCore A B h.2.2.2.2.1)
        (indexedNewCore A B h.2.2.2.2.1)
        (indexedOldCore_nonempty A B h.2.2.2.2.1 h.2.1)
        (indexedNewCore_nonempty A B h.2.2.2.2.1 h.2.2.1)
        (indexedCores_disjoint A B h.2.2.2.2.1 h.2.2.2.1)
        (indexedCores_union A B h.2.2.2.2.1))).hom ≫
          SSet.toTop.map newIso.hom = SSet.toTop.map g
  rw [← Category.assoc, hstandard]
  change SSet.toTop.map (g ≫ newIso.inv) ≫
    SSet.toTop.map newIso.hom = SSet.toTop.map g
  rw [← Functor.map_comp]
  congr 1
  simp

end Submission.FiniteOrderedComplex
