/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarLocalReindex

/-!
# Boundary compatibility in ordered local bistellar models

This file proves that the simplicial-set isomorphisms used to identify selected faces and to
reindex finite ordered complexes commute with their ambient nerve inclusions.  It uses those
formulas to transport the affine pointwise-fixed theorem to the ordered local bistellar
homeomorphism: on the intersection of the old and new ordered local balls, the map is exactly the
new inclusion.

## Main results

* `Submission.FiniteOrderedComplex.selectedFacesOrderedRealizationToAmbient_eq`;
* `Submission.FiniteOrderedComplex.selectedFacesOrderedBistellarHomeomorph_common`;
* `Submission.FiniteOrderedComplex.orderedSSetMapFacetsIso_hom_ι`.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.FiniteOrderedComplex

universe u

theorem selectedFacesOrderedSSetIso_hom_ι {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    (selectedFacesOrderedSSetIso I).hom ≫
        (orderedSubcomplex (selectedFaceFacets I)).ι =
      (selectedFacesSubcomplex I).ι ≫ (finNerveIso (n + 1)).hom := by
  simp [selectedFacesOrderedSSetIso]

variable {V W : Type} [LinearOrder V] [LinearOrder W]

theorem orderedSSetMapFacetsIso_hom_ι (e : V ↪o W)
    (facets : Finset (Finset V)) :
    (orderedSSetMapFacetsIso e facets).hom ≫
        (orderedSubcomplex (mapFacets e.toEmbedding facets)).ι =
      (orderedSubcomplex facets).ι ≫ nerveOrderEmb e := by
  simp [orderedSSetMapFacetsIso]

/-- Forget that an ordered selected-face realization lies in its affine carrier. -/
def selectedFacesOrderedRealizationToAmbient {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    SSet.toTop.obj (orderedSSet (selectedFaceFacets I)) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
  (TopCat.isoOfHomeo
      (selectedFacesOrderedRealizationHomeomorphCarrier I)).hom ≫
    TopCat.ofHom (selectedFacesCarrierIncl I)

theorem selectedFacesOrderedRealizationToAmbient_eq {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    selectedFacesOrderedRealizationToAmbient I =
      SSet.toTop.map (orderedSubcomplex (selectedFaceFacets I)).ι ≫
        (SSet.toTop.mapIso (finNerveIso (n + 1)).symm).hom ≫
          (TopCat.isoOfHomeo
            (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))).hom := by
  change (SSet.toTop.mapIso (selectedFacesOrderedSSetIso I).symm).hom ≫
      (TopCat.isoOfHomeo (selectedFacesRealizationHomeomorphCarrier I)).hom ≫
        TopCat.ofHom (selectedFacesCarrierIncl I) = _
  change (SSet.toTop.mapIso (selectedFacesOrderedSSetIso I).symm).hom ≫
      selectedFacesRealizationToAmbient I = _
  rw [selectedFacesRealizationToAmbient_eq]
  have hs :
      (selectedFacesOrderedSSetIso I).inv ≫
          (selectedFacesSubcomplex I).ι =
        (orderedSubcomplex (selectedFaceFacets I)).ι ≫
          (finNerveIso (n + 1)).inv := by
    rw [← cancel_mono (finNerveIso (n + 1)).hom]
    simp only [Category.assoc]
    rw [← selectedFacesOrderedSSetIso_hom_ι]
    simp
  let τ : SSet.toTop.obj (Δ[n + 1] : SSet) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
    (TopCat.isoOfHomeo
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))).hom
  change (SSet.toTop.map (selectedFacesOrderedSSetIso I).inv ≫
      SSet.toTop.map (selectedFacesSubcomplex I).ι) ≫ τ =
    (SSet.toTop.map (orderedSubcomplex (selectedFaceFacets I)).ι ≫
      SSet.toTop.map (finNerveIso (n + 1)).inv) ≫ τ
  have ht := congrArg (fun f ↦ SSet.toTop.map f) hs
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun f ↦ f ≫ τ) ht

/-- The ordered selected-face bistellar homeomorphism is the identity on the common ordered
subcomplex. -/
theorem selectedFacesOrderedBistellarHomeomorph_common {n : ℕ}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE
        (inf_le_left :
          orderedSubcomplex (selectedFaceFacets B) ⊓
              orderedSubcomplex (selectedFaceFacets A) ≤
            orderedSubcomplex (selectedFaceFacets B))) ≫
      (TopCat.isoOfHomeo
        (selectedFacesOrderedBistellarHomeomorph A B hA hB hdisj hcover)).hom =
    SSet.toTop.map (SSet.Subcomplex.homOfLE
      (inf_le_right :
        orderedSubcomplex (selectedFaceFacets B) ⊓
            orderedSubcomplex (selectedFaceFacets A) ≤
          orderedSubcomplex (selectedFaceFacets A))) := by
  let common : (CategoryTheory.nerve (Fin (n + 2))).Subcomplex :=
    orderedSubcomplex (selectedFaceFacets B) ⊓
      orderedSubcomplex (selectedFaceFacets A)
  let oldIncl : (common : SSet) ⟶ orderedSSet (selectedFaceFacets B) :=
    SSet.Subcomplex.homOfLE
      (show common ≤ orderedSubcomplex (selectedFaceFacets B) from inf_le_left)
  let newIncl : (common : SSet) ⟶ orderedSSet (selectedFaceFacets A) :=
    SSet.Subcomplex.homOfLE
      (show common ≤ orderedSubcomplex (selectedFaceFacets A) from inf_le_right)
  have hincl :
      oldIncl ≫ (orderedSubcomplex (selectedFaceFacets B)).ι =
        newIncl ≫ (orderedSubcomplex (selectedFaceFacets A)).ι := by
    rfl
  have hamb :
      SSet.toTop.map oldIncl ≫ selectedFacesOrderedRealizationToAmbient B =
        SSet.toTop.map newIncl ≫ selectedFacesOrderedRealizationToAmbient A := by
    rw [selectedFacesOrderedRealizationToAmbient_eq,
      selectedFacesOrderedRealizationToAmbient_eq]
    have ht :
        SSet.toTop.map oldIncl ≫
            SSet.toTop.map (orderedSubcomplex (selectedFaceFacets B)).ι =
          SSet.toTop.map newIncl ≫
            SSet.toTop.map (orderedSubcomplex (selectedFaceFacets A)).ι := by
      rw [← (SSet.toTop).map_comp, ← (SSet.toTop).map_comp, hincl]
    let τ : SSet.toTop.obj (CategoryTheory.nerve (Fin (n + 2))) ⟶
        TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
      (SSet.toTop.mapIso (finNerveIso (n + 1)).symm).hom ≫
        (TopCat.isoOfHomeo
          (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))).hom
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ τ) ht
  apply ConcreteCategory.hom_ext
  intro x
  change selectedFacesOrderedBistellarHomeomorph A B hA hB hdisj hcover
      (SSet.toTop.map oldIncl x) = SSet.toTop.map newIncl x
  let yOld : finsetFaceCarrier B :=
    selectedFacesOrderedRealizationHomeomorphCarrier B (SSet.toTop.map oldIncl x)
  let yNew : finsetFaceCarrier A :=
    selectedFacesOrderedRealizationHomeomorphCarrier A (SSet.toTop.map newIncl x)
  have hy : yOld.1 = yNew.1 := by
    exact ConcreteCategory.congr_hom hamb x
  obtain ⟨a, ha⟩ := yNew.2
  have haOld : yOld.1 a.1 = 0 := by rw [hy]; exact ha
  have hfixed := finsetFaceCarrierBistellarHomeomorph_fixed
    A B hA hB hdisj hcover yOld a haOld
  rw [selectedFacesOrderedBistellarHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply]
  apply (selectedFacesOrderedRealizationHomeomorphCarrier A).injective
  rw [Homeomorph.apply_symm_apply]
  change finsetFaceCarrierBistellarHomeomorph A B hA hB hdisj hcover yOld = yNew
  apply Subtype.ext
  exact hfixed.trans hy

end Submission.FiniteOrderedComplex
