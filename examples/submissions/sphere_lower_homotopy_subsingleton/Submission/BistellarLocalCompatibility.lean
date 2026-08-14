/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarLocalRealization

/-!
# Boundary compatibility of the local bistellar homeomorphism

This file compares a selected union of simplicial faces with its affine realization inside the
ambient simplex.  It then proves that the local bistellar homeomorphism between complementary
selected face unions restricts to the identity on their common simplicial subcomplex.

## Main results

* `Submission.selectedFacesRealizationToAmbient_eq`: the selected-face affine comparison followed
  by inclusion is the realized simplicial inclusion;
* `Submission.FiniteOrderedComplex.selectedFacesRealizationBistellarHomeomorph_common`: the local
  bistellar homeomorphism commutes with both inclusions of the common subcomplex.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission

/-- Forget that an affine point lies in a selected union of faces. -/
def selectedFacesCarrierIncl {n : ℕ} (I : Finset (Fin (n + 2))) :
    C(selectedFacesCarrier I, stdSimplex ℝ (Fin (n + 2))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The selected-face realization map followed by the inclusion in the ambient affine simplex. -/
def selectedFacesRealizationToAmbient {n : ℕ} (I : Finset (Fin (n + 2))) :
    SSet.toTop.obj (selectedFacesSubcomplex I) ⟶
      TopCat.of (stdSimplex ℝ (Fin (n + 2))) :=
  selectedFacesRealizationToCarrier I ≫ TopCat.ofHom (selectedFacesCarrierIncl I)

/-- The affine selected-face comparison is the realization of the simplicial inclusion into the
ambient standard simplex. -/
theorem selectedFacesRealizationToAmbient_eq {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    selectedFacesRealizationToAmbient I =
      SSet.toTop.map (selectedFacesSubcomplex I).ι ≫
        (TopCat.isoOfHomeo
          (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)))).hom := by
  apply selectedFacesRealization_hom_ext I
  intro i
  apply ConcreteCategory.hom_ext
  intro x
  change (selectedFacesRealizationToCarrier I
      (SSet.toTop.map (selectedFacesι I i) x)).1 =
    SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
      (SSet.toTop.map (selectedFacesSubcomplex I).ι
        (SSet.toTop.map (selectedFacesι I i) x))
  rw [show selectedFacesRealizationToCarrier I
      (SSet.toTop.map (selectedFacesι I i) x) = selectedTopologicalFace I i x by
    exact ConcreteCategory.congr_hom
      (selectedFacesRealizationToCarrier_comp_ι I i) x]
  change faceMap i.1 (SimplexCategory.toTopHomeo (SimplexCategory.mk n) x) = _
  rw [← ConcreteCategory.comp_apply, ← (SSet.toTop).map_comp,
    selectedFacesι_ι]
  rw [← stdSimplexMap_delta_eq_faceMap]
  exact (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i.1) x).symm

namespace FiniteOrderedComplex

/-- The selected simplicial face unions themselves are related by the affine bistellar
homeomorphism. -/
def selectedFacesRealizationBistellarHomeomorph {n : ℕ}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    SSet.toTop.obj (selectedFacesSubcomplex B) ≃ₜ
      SSet.toTop.obj (selectedFacesSubcomplex A) :=
  (selectedFacesRealizationHomeomorphCarrier B).trans
    ((finsetFaceCarrierBistellarHomeomorph A B hA hB hdisj hcover).trans
      (selectedFacesRealizationHomeomorphCarrier A).symm)

/-- The selected-face realization bistellar homeomorphism is the identity on the realization of
the common subcomplex. -/
theorem selectedFacesRealizationBistellarHomeomorph_common {n : ℕ}
    (A B : Finset (Fin (n + 2)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Finset.univ) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE
        (inf_le_left : selectedFacesSubcomplex B ⊓ selectedFacesSubcomplex A ≤
          selectedFacesSubcomplex B)) ≫
      (TopCat.isoOfHomeo
        (selectedFacesRealizationBistellarHomeomorph A B hA hB hdisj hcover)).hom =
    SSet.toTop.map (SSet.Subcomplex.homOfLE
      (inf_le_right : selectedFacesSubcomplex B ⊓ selectedFacesSubcomplex A ≤
        selectedFacesSubcomplex A)) := by
  let common : (Δ[n + 1] : SSet.{0}).Subcomplex :=
    selectedFacesSubcomplex B ⊓ selectedFacesSubcomplex A
  let oldIncl :
      (common : SSet) ⟶
        selectedFacesSubcomplex.{0} B := SSet.Subcomplex.homOfLE
    (show common ≤ selectedFacesSubcomplex B from inf_le_left)
  let newIncl :
      (common : SSet) ⟶
        selectedFacesSubcomplex.{0} A := SSet.Subcomplex.homOfLE
    (show common ≤ selectedFacesSubcomplex A from inf_le_right)
  have hincl :
      oldIncl ≫ (selectedFacesSubcomplex.{0} B).ι =
        newIncl ≫ (selectedFacesSubcomplex.{0} A).ι := by
    rfl
  have hamb :
      SSet.toTop.map oldIncl ≫ selectedFacesRealizationToAmbient B =
        SSet.toTop.map newIncl ≫ selectedFacesRealizationToAmbient A := by
    rw [selectedFacesRealizationToAmbient_eq,
      selectedFacesRealizationToAmbient_eq,
      ← Category.assoc, ← Category.assoc,
      ← (SSet.toTop).map_comp, ← (SSet.toTop).map_comp, hincl]
  apply ConcreteCategory.hom_ext
  intro x
  change selectedFacesRealizationBistellarHomeomorph A B hA hB hdisj hcover
      (SSet.toTop.map oldIncl x) = SSet.toTop.map newIncl x
  let yOld : selectedFacesCarrier B :=
    selectedFacesRealizationHomeomorphCarrier B (SSet.toTop.map oldIncl x)
  let yNew : selectedFacesCarrier A :=
    selectedFacesRealizationHomeomorphCarrier A (SSet.toTop.map newIncl x)
  have hy : yOld.1 = yNew.1 := by
    exact ConcreteCategory.congr_hom hamb x
  obtain ⟨a, ha⟩ := yNew.2
  have haOld : yOld.1 a.1 = 0 := by rw [hy]; exact ha
  have hfixed := finsetFaceCarrierBistellarHomeomorph_fixed
    A B hA hB hdisj hcover yOld a haOld
  rw [selectedFacesRealizationBistellarHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply]
  apply (selectedFacesRealizationHomeomorphCarrier A).injective
  rw [Homeomorph.apply_symm_apply]
  change finsetFaceCarrierBistellarHomeomorph A B hA hB hdisj hcover yOld = yNew
  apply Subtype.ext
  exact hfixed.trans hy

end FiniteOrderedComplex

end Submission
