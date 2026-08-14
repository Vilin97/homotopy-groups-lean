/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.SSetBoundaryRealization

/-!
# Realization of selected standard-simplex faces

For any finite collection `I` of codimension-one faces of a standard simplex, this file identifies
the realization of their simplicial union with the corresponding union of affine faces.  The
forward map realizes each simplex affinely.  Its inverse glues the realized face inclusions over a
finite closed cover; compatibility on face intersections follows from the cosimplicial identities.

This generalizes the full-boundary comparison to arbitrary face families, including the two local
balls in a bistellar move.

## Main results

* `Submission.selectedFacesRealizationHomeomorphCarrier`: realization of any selected face union
  is homeomorphic to its affine carrier;
* `Submission.selectedFacesRealizationToCarrier_comp_ι`: the comparison is the standard affine
  map on each selected face;
* `Submission.glueSelectedFaces`: continuous gluing over a selected finite family of faces.
-/

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Submission

universe u

/-- The union of a selected finite collection of codimension-one faces. -/
def selectedFacesSubcomplex {n : ℕ} (I : Finset (Fin (n + 2))) :
    (Δ[n + 1] : SSet.{u}).Subcomplex :=
  ⨆ i : I, SSet.stdSimplex.face {i.1}ᶜ

/-- Inclusion of a selected codimension-one face. -/
def selectedFacesι {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    (Δ[n] : SSet.{u}) ⟶ selectedFacesSubcomplex I :=
  SSet.Subcomplex.lift (SSet.stdSimplex.δ i.1) (by
    rw [SSet.stdSimplex.range_δ]
    exact le_iSup (fun j : I ↦ SSet.stdSimplex.face {j.1}ᶜ) i)

@[reassoc (attr := simp)]
theorem selectedFacesι_ι {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    selectedFacesι I i ≫ (selectedFacesSubcomplex I).ι = SSet.stdSimplex.δ i.1 := rfl

instance selectedFacesι_mono {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    Mono (selectedFacesι.{u} I i) := by
  exact mono_of_mono_fac (selectedFacesι_ι I i)

/-- Maps out of a selected union of faces are determined facewise. -/
theorem selectedFaces_hom_ext {n : ℕ} (I : Finset (Fin (n + 2)))
    {X : SSet.{u}} {f g : (selectedFacesSubcomplex I : SSet) ⟶ X}
    (h : ∀ i : I, selectedFacesι I i ≫ f = selectedFacesι I i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp only [selectedFacesSubcomplex, Subfunctor.iSup_obj,
    Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  rw [SSet.stdSimplex.face_singleton_compl,
    SSet.Subcomplex.mem_ofSimplex_obj_iff] at hi
  obtain ⟨y, rfl⟩ := hi
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

/-- The corresponding union of affine faces. -/
abbrev selectedFacesCarrier {n : ℕ} (I : Finset (Fin (n + 2))) : Type :=
  {x : stdSimplex ℝ (Fin (n + 2)) // ∃ i : I, x.1 i.1 = 0}

/-- The affine inclusion of a selected face. -/
def selectedAffineFace {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    C(stdSimplex ℝ (Fin (n + 1)), selectedFacesCarrier I) where
  toFun x := ⟨faceMap i.1 x, ⟨i, faceMap_coe_same i.1 x⟩⟩
  continuous_toFun := Continuous.subtype_mk (continuous_faceMap i.1) _

/-- A selected face inclusion with source the realization of the standard simplex. -/
def selectedTopologicalFace {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    SSet.toTop.obj (Δ[n] : SSet) ⟶ TopCat.of (selectedFacesCarrier I) :=
  TopCat.ofHom ((selectedAffineFace I i).comp
    ⟨SimplexCategory.toTopHomeo (SimplexCategory.mk n),
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous⟩)

/-- A simplex in a selected face union realizes affinely inside that union. -/
def selectedFacesTopologicalSimplexMap {n : ℕ} {I : Finset (Fin (n + 2))}
    {Δ : SimplexCategoryᵒᵖ} (s : (selectedFacesSubcomplex I : SSet).obj Δ) :
    C(stdSimplex ℝ (Fin (Δ.unop.len + 1)), selectedFacesCarrier I) where
  toFun x := ⟨stdSimplex.map (SSet.stdSimplex.objEquiv s.1).toOrderHom x, by
    have hs := s.2
    change s.1 ∈ (⨆ i : I, SSet.stdSimplex.face {i.1}ᶜ).obj Δ at hs
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hs
    obtain ⟨i, hi⟩ := hs
    refine ⟨i, ?_⟩
    change (FunOnFinite.linearMap ℝ ℝ
      (SSet.stdSimplex.objEquiv s.1).toOrderHom x) i.1 = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_filter] at hj
    have hsji : (SSet.stdSimplex.objEquiv s.1).toOrderHom j ≠ i.1 := by
      change Finset.image (SSet.stdSimplex.objEquiv s.1).toOrderHom Finset.univ ≤
        {i.1}ᶜ at hi
      have hmem := hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      simpa only [Finset.mem_compl, Finset.mem_singleton] using hmem
    exact False.elim (hsji hj.2)⟩
  continuous_toFun := Continuous.subtype_mk (stdSimplex.continuous_map _) _

/-- Naturality of affine realization for selected face unions. -/
theorem selectedFacesTopologicalSimplexMap_naturality {n : ℕ}
    {I : Finset (Fin (n + 2))} {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (s : (selectedFacesSubcomplex I : SSet).obj Δ) :
    selectedFacesTopologicalSimplexMap ((selectedFacesSubcomplex I : SSet).map f s) =
      (selectedFacesTopologicalSimplexMap s).comp
        ⟨stdSimplex.map f.unop.toOrderHom, stdSimplex.continuous_map _⟩ := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change stdSimplex.map _ x = stdSimplex.map _ (stdSimplex.map _ x)
  rw [stdSimplex.map_comp_apply]
  rfl

/-- Degreewise affine selected-face simplices. -/
def selectedFacesToSingularApp {n : ℕ} (I : Finset (Fin (n + 2)))
    (Δ : SimplexCategoryᵒᵖ) :
    (selectedFacesSubcomplex I : SSet).obj Δ ⟶
      (TopCat.toSSet.obj (TopCat.of (selectedFacesCarrier I))).obj Δ :=
  ↾fun s ↦ (TopCat.toSSetObjEquiv _ _).symm (selectedFacesTopologicalSimplexMap s)

theorem selectedFacesToSingularApp_naturality {n : ℕ}
    (I : Finset (Fin (n + 2))) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (selectedFacesSubcomplex I : SSet).map f ≫ selectedFacesToSingularApp I Δ' =
      selectedFacesToSingularApp I Δ ≫
        (TopCat.toSSet.obj (TopCat.of (selectedFacesCarrier I))).map f := by
  ext s
  apply (TopCat.toSSetObjEquiv _ _).injective
  change selectedFacesTopologicalSimplexMap ((selectedFacesSubcomplex I : SSet).map f s) =
    (selectedFacesTopologicalSimplexMap s).comp
      ⟨stdSimplex.map f.unop.toOrderHom, stdSimplex.continuous_map _⟩
  exact selectedFacesTopologicalSimplexMap_naturality f s

/-- Selected-face simplices map to the singular complex of their affine carrier. -/
def selectedFacesToSingular {n : ℕ} (I : Finset (Fin (n + 2))) :
    (selectedFacesSubcomplex I : SSet) ⟶
      TopCat.toSSet.obj (TopCat.of (selectedFacesCarrier I)) where
  app := selectedFacesToSingularApp I
  naturality _ _ f := selectedFacesToSingularApp_naturality I f

/-- The canonical affine realization map for a selected union of faces. -/
def selectedFacesRealizationToCarrier {n : ℕ} (I : Finset (Fin (n + 2))) :
    SSet.toTop.obj (selectedFacesSubcomplex I) ⟶
      TopCat.of (selectedFacesCarrier I) :=
  (sSetTopAdj.homEquiv _ _).symm (selectedFacesToSingular I)

/-- On a selected realized face, the canonical map is the corresponding affine face map. -/
theorem selectedFacesRealizationToCarrier_comp_ι {n : ℕ}
    (I : Finset (Fin (n + 2))) (i : I) :
    SSet.toTop.map (selectedFacesι I i) ≫ selectedFacesRealizationToCarrier I =
      selectedTopologicalFace I i := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [show (sSetTopAdj.homEquiv _ _) (selectedFacesRealizationToCarrier I) =
      selectedFacesToSingular I by exact Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_unit]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  apply (TopCat.toSSetObjEquiv _ _).injective
  change selectedFacesTopologicalSimplexMap.{0}
      (SSet.yonedaEquiv (selectedFacesι.{0} I i)) =
    (selectedTopologicalFace I i).hom.comp
      ((TopCat.toSSetObjEquiv
        (SSet.toTop.obj (Δ[n] : SSet)) (op (SimplexCategory.mk n)))
          (SSet.yonedaEquiv (sSetTopAdj.unit.app (Δ[n] : SSet))))
  rw [toSSetObjEquiv_yonedaEquiv_unit_stdSimplex]
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change stdSimplex.map
      (SSet.stdSimplex.objEquiv
        (SSet.yonedaEquiv (selectedFacesι.{0} I i)).1).toOrderHom x =
    faceMap i.1 ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm x))
  rw [Homeomorph.apply_symm_apply]
  have hs : SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv (selectedFacesι.{0} I i)).1 = SimplexCategory.δ i.1 := by
    change SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv
        (selectedFacesι.{0} I i ≫ (selectedFacesSubcomplex I).ι)) =
          SimplexCategory.δ i.1
    rw [selectedFacesι_ι]
    change SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv
        (SSet.stdSimplex.{0}.map (SimplexCategory.δ i.1))) =
          SimplexCategory.δ i.1
    rw [SSet.yonedaEquiv_map, Equiv.apply_symm_apply]
  rw [hs]
  exact stdSimplexMap_delta_eq_faceMap i.1 x

section SelectedFaceGluing

variable {n : ℕ} (I : Finset (Fin (n + 2)))
  {Z : Type} [TopologicalSpace Z]
  (g : I → C(stdSimplex ℝ (Fin (n + 1)), Z))
  (hg : ∀ (i k : I) (y z : stdSimplex ℝ (Fin (n + 1))),
    faceMap i.1 y = faceMap k.1 z → g i y = g k z)

/-- A selected face containing a point of the selected affine carrier. -/
def selectedFacesIdx (b : selectedFacesCarrier I) : I := b.2.choose

theorem selectedFacesIdx_spec (b : selectedFacesCarrier I) :
    b.1.1 (selectedFacesIdx I b).1 = 0 := b.2.choose_spec

include hg in
theorem glueSelectedFaces_aux (b : selectedFacesCarrier I) (i : I)
    (hi : b.1.1 i.1 = 0) :
    g (selectedFacesIdx I b) (dropMap _ (selectedFacesIdx_spec I b)) =
      g i (dropMap i.1 hi) :=
  hg _ _ _ _ ((faceMap_dropMap _ (selectedFacesIdx_spec I b)).trans
    (faceMap_dropMap i.1 hi).symm)

/-- The function obtained by gluing maps over a selected collection of affine faces. -/
def glueSelectedFacesFun (b : selectedFacesCarrier I) : Z :=
  g (selectedFacesIdx I b) (dropMap _ (selectedFacesIdx_spec I b))

include hg in
theorem continuous_glueSelectedFacesFun : Continuous (glueSelectedFacesFun I g) := by
  set S : I → Set (selectedFacesCarrier I) :=
    fun i => {b | b.1.1 i.1 = 0} with hS
  have hcont : Continuous fun b : selectedFacesCarrier I =>
      (b.1.1 : Fin (n + 2) → ℝ) :=
    (continuous_subtype_val : Continuous fun x : stdSimplex ℝ (Fin (n + 2)) => x.1).comp
      (continuous_subtype_val : Continuous fun x : selectedFacesCarrier I => x.1)
  refine (locallyFinite_of_finite S).continuous ?_ (fun i => ?_) (fun i => ?_)
  · refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨i, hi⟩ := b.2
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  · exact isClosed_eq ((continuous_apply i.1).comp hcont) continuous_const
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (S i).restrict (glueSelectedFacesFun I g) =
        fun b : S i => g i (dropMap i.1 b.2) := by
      funext b
      exact glueSelectedFaces_aux I g hg b.1 i b.2
    rw [heq]
    refine (map_continuous (g i)).comp
      (Continuous.subtype_mk (continuous_pi fun k => ?_) _)
    exact (continuous_apply _).comp (hcont.comp continuous_subtype_val)

include hg in
/-- A continuous map glued over any selected finite collection of simplex faces. -/
def glueSelectedFaces : C(selectedFacesCarrier I, Z) :=
  ⟨glueSelectedFacesFun I g, continuous_glueSelectedFacesFun I g hg⟩

include hg in
@[simp]
theorem glueSelectedFaces_faceMap (i : I) (y : stdSimplex ℝ (Fin (n + 1))) :
    glueSelectedFaces I g hg (selectedAffineFace I i y) = g i y := by
  show glueSelectedFacesFun I g (selectedAffineFace I i y) = g i y
  rw [glueSelectedFacesFun,
    glueSelectedFaces_aux I g hg (selectedAffineFace I i y) i (faceMap_coe_same i.1 y)]
  congr 1
  apply Subtype.ext
  exact congrArg Subtype.val (dropMap_faceMap i.1 y)

end SelectedFaceGluing

/-- A selected affine face maps back to the realization by its realized simplicial inclusion. -/
def selectedFaceToRealization {n : ℕ} (I : Finset (Fin (n + 2))) (i : I) :
    C(stdSimplex ℝ (Fin (n + 1)),
      SSet.toTop.{0}.obj (selectedFacesSubcomplex.{0} I)) :=
  ⟨fun y ↦ SSet.toTop.{0}.map (selectedFacesι.{0} I i)
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y),
    (SSet.toTop.{0}.map (selectedFacesι.{0} I i)).hom.continuous.comp
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.continuous⟩

lemma selectedFaceToRealization_eq_of_lt {n : ℕ}
    (I : Finset (Fin (n + 2))) {i k : I} (hik : i.1 < k.1)
    {y z : stdSimplex ℝ (Fin (n + 1))} (h : faceMap i.1 y = faceMap k.1 z) :
    selectedFaceToRealization I i y = selectedFaceToRealization I k z := by
  obtain _ | n := n
  · exact False.elim (boundaryFaces_disjoint_zeroDim (ne_of_lt hik) y z h)
  · obtain ⟨w, rfl, rfl⟩ := boundaryFaces_exists_commonFactor hik h
    set j₀ := k.1.pred (Fin.ne_zero_of_lt hik) with hj₀
    set i₀ := i.1.castPred (Fin.ne_last_of_lt hik) with hi₀
    have hsucc : j₀.succ = k.1 := Fin.succ_pred _ _
    have hcast : i₀.castSucc = i.1 := Fin.castSucc_castPred _ _
    have hle : i₀ ≤ j₀ := by
      have h1 : (i₀ : ℕ) = (i.1 : ℕ) := rfl
      have h2 : (j₀ : ℕ) = (k.1 : ℕ) - 1 := rfl
      have h3 : (i.1 : ℕ) < (k.1 : ℕ) := hik
      rw [Fin.le_def, h1, h2]
      omega
    have hmaps :
        SSet.stdSimplex.δ j₀ ≫ selectedFacesι.{0} I i =
          SSet.stdSimplex.δ i₀ ≫ selectedFacesι.{0} I k := by
      rw [← cancel_mono (selectedFacesSubcomplex I).ι]
      simp only [Category.assoc, selectedFacesι_ι]
      rw [← hcast, ← hsucc]
      exact (SSet.stdSimplex.δ_comp_δ hle).symm
    have hmaps' :
        SSet.stdSimplex.{0}.map (SimplexCategory.δ j₀) ≫
            selectedFacesι.{0} I i =
          SSet.stdSimplex.{0}.map (SimplexCategory.δ i₀) ≫
            selectedFacesι.{0} I k := hmaps
    change SSet.toTop.map (selectedFacesι.{0} I i)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
          (faceMap j₀ w)) =
      SSet.toTop.map (selectedFacesι.{0} I k)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
          (faceMap i₀ w))
    rw [← stdSimplexMap_delta_eq_faceMap, ← stdSimplexMap_delta_eq_faceMap,
      SimplexCategory.toTopHomeo_symm_naturality_apply,
      SimplexCategory.toTopHomeo_symm_naturality_apply]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← (SSet.toTop).map_comp, ← (SSet.toTop).map_comp, hmaps']

/-- The maps from selected affine faces back to the realization agree on intersections. -/
lemma selectedFaceToRealization_compatible {n : ℕ}
    (I : Finset (Fin (n + 2))) (i k : I)
    (y z : stdSimplex ℝ (Fin (n + 1))) (h : faceMap i.1 y = faceMap k.1 z) :
    selectedFaceToRealization I i y = selectedFaceToRealization I k z := by
  rcases lt_trichotomy i.1 k.1 with hik | hik | hki
  · exact selectedFaceToRealization_eq_of_lt I hik h
  · have hik' : i = k := Subtype.ext hik
    subst k
    exact congrArg (selectedFaceToRealization I i) (faceMap_injective i.1 h)
  · exact (selectedFaceToRealization_eq_of_lt I hki h.symm).symm

/-- The inverse candidate obtained by gluing selected realized face inclusions. -/
def selectedFacesRealizationFromCarrier {n : ℕ} (I : Finset (Fin (n + 2))) :
    TopCat.of (selectedFacesCarrier I) ⟶
      SSet.toTop.obj (selectedFacesSubcomplex I) :=
  TopCat.ofHom (glueSelectedFaces I (selectedFaceToRealization I)
    (selectedFaceToRealization_compatible I))

@[simp]
theorem selectedFacesRealizationFromCarrier_faceMap {n : ℕ}
    (I : Finset (Fin (n + 2))) (i : I)
    (y : stdSimplex ℝ (Fin (n + 1))) :
    selectedFacesRealizationFromCarrier I (selectedAffineFace I i y) =
      SSet.toTop.map (selectedFacesι I i)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := by
  exact glueSelectedFaces_faceMap I (selectedFaceToRealization I)
    (selectedFaceToRealization_compatible I) i y

/-- Gluing selected faces and then applying the affine realization map is the identity. -/
theorem selectedFacesRealizationFromCarrier_comp_toCarrier {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    selectedFacesRealizationFromCarrier I ≫ selectedFacesRealizationToCarrier I =
      𝟙 (TopCat.of (selectedFacesCarrier I)) := by
  apply ConcreteCategory.hom_ext
  intro b
  obtain ⟨i, hi⟩ := b.2
  let y : stdSimplex ℝ (Fin (n + 1)) := dropMap i.1 hi
  have hb : selectedAffineFace I i y = b := by
    apply Subtype.ext
    exact faceMap_dropMap i.1 hi
  rw [← hb, ConcreteCategory.comp_apply, selectedFacesRealizationFromCarrier_faceMap]
  calc
    selectedFacesRealizationToCarrier I
        (SSet.toTop.map (selectedFacesι I i)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) =
      selectedTopologicalFace I i
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := by
          exact ConcreteCategory.congr_hom
            (selectedFacesRealizationToCarrier_comp_ι I i) _
    _ = selectedAffineFace I i y := by
      apply Subtype.ext
      change faceMap i.1
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) = faceMap i.1 y
      rw [Homeomorph.apply_symm_apply]
    _ = (𝟙 (TopCat.of (selectedFacesCarrier I))) (selectedAffineFace I i y) := rfl

/-- Maps out of a realized selected face union are determined by their face restrictions. -/
theorem selectedFacesRealization_hom_ext {n : ℕ}
    (I : Finset (Fin (n + 2))) {X : TopCat.{0}}
    {f g : SSet.toTop.obj (selectedFacesSubcomplex I) ⟶ X}
    (h : ∀ i : I,
      SSet.toTop.map (selectedFacesι I i) ≫ f =
        SSet.toTop.map (selectedFacesι I i) ≫ g) :
    f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply selectedFaces_hom_ext I
  intro i
  rw [← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left]
  exact congrArg (sSetTopAdj.homEquiv (Δ[n] : SSet) X) (h i)

theorem selectedTopologicalFace_comp_realizationFromCarrier {n : ℕ}
    (I : Finset (Fin (n + 2))) (i : I) :
    selectedTopologicalFace I i ≫ selectedFacesRealizationFromCarrier I =
      SSet.toTop.map (selectedFacesι I i) := by
  apply ConcreteCategory.hom_ext
  intro x
  change selectedFacesRealizationFromCarrier I
      (selectedAffineFace I i
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n) x)) =
    SSet.toTop.map (selectedFacesι I i) x
  rw [selectedFacesRealizationFromCarrier_faceMap]
  rw [Homeomorph.symm_apply_apply]

/-- Applying the affine map and then gluing selected faces is the identity. -/
theorem selectedFacesRealizationToCarrier_comp_fromCarrier {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    selectedFacesRealizationToCarrier I ≫ selectedFacesRealizationFromCarrier I =
      𝟙 (SSet.toTop.obj (selectedFacesSubcomplex I)) := by
  apply selectedFacesRealization_hom_ext I
  intro i
  rw [← Category.assoc, selectedFacesRealizationToCarrier_comp_ι,
    selectedTopologicalFace_comp_realizationFromCarrier, Category.comp_id]

/-- Realization of a selected union of standard-simplex faces is homeomorphic to its affine
carrier. -/
def selectedFacesRealizationHomeomorphCarrier {n : ℕ}
    (I : Finset (Fin (n + 2))) :
    SSet.toTop.obj (selectedFacesSubcomplex I) ≃ₜ selectedFacesCarrier I where
  toFun := selectedFacesRealizationToCarrier I
  invFun := selectedFacesRealizationFromCarrier I
  left_inv x := by
    have h := ConcreteCategory.congr_hom
      (selectedFacesRealizationToCarrier_comp_fromCarrier I) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  right_inv x := by
    have h := ConcreteCategory.congr_hom
      (selectedFacesRealizationFromCarrier_comp_toCarrier I) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  continuous_toFun := (selectedFacesRealizationToCarrier I).hom.continuous
  continuous_invFun := (selectedFacesRealizationFromCarrier I).hom.continuous

end Submission
