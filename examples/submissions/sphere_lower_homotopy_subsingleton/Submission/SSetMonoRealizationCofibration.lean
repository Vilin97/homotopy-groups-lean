/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Submission.SSetBoundaryRealization
import Submission.WhiteheadTheorem.HEP.Cofibration

/-!
# Cofibrations from simplicial monomorphisms

Every simplicial monomorphism is a relative cell complex built from standard-simplex boundary
inclusions.  This file proves directly that the geometric realization of each such boundary
inclusion has the homotopy extension property, then propagates that property through coproducts,
pushouts, and transfinite compositions.  Consequently, every simplicial monomorphism realizes
to a topological cofibration.
-/

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped TopCat

universe w v v' u u'

namespace Submission

private def topologicalCofibrationProperty : MorphismProperty TopCat.{0} :=
  fun _ _ i ↦ IsCofibration i

private instance : topologicalCofibrationProperty.RespectsIso :=
  MorphismProperty.RespectsIso.mk topologicalCofibrationProperty
    (by
      intro X Y Z e f hf
      letI : IsCofibration f := hf
      exact IsCofibration.of_comp_left e.hom f)
    (by
      intro X Y Z e f hf
      letI : IsCofibration f := hf
      exact IsCofibration.of_comp_left f e.hom)

private instance : topologicalCofibrationProperty.IsStableUnderCobaseChange where
  of_isPushout h hf := h.isCofibration hf

private instance : MorphismProperty.IsStableUnderCoproducts.{0}
    topologicalCofibrationProperty where
  isStableUnderCoproductsOfShape J := by
    apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
    intro A B _ _ f hf
    exact @IsCofibration.of_sigma_map J A B f (fun j ↦ hf j)

set_option backward.isDefEq.respectTransparency false in
private instance {J : Type} [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] :
    topologicalCofibrationProperty.IsStableUnderTransfiniteCompositionOfShape J where
  le _ _ f hf := by
    obtain ⟨h⟩ := hf
    have hincl : IsCofibration (h.incl.app ⊥) := by
      constructor
      intro Y
      exact
        ⟨HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
          (hc := h.isColimit)
          (fun j hj ↦ ((h.map_mem j hj).hasCurriedHEP Y).hasLift)⟩
    exact (topologicalCofibrationProperty.arrow_mk_iso_iff
      (Arrow.isoMk h.isoBot.symm (Iso.refl _))).2 hincl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def mapSigmaMapArrowIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    (F : Functor C D) {J : Type w} (A B : J → C)
    (f : (j : J) → A j ⟶ B j)
    [HasCoproduct A] [HasCoproduct B]
    [HasCoproduct (fun j ↦ F.obj (A j))]
    [HasCoproduct (fun j ↦ F.obj (B j))]
    [PreservesColimit (Discrete.functor A) F]
    [PreservesColimit (Discrete.functor B) F] :
    Arrow.mk (F.map (Limits.Sigma.map f)) ≅
      Arrow.mk (Limits.Sigma.map (fun j : J ↦ F.map (f j))) := by
  refine Arrow.isoMk (PreservesCoproduct.iso F A)
    (PreservesCoproduct.iso F B) ?_
  apply (isColimitOfHasCoproductOfPreservesColimit F A).hom_ext
  intro j
  simp only [Cofan.mk_ι_app, Arrow.mk_hom]
  have hA : (PreservesCoproduct.iso F A).hom =
      inv (sigmaComparison F A) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← PreservesCoproduct.inv_hom]
    exact (PreservesCoproduct.iso F A).inv_hom_id
  have hB : (PreservesCoproduct.iso F B).hom =
      inv (sigmaComparison F B) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← PreservesCoproduct.inv_hom]
    exact (PreservesCoproduct.iso F B).inv_hom_id
  rw [hA, hB]
  rw [← Category.assoc,
    map_ι_comp_inv_sigmaComparison,
    Sigma.ι_map]
  rw [← Category.assoc, ← F.map_comp, Sigma.ι_map, F.map_comp,
    Category.assoc,
    map_ι_comp_inv_sigmaComparison]

private def simplicialRealizationCofibrationProperty : MorphismProperty SSet.{0} :=
  topologicalCofibrationProperty.inverseImage SSet.toTop.{0}

private instance : simplicialRealizationCofibrationProperty.RespectsIso := by
  unfold simplicialRealizationCofibrationProperty
  infer_instance

private instance : MorphismProperty.IsStableUnderCoproducts.{0}
    simplicialRealizationCofibrationProperty where
  isStableUnderCoproductsOfShape J := by
    apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
    intro A B _ _ f hf
    have hsigma : topologicalCofibrationProperty
        (Limits.Sigma.map (fun j : J ↦ SSet.toTop.map (f j))) :=
      @IsCofibration.of_sigma_map J
        (fun j ↦ SSet.toTop.{0}.obj (A j))
        (fun j ↦ SSet.toTop.{0}.obj (B j))
        (fun j ↦ SSet.toTop.{0}.map (f j)) (fun j ↦ hf j)
    exact (topologicalCofibrationProperty.arrow_mk_iso_iff
      (mapSigmaMapArrowIso SSet.toTop.{0} A B f)).2 hsigma

private instance : simplicialRealizationCofibrationProperty.IsStableUnderCobaseChange where
  of_isPushout h hf := (h.map SSet.toTop.{0}).isCofibration hf

private theorem realization_isCofibration_of_mono_of_boundary
    {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i]
    (hboundary : ∀ n : ℕ,
      IsCofibration (SSet.toTop.{0}.map (SSet.boundary.{0} n).ι)) :
    IsCofibration (SSet.toTop.{0}.map i) := by
  let c := SSet.relativeCellComplexOfMono i
  have hcells : ∀ s : c.Cells,
      simplicialRealizationCofibrationProperty
        (SSet.boundary s.j).ι := fun s ↦ by
          change IsCofibration
            (SSet.toTop.{0}.map (SSet.boundary.{0} s.j).ι)
          exact hboundary s.j
  have h := c.transfiniteCompositionOfShape'
    (I := simplicialRealizationCofibrationProperty) hcells
  have hle :
      (MorphismProperty.coproducts.{0} simplicialRealizationCofibrationProperty).pushouts ≤
        simplicialRealizationCofibrationProperty := by
    rw [MorphismProperty.pushouts_le_iff]
    exact MorphismProperty.coproducts_le simplicialRealizationCofibrationProperty
  letI : PreservesWellOrderContinuousOfShape ℕ SSet.toTop.{0} := by
    constructor
    intro j hj
    infer_instance
  have hrealization := (h.ofLE hle).map
  exact topologicalCofibrationProperty.transfiniteCompositionsOfShape_le ℕ _
    hrealization.mem

private noncomputable def standardSimplexRealizationHomeomorphDisk (n : ℕ) :
    SSet.toTop.{0}.obj (Δ[n] : SSet.{0}) ≃ₜ TopCat.disk.{0} n :=
  (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).trans
    (Submission.simplexHomeoDisk' n)

private noncomputable def standardBoundaryRealizationHomeomorphDiskBoundary (n : ℕ) :
    SSet.toTop.{0}.obj (SSet.boundary.{0} (n + 1) : SSet.{0}) ≃ₜ
      TopCat.diskBoundary.{0} (n + 1) :=
  (Submission.boundaryRealizationHomeomorphBdry n).trans
    (Submission.bdryHomeoDiskBoundary (n + 1))

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryRealization_toTopHomeo_inclusion (n : ℕ)
    (x : SSet.toTop.{0}.obj (SSet.boundary.{0} (n + 1) : SSet.{0})) :
    SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
        (SSet.toTop.{0}.map (SSet.boundary.{0} (n + 1)).ι x) =
      (Submission.boundaryRealizationToBdry (n + 1) x).1 := by
  let b := Submission.boundaryRealizationToBdry (n + 1) x
  have hx : Submission.boundaryRealizationFromBdry n b = x :=
    (Submission.boundaryRealizationHomeomorphBdry n).symm_apply_apply x
  have hfb : Submission.boundaryRealizationToBdry (n + 1)
      (Submission.boundaryRealizationFromBdry n b) = b := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom
        (Submission.boundaryRealizationFromBdry_comp_toBdry n) b
  obtain ⟨i, y, hb⟩ := Submission.boundaryPoint_existsFace b
  rw [← hx, hfb, ← hb, Submission.boundaryRealizationFromBdry_faceMap]
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    SSet.boundary.ι_ι]
  change SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
      (SSet.toTop.map
        (SSet.stdSimplex.map (SimplexCategory.δ i))
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) =
    Submission.faceMap i y
  rw [SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply,
    Submission.stdSimplexMap_delta_eq_faceMap]

private theorem standardBoundaryRealizationHomeomorphDiskBoundary_commutes (n : ℕ)
    (x : SSet.toTop.{0}.obj (SSet.boundary.{0} (n + 1) : SSet.{0})) :
    TopCat.diskBoundaryIncl (n + 1)
        (standardBoundaryRealizationHomeomorphDiskBoundary n x) =
      standardSimplexRealizationHomeomorphDisk (n + 1)
        (SSet.toTop.{0}.map (SSet.boundary.{0} (n + 1)).ι x) := by
  apply ULift.ext
  apply Subtype.ext
  change (Submission.simplexHomeoBall (n + 1)
      (Submission.boundaryRealizationToBdry (n + 1) x).1).1 =
    (Submission.simplexHomeoBall (n + 1)
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))
        (SSet.toTop.{0}.map (SSet.boundary.{0} (n + 1)).ι x))).1
  rw [boundaryRealization_toTopHomeo_inclusion]

private theorem standardBoundaryRealizationIncl_isCofibration_succ (n : ℕ) :
    IsCofibration
      (SSet.toTop.{0}.map (SSet.boundary.{0} (n + 1)).ι) := by
  apply (IsCofibration.iff_hasHomotopyExtensionProperty _).2
  intro (Y : TopCat.{0})
  exact Submission.hasHEP_of_homeomorph
    (standardBoundaryRealizationHomeomorphDiskBoundary n)
    (standardSimplexRealizationHomeomorphDisk (n + 1))
    (standardBoundaryRealizationHomeomorphDiskBoundary_commutes n)
    (TopCat.diskBoundaryIncl_hasHEP.{0} (n + 1) Y)

private theorem isCofibration_of_isEmpty_domain {A X : TopCat.{0}} (i : A ⟶ X)
    [IsEmpty A] : IsCofibration i := by
  apply (IsCofibration.iff_hasHomotopyExtensionProperty i).2
  intro Y f h _
  refine ⟨⟨fun p ↦ f p.1, f.continuous.comp continuous_fst⟩, ?_, ?_⟩
  · funext x
    rfl
  · funext p
    exact isEmptyElim p.1

private noncomputable def standardBoundaryZero_isInitial :
    IsInitial (SSet.boundary.{0} 0 : SSet.{0}) := by
  rw [SSet.boundary_zero]
  exact SSet.Subcomplex.isInitialBot

private theorem standardBoundaryZeroRealization_isEmpty :
    IsEmpty
      (SSet.toTop.{0}.obj (SSet.boundary.{0} 0 : SSet.{0})) := by
  have h : IsInitial
      (SSet.toTop.{0}.obj (SSet.boundary.{0} 0 : SSet.{0})) :=
    standardBoundaryZero_isInitial.isInitialObj SSet.toTop.{0}
  exact CategoryTheory.Limits.Concrete.empty_of_initial_of_preserves _
    ⟨h⟩

private theorem standardBoundaryRealizationIncl_isCofibration_zero :
    IsCofibration
      (SSet.toTop.{0}.map (SSet.boundary.{0} 0).ι) := by
  letI : IsEmpty
      (SSet.toTop.{0}.obj (SSet.boundary.{0} 0 : SSet.{0})) :=
    standardBoundaryZeroRealization_isEmpty
  exact isCofibration_of_isEmpty_domain _

/-- The geometric realization of the boundary inclusion of every standard simplex is a
topological cofibration. -/
theorem standardBoundaryRealizationIncl_isCofibration (n : ℕ) :
    IsCofibration
      (SSet.toTop.{0}.map (SSet.boundary.{0} n).ι) := by
  cases n with
  | zero => exact standardBoundaryRealizationIncl_isCofibration_zero
  | succ n => exact standardBoundaryRealizationIncl_isCofibration_succ n

/-- The geometric realization of every simplicial monomorphism is a topological cofibration. -/
theorem geometricRealization_isCofibration_of_mono
    {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    IsCofibration (SSet.toTop.{0}.map i) :=
  realization_isCofibration_of_mono_of_boundary i
    standardBoundaryRealizationIncl_isCofibration

end Submission
