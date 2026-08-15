/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.FiniteOrderedComplexSSet

/-!
# Maps of finite ordered complexes

A monotone map of vertex orders induces a simplicial map between ordered nerves.  This file
restricts that ambient nerve map to complexes presented by finite facet families, provided the
image of every source facet is a face of the target family.  Unlike reindexing, the vertex map
may identify vertices; this is the form needed for finite simplicial quotient maps.
-/

namespace Submission.FiniteOrderedComplex

open CategoryTheory Simplicial

variable {V W : Type} [LinearOrder V] [LinearOrder W]

/-- A monotone vertex map carries one finite facet presentation into another when the image of
every listed source facet is contained in a listed target facet. -/
def FacetFamilyMapsTo (f : V →o W)
    (source : Finset (Finset V)) (target : Finset (Finset W)) : Prop :=
  ∀ facet ∈ source, IsFace target (facet.image f)

/-- A facet-family map sends every generated face to a generated target face. -/
theorem FacetFamilyMapsTo.isFace_image
    {f : V →o W} {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target)
    {σ : Finset V} (hσ : IsFace source σ) :
    IsFace target (σ.image f) := by
  rcases hσ with ⟨facet, hfacet, hsubset⟩
  rcases h facet hfacet with ⟨targetFacet, htargetFacet, himage⟩
  exact ⟨targetFacet, htargetFacet,
    (Finset.image_mono f hsubset).trans himage⟩

/-- Restriction of the nerve map induced by a monotone vertex map to two ordered finite
complexes. -/
def orderedSSetMapOfMonotone
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target) :
    orderedSSet source ⟶ orderedSSet target where
  app := fun Δ ↦ ↾fun x ↦
    ⟨(CategoryTheory.nerveMap f.monotone.functor).app Δ x.1, by
      rcases x.2 with ⟨facet, hfacet, hx⟩
      rcases h facet hfacet with ⟨targetFacet, htargetFacet, himage⟩
      refine ⟨targetFacet, htargetFacet, fun i ↦ himage ?_⟩
      exact Finset.mem_image.mpr ⟨x.1.obj i, hx i, rfl⟩⟩
  naturality _ _ φ := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.nerveMap f.monotone.functor).naturality φ) x.1

/-- On vertices, the restricted simplicial map is the original monotone map. -/
@[simp]
theorem orderedSSetMapOfMonotone_app_obj
    (f : V →o W) {source : Finset (Finset V)} {target : Finset (Finset W)}
    (h : FacetFamilyMapsTo f source target)
    (Δ : SimplexCategoryᵒᵖ) (x : (orderedSSet source).obj Δ)
    (i : Fin (Δ.unop.len + 1)) :
    ((orderedSSetMapOfMonotone f h).app Δ x).1.obj i = f (x.1.obj i) :=
  rfl

end Submission.FiniteOrderedComplex
