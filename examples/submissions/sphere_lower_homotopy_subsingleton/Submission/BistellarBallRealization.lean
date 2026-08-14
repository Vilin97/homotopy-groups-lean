/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.BistellarLocalReindex
import Submission.FiniteOrderedSimplexRealization

/-!
# Realization of a simplicial cone over a simplex boundary

The cone from an external apex over the boundary of an `n`-simplex is the old local ball in the
bistellar replacement with singleton old core.  The explicit local bistellar homeomorphism sends
it to the one-facet `n`-simplex, whose realization is the exact closed `n`-disk.

## Main result

* `Submission.FiniteOrderedComplex.bistellarConeRealizationHomeomorphDisk` identifies the
  realization of the finite cone facet family with the exact disk.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.FiniteOrderedComplex

variable {V : Type} [LinearOrder V]

/-- Replacing a singleton old core leaves one new facet. -/
theorem bistellarNewFacets_singleton (apex : V) (vertices : Finset V) :
    bistellarNewFacets {apex} vertices = {vertices} := by
  simp [bistellarNewFacets]

/-- The old facets for a singleton core are exactly the cone over the boundary of the opposite
simplex. -/
theorem bistellarOldFacets_singleton_eq_cone (apex : V) (vertices : Finset V) :
    bistellarOldFacets {apex} vertices =
      (simplexBoundaryFacets vertices).image (fun σ ↦ insert apex σ) := by
  rw [bistellarOldFacets, simplexBoundaryFacets, Finset.image_image]
  apply Finset.image_congr
  intro b hb
  simp

/-- The realization of a cone from an external apex over a finite simplex boundary is an exact
closed disk. -/
def bistellarConeRealizationHomeomorphDisk
    (dimension : ℕ) (apex : V) (vertices : Finset V)
    (hapex : apex ∉ vertices) (hcard : vertices.card = dimension + 1) :
    SSet.toTop.obj (orderedSSet (bistellarOldFacets {apex} vertices)) ≃ₜ
      TopCat.disk.{0} dimension := by
  have hvertices : vertices.Nonempty := Finset.card_pos.mp (by omega)
  have hdisj : Disjoint ({apex} : Finset V) vertices := by
    simp [hapex]
  have hunion : (({apex} : Finset V) ∪ vertices).card = dimension + 2 := by
    rw [Finset.singleton_union, Finset.card_insert_of_notMem hapex, hcard]
  exact (bistellarLocalRealizationHomeomorph
      {apex} vertices (by simp) hvertices hdisj hunion).trans
    ((TopCat.homeoOfIso (SSet.toTop.mapIso
      (SSet.Subcomplex.eqToIso
        (congrArg orderedSubcomplex
          (bistellarNewFacets_singleton apex vertices))))).trans
      (simplexRealizationHomeomorphDisk dimension vertices hcard))

end Submission.FiniteOrderedComplex
