/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Submission.Cohomology.FiniteOrderedComplexSSet

/-!
# Geometric realization of a finite ordered complex

This file places the ordered simplicial-set model of a finite complex inside an ordinary
topological standard simplex.  For vertices `Fin (n + 1)`, the ambient nerve is isomorphic to the
standard simplicial `n`-simplex.  Geometric realization and the standard-simplex homeomorphism
therefore give a canonical continuous map from the realization of the finite complex to
`stdSimplex ℝ (Fin (n + 1))`.

The construction does not assert that this map is an embedding; that comparison is deliberately
kept explicit for the later identification of a concrete triangulation with its maintained
topological model.

## Main definitions

* `Submission.FiniteOrderedComplex.nerveOrderIso`: an order isomorphism induces an isomorphism of
  nerves;
* `Submission.FiniteOrderedComplex.finNerveIso`: `Δ[n]` is isomorphic to the nerve of
  `Fin (n + 1)`;
* `Submission.FiniteOrderedComplex.orderedSSetToStdSimplex`: the simplicial inclusion of an
  ordered finite complex in its ambient standard simplex;
* `Submission.FiniteOrderedComplex.orderedRealizationToTopologicalSimplex`: the corresponding
  continuous map of geometric realizations into the topological standard simplex.
-/

noncomputable section

namespace Submission

open CategoryTheory Simplicial

namespace FiniteOrderedComplex

variable {V W : Type} [LinearOrder V] [LinearOrder W]

/-- An order isomorphism induces an isomorphism between the nerves of the associated thin
categories. -/
def nerveOrderIso (e : V ≃o W) : CategoryTheory.nerve V ≅ CategoryTheory.nerve W where
  hom := CategoryTheory.nerveMap e.monotone.functor
  inv := CategoryTheory.nerveMap e.symm.monotone.functor
  hom_inv_id := by
    ext Δ x i
    exact e.symm_apply_apply (x.obj i)
  inv_hom_id := by
    ext Δ x i
    exact e.apply_symm_apply (x.obj i)

/-- The standard simplicial `n`-simplex is isomorphic to the nerve of the ordered type
`Fin (n + 1)`. -/
def finNerveIso (n : ℕ) :
    (Δ[n] : SSet) ≅ CategoryTheory.nerve (Fin (n + 1)) :=
  SSet.stdSimplex.isoNerve n ≪≫ nerveOrderIso ULift.orderIso

/-- The ordered simplicial set on vertices `Fin (n + 1)` maps canonically into the ambient
standard simplicial `n`-simplex. -/
def orderedSSetToStdSimplex {n : ℕ} (facets : Finset (Finset (Fin (n + 1)))) :
    orderedSSet facets ⟶ (Δ[n] : SSet) :=
  SSet.Subcomplex.ι (orderedSubcomplex facets) ≫ (finNerveIso n).inv

/-- The simplicial map to the ambient standard simplex is a monomorphism. -/
instance orderedSSetToStdSimplex_mono {n : ℕ}
    (facets : Finset (Finset (Fin (n + 1)))) : Mono (orderedSSetToStdSimplex facets) := by
  dsimp [orderedSSetToStdSimplex]
  infer_instance

/-- In every degree, the simplicial inclusion in the ambient standard simplex is injective. -/
theorem orderedSSetToStdSimplex_app_injective {n : ℕ}
    (facets : Finset (Finset (Fin (n + 1)))) (Δ : SimplexCategoryᵒᵖ) :
    Function.Injective ((orderedSSetToStdSimplex facets).app Δ) := by
  rw [← CategoryTheory.mono_iff_injective]
  infer_instance

/-- The geometric realization of an ordered complex, as a topological space. -/
abbrev orderedRealization {n : ℕ} (facets : Finset (Finset (Fin (n + 1)))) : TopCat :=
  SSet.toTop.obj (orderedSSet facets)

/-- Geometric realization of the simplicial inclusion into the ambient standard simplex. -/
def orderedRealizationToStdSimplex {n : ℕ} (facets : Finset (Finset (Fin (n + 1)))) :
    orderedRealization facets ⟶ SSet.toTop.obj (Δ[n] : SSet) :=
  SSet.toTop.map (orderedSSetToStdSimplex facets)

/-- The canonical continuous map from the realization of an ordered finite complex to the
ordinary topological standard simplex on the same vertices. -/
def orderedRealizationToTopologicalSimplex {n : ℕ}
    (facets : Finset (Finset (Fin (n + 1)))) :
    orderedRealization facets ⟶ TopCat.of (stdSimplex ℝ (Fin (n + 1))) :=
  orderedRealizationToStdSimplex facets ≫
    (TopCat.isoOfHomeo (SimplexCategory.toTopHomeo ⦋n⦌)).hom

end FiniteOrderedComplex

end Submission
