/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexGlue
import Submission.Hurewicz.Vanishing

/-!
# Singular simplices as continuous maps out of the standard simplex

`Submission.SimplicialCompression` is phrased in terms of the simplicial set `Sng X` and its face
maps, whereas the geometric compression recursion works with continuous maps out of the standard
topological simplex.  This file is the dictionary between the two: `sngEquiv` identifies the
`j`-simplices of `Sng X` with `C(|Δ^j|, X)`, and `sngEquiv_δ` says that under this identification
the `i`-th face map of `Sng X` is precomposition with the face inclusion `faceMap i` of
`Submission/Hurewicz/SimplexGlue.lean`.

## Main results

* `Submission.stdSimplex_map_δ` — the topological realisation of `SimplexCategory.δ i` is
  `faceMap i`;
* `Submission.sngEquiv` — `Sng X _⦋j⦌ ≃ C(|Δ^j|, X)`;
* `Submission.sngEquiv_δ` — the face map is precomposition with `faceMap i`.
-/

open CategoryTheory Simplicial Opposite

noncomputable section

namespace Submission

variable {j : ℕ}

/-- The face inclusion of standard simplices, bundled as a continuous map. -/
def faceCM (i : Fin (j + 2)) :
    C(stdSimplex ℝ (Fin (j + 1)), stdSimplex ℝ (Fin (j + 2))) :=
  ⟨faceMap i, continuous_faceMap i⟩

@[simp]
theorem faceCM_apply (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    faceCM i x = faceMap i x := rfl

/-- The `i`-th face map of `SimplexCategory`, as a function, is `Fin.succAbove i`. -/
theorem δ_apply (i : Fin (j + 2)) (k : Fin (j + 1)) :
    (SimplexCategory.δ (n := j) i) k = i.succAbove k := rfl

/-- The topological realisation of the `i`-th face map of `SimplexCategory` is the face
inclusion `faceMap i`. -/
theorem stdSimplex_map_δ (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    stdSimplex.map (⇑(SimplexCategory.δ (n := j) i)) x = faceMap i x := by
  classical
  refine Subtype.ext (funext fun k => ?_)
  have hmap : (stdSimplex.map (⇑(SimplexCategory.δ (n := j) i)) x).1 =
      FunOnFinite.linearMap ℝ ℝ (⇑(SimplexCategory.δ (n := j) i)) x.1 := rfl
  rw [hmap, FunOnFinite.linearMap_apply_apply]
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · rw [faceMap_coe_same]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_filter, δ_apply] at hm
    exact absurd hm.2 (Fin.succAbove_ne i m)
  · rw [faceMap_coe_succAbove, Finset.sum_filter, Finset.sum_eq_single k]
    · rw [δ_apply, if_pos rfl]
    · intro m _ hm
      rw [δ_apply, if_neg]
      exact fun h => hm (Fin.succAbove_right_injective (p := i) h)
    · intro h
      exact absurd (Finset.mem_univ k) h

/-- Singular `j`-simplices of `X` are the continuous maps `|Δ^j| → X`. -/
def sngEquiv (X : TopCat.{0}) (j : ℕ) :
    Sng X _⦋j⦌ ≃ C(stdSimplex ℝ (Fin (j + 1)), X) :=
  TopCat.toSSetObjEquiv X (op ⦋j⦌)

/-- Under `sngEquiv`, the `i`-th face map of the singular simplicial set is precomposition with
the face inclusion of standard simplices. -/
theorem sngEquiv_δ (X : TopCat.{0}) (i : Fin (j + 2)) (σ : Sng X _⦋j + 1⦌) :
    sngEquiv X j ((Sng X).δ i σ) = (sngEquiv X (j + 1) σ).comp (faceCM i) := by
  ext x
  show (sngEquiv X (j + 1) σ) (stdSimplex.map (⇑(SimplexCategory.δ (n := j) i)) x) = _
  rw [stdSimplex_map_δ]
  rfl

end Submission
