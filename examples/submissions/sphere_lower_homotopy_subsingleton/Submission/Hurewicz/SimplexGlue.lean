/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexBall
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.CompactOpen

/-!
# Gluing continuous maps over the boundary of a standard simplex

The compression recursion of `Submission.exists_simplicialCompression` builds, for a singular
`(j+1)`-simplex `σ`, a homotopy on `|∂Δ^{j+1}| × I` out of the homotopies already constructed for
the `j+2` faces of `σ`.  This file provides that gluing step.

The boundary `|∂Δ^{j+1}| = {x | ∃ i, x i = 0}` is covered by the `j + 2` closed faces
`{x | x i = 0}`, each of which is the image of the `i`-th face inclusion `faceMap i`.  Given
continuous maps `g i` on `|Δ^j|` which agree whenever their arguments have the same image, the
glued map is continuous by `LocallyFinite.continuous` applied to this finite closed cover.

## Main definitions and results

* `Submission.faceMap i` — the `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero;
* `Submission.dropMap i` — its inverse on the `i`-th face;
* `Submission.range_faceMap` — the image of `faceMap i` is `{x | x i = 0}`;
* `Submission.bdry` — the boundary of the standard simplex;
* `Submission.glueFaces` — the glued continuous map on the boundary, with `glueFaces_faceMap`;
* `Submission.glueFacesHomotopy` — the version for homotopies, i.e. maps out of `bdry × I`.
-/

open Set Metric

noncomputable section

namespace Submission

variable {j : ℕ} {Z : Type} [TopologicalSpace Z]

/-! ### Faces of the standard simplex -/

/-- The boundary of the standard `j`-simplex: the points with a vanishing coordinate. -/
def bdry (j : ℕ) : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

theorem mem_bdry {x : stdSimplex ℝ (Fin (j + 1))} : x ∈ bdry j ↔ ∃ i, x.1 i = 0 := Iff.rfl

/-- The `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero in slot `i`. -/
def faceMap (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, by
    refine ⟨(Fin.forall_iff_succAbove i).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove]; exact x.2.1 k
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
      simp only [Fin.insertNth_apply_succAbove]
      rw [zero_add, x.2.2]⟩

@[simp]
theorem faceMap_coe_same (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    (faceMap i x).1 i = 0 := by
  simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by
  simp [faceMap]

theorem faceMap_mem_bdry (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    faceMap i x ∈ bdry (j + 1) := ⟨i, faceMap_coe_same i x⟩

theorem continuous_faceMap (i : Fin (j + 2)) : Continuous (faceMap (j := j) i) := by
  refine Continuous.subtype_mk (continuous_pi fun k => ?_) _
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · simp only [Fin.insertNth_apply_same]
    exact continuous_const
  · simp only [Fin.insertNth_apply_succAbove]
    exact (continuous_apply k).comp continuous_subtype_val

theorem faceMap_injective (i : Fin (j + 2)) : Function.Injective (faceMap (j := j) i) := by
  intro x y h
  refine Subtype.ext (funext fun k => ?_)
  have := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 (i.succAbove k)) h
  simpa using this

/-- The subspace of the `(j+1)`-simplex cut out by the vanishing of the `i`-th coordinate. -/
def faceSet (i : Fin (j + 2)) : Set (stdSimplex ℝ (Fin (j + 2))) := {x | x.1 i = 0}

theorem isClosed_faceSet (i : Fin (j + 2)) : IsClosed (faceSet (j := j) i) :=
  isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const

/-- The inverse of the `i`-th face inclusion, deleting the `i`-th coordinate. -/
def dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    stdSimplex ℝ (Fin (j + 1)) :=
  ⟨Fin.removeNth i x.1, fun k => x.2.1 _, by
    have h := x.2.2
    rw [Fin.sum_univ_succAbove _ i, hx, zero_add] at h
    exact h⟩

theorem faceMap_dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    faceMap i (dropMap i hx) = x := by
  refine Subtype.ext (funext fun k => ?_)
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · rw [faceMap_coe_same, hx]
  · rw [faceMap_coe_succAbove]
    rfl

theorem dropMap_faceMap (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) :
    dropMap i (faceMap_coe_same i y) = y :=
  faceMap_injective i (faceMap_dropMap i (faceMap_coe_same i y))

theorem range_faceMap (i : Fin (j + 2)) : Set.range (faceMap (j := j) i) = faceSet i := by
  refine Subset.antisymm ?_ fun x hx => ⟨dropMap i hx, faceMap_dropMap i hx⟩
  rintro _ ⟨y, rfl⟩
  exact faceMap_coe_same i y

/-! ### The gluing -/

variable (g : Fin (j + 2) → C(stdSimplex ℝ (Fin (j + 1)), Z))
  (hg : ∀ (i k : Fin (j + 2)) (y z : stdSimplex ℝ (Fin (j + 1))),
    faceMap i y = faceMap k z → g i y = g k z)

/-- An index witnessing that a boundary point lies on a face. -/
def bdryIdx (b : bdry (j + 1)) : Fin (j + 2) := (mem_bdry.1 b.2).choose

theorem bdryIdx_spec (b : bdry (j + 1)) : (b : stdSimplex ℝ (Fin (j + 2))).1 (bdryIdx b) = 0 :=
  (mem_bdry.1 b.2).choose_spec

include hg in
theorem glueFaces_aux (b : bdry (j + 1)) (i : Fin (j + 2))
    (hi : (b : stdSimplex ℝ (Fin (j + 2))).1 i = 0) :
    g (bdryIdx b) (dropMap _ (bdryIdx_spec b)) = g i (dropMap i hi) :=
  hg _ _ _ _ ((faceMap_dropMap _ (bdryIdx_spec b)).trans (faceMap_dropMap i hi).symm)

/-- The map obtained by gluing the `g i` over the faces of the boundary. -/
def glueFacesFun (b : bdry (j + 1)) : Z := g (bdryIdx b) (dropMap _ (bdryIdx_spec b))

include hg in
theorem continuous_glueFacesFun : Continuous (glueFacesFun g) := by
  set S : Fin (j + 2) → Set (bdry (j + 1)) :=
    fun i => {b | (b : stdSimplex ℝ (Fin (j + 2))).1 i = 0} with hS
  have hcont : Continuous fun b : bdry (j + 1) => (b : stdSimplex ℝ (Fin (j + 2))).1 :=
    continuous_subtype_val.comp continuous_subtype_val
  refine (locallyFinite_of_finite S).continuous ?_ (fun i => ?_) (fun i => ?_)
  · refine eq_univ_of_forall fun b => ?_
    obtain ⟨i, hi⟩ := mem_bdry.1 b.2
    exact mem_iUnion.2 ⟨i, hi⟩
  · exact isClosed_eq ((continuous_apply i).comp hcont) continuous_const
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (S i).restrict (glueFacesFun g) =
        fun b : S i => g i (dropMap i b.2) := by
      funext b
      exact glueFaces_aux g hg b.1 i b.2
    rw [heq]
    refine (map_continuous (g i)).comp
      (Continuous.subtype_mk (continuous_pi fun k => ?_) _)
    exact (continuous_apply _).comp (hcont.comp continuous_subtype_val)

include hg in
/-- **The glued continuous map on the boundary of the standard simplex.** -/
def glueFaces : C(bdry (j + 1), Z) := ⟨glueFacesFun g, continuous_glueFacesFun g hg⟩

include hg in
@[simp]
theorem glueFaces_faceMap (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) :
    glueFaces g hg ⟨faceMap i y, faceMap_mem_bdry i y⟩ = g i y := by
  show glueFacesFun g ⟨faceMap i y, faceMap_mem_bdry i y⟩ = g i y
  rw [glueFacesFun,
    glueFaces_aux g hg ⟨faceMap i y, faceMap_mem_bdry i y⟩ i (faceMap_coe_same i y),
    dropMap_faceMap]

/-! ### The homotopy version -/

variable (G : Fin (j + 2) → C(stdSimplex ℝ (Fin (j + 1)) × unitInterval, Z))
  (hG : ∀ (i k : Fin (j + 2)) (y z : stdSimplex ℝ (Fin (j + 1))) (t : unitInterval),
    faceMap i y = faceMap k z → G i (y, t) = G k (z, t))

include hG in
theorem curry_compat (i k : Fin (j + 2)) (y z : stdSimplex ℝ (Fin (j + 1)))
    (h : faceMap i y = faceMap k z) : (G i).curry y = (G k).curry z :=
  ContinuousMap.ext fun t => hG i k y z t h

include hG in
/-- **The glued homotopy on the boundary of the standard simplex.** -/
def glueFacesHomotopy : C(bdry (j + 1) × unitInterval, Z) :=
  ContinuousMap.uncurry (glueFaces (fun i => (G i).curry) (curry_compat G hG))

include hG in
@[simp]
theorem glueFacesHomotopy_faceMap (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1)))
    (t : unitInterval) :
    glueFacesHomotopy G hG (⟨faceMap i y, faceMap_mem_bdry i y⟩, t) = G i (y, t) := by
  show (glueFaces (fun i => (G i).curry) (curry_compat G hG)
    ⟨faceMap i y, faceMap_mem_bdry i y⟩) t = G i (y, t)
  rw [glueFaces_faceMap]
  rfl

end Submission
