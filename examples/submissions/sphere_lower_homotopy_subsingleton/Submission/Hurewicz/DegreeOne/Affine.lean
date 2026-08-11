/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.DualBridge
import Submission.Hurewicz.SimplexDict
import Mathlib.Topology.Homotopy.Path

/-!
# Affine singular simplices and the dictionary between paths and edges

The degree-one Hurewicz theorem is proved by writing down, by hand, a handful of singular
`2`-simplices whose boundaries realise the group-theoretic identities of `π₁` inside the group of
singular `1`-chains.  All of these simplices are of the shape "an affine map from the standard
simplex into the unit interval (or into the square), followed by a path (or a path homotopy)".
This file sets up that construction and computes the faces.

## Main definitions

* `Submission.affI` — the affine simplex `|Δⁿ| → I` with prescribed vertex values;
* `Submission.affSq` — the same with values in the square `I × I`;
* `Submission.sng` — a singular simplex from a continuous map out of `|Δⁿ|`;
* `Submission.constSimplex` — the constant singular simplex at a point;
* `Submission.pathSimplex` — the singular `1`-simplex determined by a path.

## Main results

* `Submission.affI_faceMap`, `Submission.affSq_comp_faceCM` — the faces of an affine simplex are
  the affine simplices on the corresponding subsets of vertices;
* `Submission.face_sng` — the faces of `sng f` are `sng` of the restrictions of `f`;
* `Submission.face_pathSimplex_zero`, `Submission.face_pathSimplex_one` — the endpoints of a path
  are the two faces of the corresponding edge.
-/

open CategoryTheory Simplicial Opposite
open scoped unitInterval

noncomputable section

namespace Submission

variable {n : ℕ}

/-! ### Affine simplices in the unit interval -/

theorem affI_mem (v : Fin (n + 1) → I) (x : stdSimplex ℝ (Fin (n + 1))) :
    ∑ j, x.1 j * (v j : ℝ) ∈ I := by
  refine Set.mem_Icc.2 ⟨Finset.sum_nonneg fun j _ => mul_nonneg (x.2.1 j) (v j).2.1, ?_⟩
  calc ∑ j, x.1 j * (v j : ℝ) ≤ ∑ j, x.1 j * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (v j).2.2 (x.2.1 j)
    _ = 1 := by simpa using x.2.2

/-- The affine singular `n`-simplex in the unit interval taking the prescribed values `v` at the
vertices of `|Δⁿ|`. -/
def affI (v : Fin (n + 1) → I) : C(stdSimplex ℝ (Fin (n + 1)), I) where
  toFun x := ⟨∑ j, x.1 j * (v j : ℝ), affI_mem v x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_finsetSum _ fun j _ => ?_) _
    exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

@[simp]
theorem affI_coe (v : Fin (n + 1) → I) (x : stdSimplex ℝ (Fin (n + 1))) :
    (affI v x : ℝ) = ∑ j, x.1 j * (v j : ℝ) := rfl

/-- The `i`-th face of an affine simplex is the affine simplex on the remaining vertices. -/
theorem affI_faceMap (v : Fin (n + 2) → I) (i : Fin (n + 2)) (x : stdSimplex ℝ (Fin (n + 1))) :
    affI v (faceMap i x) = affI (v ∘ i.succAbove) x := by
  refine Subtype.ext ?_
  rw [affI_coe, affI_coe, Fin.sum_univ_succAbove (fun k => (faceMap i x).1 k * (v k : ℝ)) i]
  simp

theorem affI_comp_faceCM (v : Fin (n + 2) → I) (i : Fin (n + 2)) :
    (affI v).comp (faceCM i) = affI (v ∘ i.succAbove) :=
  ContinuousMap.ext fun x => affI_faceMap v i x

/-- An affine `0`-simplex is constant at its unique vertex value. -/
@[simp]
theorem affI_dim_zero (v : Fin 1 → I) (x : stdSimplex ℝ (Fin 1)) : affI v x = v 0 := by
  refine Subtype.ext ?_
  rw [affI_coe, Fin.sum_univ_one, show x.1 0 = 1 by simpa using x.2.2, one_mul]

/-- The standard parametrisation of `|Δ¹|` by the unit interval. -/
def edgeParam : C(stdSimplex ℝ (Fin 2), I) := affI ![0, 1]

@[simp]
theorem edgeParam_coe (x : stdSimplex ℝ (Fin 2)) : (edgeParam x : ℝ) = x.1 1 := by
  simp [edgeParam, Fin.sum_univ_two]

theorem sum_two (x : stdSimplex ℝ (Fin 2)) : x.1 0 + x.1 1 = 1 := by
  simpa [Fin.sum_univ_two] using x.2.2

/-- An affine `1`-simplex, in terms of the standard parametrisation of `|Δ¹|`. -/
theorem affI_two_coe (a b : I) (x : stdSimplex ℝ (Fin 2)) :
    (affI ![a, b] x : ℝ) = (1 - (edgeParam x : ℝ)) * a + (edgeParam x : ℝ) * b := by
  rw [affI_coe, Fin.sum_univ_two, edgeParam_coe]
  have h : x.1 0 = 1 - x.1 1 := by linarith [sum_two x]
  rw [h]
  simp

/-! ### Affine simplices in the square -/

/-- The affine singular `n`-simplex in the square `I × I` taking the prescribed values `v` at the
vertices of `|Δⁿ|`. -/
def affSq (v : Fin (n + 1) → I × I) : C(stdSimplex ℝ (Fin (n + 1)), I × I) where
  toFun x := (affI (fun j => (v j).1) x, affI (fun j => (v j).2) x)
  continuous_toFun := (map_continuous _).prodMk (map_continuous _)

@[simp]
theorem affSq_apply (v : Fin (n + 1) → I × I) (x : stdSimplex ℝ (Fin (n + 1))) :
    affSq v x = (affI (fun j => (v j).1) x, affI (fun j => (v j).2) x) := rfl

theorem affSq_comp_faceCM (v : Fin (n + 2) → I × I) (i : Fin (n + 2)) :
    (affSq v).comp (faceCM i) = affSq (v ∘ i.succAbove) := by
  refine ContinuousMap.ext fun x => ?_
  simp only [ContinuousMap.comp_apply, faceCM_apply, affSq_apply, affI_faceMap]
  rfl

/-! ### Vertex tuples -/

variable {α : Type*}

theorem succAbove_two_zero (a b c : α) : ![a, b, c] ∘ Fin.succAbove 0 = ![b, c] := by
  funext k; fin_cases k <;> rfl

theorem succAbove_two_one (a b c : α) : ![a, b, c] ∘ Fin.succAbove 1 = ![a, c] := by
  funext k; fin_cases k <;> rfl

theorem succAbove_two_two (a b c : α) : ![a, b, c] ∘ Fin.succAbove 2 = ![a, b] := by
  funext k; fin_cases k <;> rfl

theorem succAbove_one_zero (a b : α) : ![a, b] ∘ Fin.succAbove 0 = ![b] := by
  funext k; fin_cases k; rfl

theorem succAbove_one_one (a b : α) : ![a, b] ∘ Fin.succAbove 1 = ![a] := by
  funext k; fin_cases k; rfl

/-! ### Singular simplices from continuous maps -/

variable {X : TopCat.{0}}

/-- The singular `n`-simplex of `X` given by a continuous map out of the standard simplex. -/
def sng {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), X)) : Sng X _⦋n⦌ := (sngEquiv X n).symm f

@[simp]
theorem sngEquiv_sng {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    sngEquiv X n (sng f) = f := (sngEquiv X n).apply_symm_apply f

@[simp]
theorem sng_sngEquiv {n : ℕ} (s : Sng X _⦋n⦌) : sng (sngEquiv X n s) = s :=
  (sngEquiv X n).symm_apply_apply s

theorem sng_injective {n : ℕ} {f g : C(stdSimplex ℝ (Fin (n + 1)), X)} (h : sng f = sng g) :
    f = g := by rw [← sngEquiv_sng (X := X) f, ← sngEquiv_sng (X := X) g, h]

/-- The faces of `sng f` are given by restricting `f` along the face inclusions. -/
theorem face_sng {n : ℕ} (i : Fin (n + 2)) (f : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    SSet.face (Sng X) i (sng f) = sng (f.comp (faceCM i)) := by
  refine (sngEquiv X n).injective ?_
  rw [show SSet.face (Sng X) i (sng f) = (Sng X).δ i (sng f) from rfl, sngEquiv_δ, sngEquiv_sng,
    sngEquiv_sng]

/-- The singular `n`-simplex constant at a point. -/
def constSimplex (n : ℕ) (x : X) : Sng X _⦋n⦌ := sng (ContinuousMap.const _ x)

@[simp]
theorem face_constSimplex (n : ℕ) (i : Fin (n + 2)) (x : X) :
    SSet.face (Sng X) i (constSimplex (n + 1) x) = constSimplex n x := by
  rw [constSimplex, face_sng]; rfl

/-! ### Edges from paths -/

/-- The singular `1`-simplex determined by a path. -/
def pathSimplex {x y : X} (p : Path x y) : Sng X _⦋1⦌ :=
  sng (p.toContinuousMap.comp edgeParam)

theorem pathSimplex_congr {x y : X} {p q : Path x y} (h : ∀ t, p t = q t) :
    pathSimplex p = pathSimplex q := by
  rw [pathSimplex, pathSimplex]
  exact congrArg sng (ContinuousMap.ext fun z => h _)

@[simp]
theorem pathSimplex_refl (x : X) : pathSimplex (Path.refl x) = constSimplex 1 x :=
  congrArg sng (ContinuousMap.ext fun _ => rfl)

/-- The `0`-th face of the edge of a path is its endpoint. -/
@[simp]
theorem face_pathSimplex_zero {x y : X} (p : Path x y) :
    SSet.face (Sng X) 0 (pathSimplex p) = constSimplex 0 y := by
  rw [pathSimplex, face_sng]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show p (edgeParam (faceMap 0 z)) = y
  rw [edgeParam, affI_faceMap, succAbove_one_zero, affI_dim_zero]
  exact p.target

/-- The first face of the edge of a path is its source. -/
@[simp]
theorem face_pathSimplex_one {x y : X} (p : Path x y) :
    SSet.face (Sng X) 1 (pathSimplex p) = constSimplex 0 x := by
  rw [pathSimplex, face_sng]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show p (edgeParam (faceMap 1 z)) = x
  rw [edgeParam, affI_faceMap, succAbove_one_one, affI_dim_zero]
  exact p.source

/-! ### The inverse parametrisation, and the path underlying a singular `1`-simplex -/

theorem edgeInv_mem (t : I) : ![1 - (t : ℝ), (t : ℝ)] ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k
    · simpa using t.2.2
    · simpa using t.2.1
  · simp [Fin.sum_univ_two]

/-- The inverse of the standard parametrisation `edgeParam` of `|Δ¹|`. -/
def edgeInv : C(I, stdSimplex ℝ (Fin 2)) where
  toFun t := ⟨![1 - (t : ℝ), (t : ℝ)], edgeInv_mem t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun k => ?_) _
    fin_cases k
    · exact continuous_const.sub continuous_subtype_val
    · exact continuous_subtype_val

@[simp]
theorem edgeInv_coe (t : I) (k : Fin 2) :
    (edgeInv t).1 k = ![1 - (t : ℝ), (t : ℝ)] k := rfl

@[simp]
theorem edgeParam_edgeInv (t : I) : edgeParam (edgeInv t) = t := by
  refine Subtype.ext ?_
  rw [edgeParam_coe]
  simp

/-- A continuous map out of the unit interval, viewed as a path between its endpoints. -/
def toPath {Z : Type*} [TopologicalSpace Z] (f : C(I, Z)) : Path (f 0) (f 1) where
  toContinuousMap := f
  source' := rfl
  target' := rfl

@[simp]
theorem toPath_apply {Z : Type*} [TopologicalSpace Z] (f : C(I, Z)) (t : I) : toPath f t = f t :=
  rfl

/-- The continuous map `I → X` underlying a singular `1`-simplex. -/
def arc (s : Sng X _⦋1⦌) : C(I, X) := (sngEquiv X 1 s).comp edgeInv

@[simp]
theorem arc_apply (s : Sng X _⦋1⦌) (t : I) : arc s t = sngEquiv X 1 s (edgeInv t) := rfl

/-- The path underlying a singular `1`-simplex. -/
def spath (s : Sng X _⦋1⦌) : Path (arc s 0) (arc s 1) := toPath (arc s)

@[simp]
theorem spath_apply (s : Sng X _⦋1⦌) (t : I) : spath s t = arc s t := rfl

theorem arc_pathSimplex {x y : X} (p : Path x y) (t : I) : arc (pathSimplex p) t = p t := by
  rw [arc_apply, pathSimplex, sngEquiv_sng]
  exact congrArg p (edgeParam_edgeInv t)

@[simp]
theorem edgeInv_edgeParam (z : stdSimplex ℝ (Fin 2)) : edgeInv (edgeParam z) = z := by
  refine Subtype.ext (funext fun k => ?_)
  rw [edgeInv_coe, edgeParam_coe]
  fin_cases k
  · simpa using (by linarith [sum_two z] : 1 - z.1 1 = z.1 0)
  · simp

theorem pathSimplex_spath (s : Sng X _⦋1⦌) : pathSimplex (spath s) = s := by
  conv_rhs => rw [← sng_sngEquiv s]
  refine congrArg sng (ContinuousMap.ext fun z => ?_)
  show sngEquiv X 1 s (edgeInv (edgeParam z)) = sngEquiv X 1 s z
  rw [edgeInv_edgeParam]

/-- The point underlying a singular `0`-simplex. -/
def pt0 (v : Sng X _⦋0⦌) : X := sngEquiv X 0 v default

theorem constSimplex_pt0 (v : Sng X _⦋0⦌) : constSimplex 0 (pt0 v) = v := by
  refine (sngEquiv X 0).injective ?_
  rw [constSimplex, sngEquiv_sng]
  exact ContinuousMap.ext fun z => congrArg (sngEquiv X 0 v) (Subsingleton.elim default z)

@[simp]
theorem pt0_constSimplex (x : X) : pt0 (constSimplex 0 x) = x := by
  rw [pt0, constSimplex, sngEquiv_sng]; rfl

end Submission
