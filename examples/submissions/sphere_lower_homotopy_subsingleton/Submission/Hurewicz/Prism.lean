/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplexDict
import Mathlib.Topology.UnitInterval

/-!
# The prism decomposition of `|Δ^n| × I`

A homotopy `|Δ^n| × I → X` attached to every singular `n`-simplex of `X` produces a family of
maps `Sng X _⦋n⦌ → Sng X _⦋n+1⦌` — the operators of the associated simplicial homotopy — by
precomposing with the `n + 1` affine maps `|Δ^{n+1}| → |Δ^n| × I` that triangulate the prism.
The `i`-th of these sends the vertex `e_k` to `(v_k, 1)` for `k ≤ i` and to `(v_{k-1}, 0)` for
`k > i`; equivalently it is the pair `(|σ_i|, τ_i)` of the `i`-th degeneracy and the affine
"time" map that is `1` on the first `i + 1` vertices and `0` on the rest.

This file defines these maps and proves the six identities relating them to the face inclusions
that are needed to verify the axioms of `Submission.SimplicialCompression`.

## Main definitions and results

* `Submission.prismSpace`, `Submission.prismTime`, `Submission.prism` — the prism maps;
* `Submission.prism_faceMap_zero`, `Submission.prism_faceMap_last` — the two end faces;
* `Submission.prism_faceMap_castSucc`, `Submission.prism_faceMap_mid`,
  `Submission.prism_faceMap_succ` — the three compatibilities with the face maps.
-/

open scoped unitInterval

noncomputable section

namespace Submission

variable {n : ℕ}

/-! ### Values of `Fin.succAbove` and `Fin.predAbove` -/

theorem val_succAbove_eq (p : Fin (n + 1)) (k : Fin n) :
    ((p.succAbove k : Fin (n + 1)) : ℕ) = if (k : ℕ) < (p : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  rcases lt_or_ge k.castSucc p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, if_pos]
    · rfl
    · simpa [Fin.lt_def] using h
  · rw [Fin.succAbove_of_le_castSucc _ _ h, if_neg]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc] at h
      omega

theorem val_predAbove_eq (p : Fin n) (k : Fin (n + 1)) :
    ((p.predAbove k : Fin n) : ℕ) = if (p : ℕ) < (k : ℕ) then (k : ℕ) - 1 else (k : ℕ) := by
  rcases lt_or_ge p.castSucc k with h | h
  · rw [Fin.predAbove_of_castSucc_lt _ _ h, if_pos]
    · rfl
    · simpa [Fin.lt_def] using h
  · rw [Fin.predAbove_of_le_castSucc _ _ h, if_neg]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc] at h
      omega

/-! ### The face inclusion as a map of standard simplices -/

/-- The face inclusion of `Submission/Hurewicz/SimplexGlue.lean` is the map of standard simplices
induced by `Fin.succAbove`. -/
theorem faceMap_eq_map {j : ℕ} (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    faceMap i x = stdSimplex.map i.succAbove x := (stdSimplex_map_δ i x).symm

/-! ### The prism maps -/

/-- The "time" map `Fin (n + 2) → Fin 2` cutting the vertices of `|Δ^{n+1}|` into the first
`i + 1` (sent to time `1`) and the rest (sent to time `0`). -/
def timeFun (i : Fin (n + 1)) : Fin (n + 2) → Fin 2 := fun k => if (k : ℕ) ≤ (i : ℕ) then 1 else 0

/-- The space component of the `i`-th prism map: the `i`-th degeneracy. -/
def prismSpace (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) : stdSimplex ℝ (Fin (n + 1)) :=
  stdSimplex.map i.predAbove x

/-- The time component of the `i`-th prism map. -/
def prismTime (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) : I :=
  stdSimplexHomeomorphUnitInterval (stdSimplex.map (timeFun i) x)

theorem continuous_prismSpace (i : Fin (n + 1)) : Continuous (prismSpace i) :=
  stdSimplex.continuous_map _

theorem continuous_prismTime (i : Fin (n + 1)) : Continuous (prismTime i) :=
  stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _)

/-- **The `i`-th prism map** `|Δ^{n+1}| → |Δ^n| × I`. -/
def prism (i : Fin (n + 1)) : C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I) :=
  ⟨fun x => (prismSpace i x, prismTime i x),
    (continuous_prismSpace i).prodMk (continuous_prismTime i)⟩

@[simp]
theorem prism_apply (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    prism i x = (prismSpace i x, prismTime i x) := rfl

/-! ### Constant time maps -/

theorem stdSimplex_map_const {m : ℕ} (c : Fin 2) (y : stdSimplex ℝ (Fin (m + 1))) :
    stdSimplex.map (fun _ => c) y = stdSimplex.vertex c := by
  have h : (fun _ : Fin (m + 1) => c) = (fun _ : Fin 1 => c) ∘ (fun _ => 0) := rfl
  rw [h, ← stdSimplex.map_comp_apply,
    Subsingleton.elim (stdSimplex.map (fun _ : Fin (m + 1) => (0 : Fin 1)) y)
      (stdSimplex.vertex (0 : Fin 1)), stdSimplex.map_vertex]

theorem prismTime_of_const_zero {m : ℕ} {i : Fin (n + 1)} {f : Fin (m + 1) → Fin (n + 2)}
    (hf : timeFun i ∘ f = fun _ => 0) (y : stdSimplex ℝ (Fin (m + 1))) :
    prismTime i (stdSimplex.map f y) = 0 := by
  rw [prismTime, stdSimplex.map_comp_apply, hf, stdSimplex_map_const]
  exact stdSimplexHomeomorphUnitInterval_zero

theorem prismTime_of_const_one {m : ℕ} {i : Fin (n + 1)} {f : Fin (m + 1) → Fin (n + 2)}
    (hf : timeFun i ∘ f = fun _ => 1) (y : stdSimplex ℝ (Fin (m + 1))) :
    prismTime i (stdSimplex.map f y) = 1 := by
  rw [prismTime, stdSimplex.map_comp_apply, hf, stdSimplex_map_const]
  exact stdSimplexHomeomorphUnitInterval_one

theorem prismTime_of_eq {m : ℕ} {i : Fin (n + 1)} {i' : Fin (m + 1)} {f : Fin (m + 2) → Fin (n + 2)}
    (hf : timeFun i ∘ f = timeFun i') (y : stdSimplex ℝ (Fin (m + 2))) :
    prismTime i (stdSimplex.map f y) = prismTime i' y := by
  rw [prismTime, prismTime, stdSimplex.map_comp_apply, hf]

/-! ### The two end faces -/

theorem prismSpace_faceMap_zero (y : stdSimplex ℝ (Fin (n + 1))) :
    prismSpace (0 : Fin (n + 1)) (faceMap 0 y) = y := by
  rw [prismSpace, faceMap_eq_map, stdSimplex.map_comp_apply,
    show Fin.predAbove (0 : Fin (n + 1)) ∘ Fin.succAbove (0 : Fin (n + 2)) = id from ?_,
    stdSimplex.map_id_apply]
  funext k
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_predAbove_eq, val_succAbove_eq, Fin.val_zero, id_eq]
  split_ifs <;> omega

theorem prismTime_faceMap_zero (y : stdSimplex ℝ (Fin (n + 1))) :
    prismTime (0 : Fin (n + 1)) (faceMap 0 y) = 0 := by
  rw [faceMap_eq_map]
  refine prismTime_of_const_zero ?_ y
  funext k
  simp only [timeFun, Function.comp_apply, val_succAbove_eq, Fin.val_zero]
  split_ifs <;> omega

theorem prismSpace_faceMap_last (y : stdSimplex ℝ (Fin (n + 1))) :
    prismSpace (Fin.last n) (faceMap (Fin.last (n + 1)) y) = y := by
  rw [prismSpace, faceMap_eq_map, stdSimplex.map_comp_apply,
    show Fin.predAbove (Fin.last n) ∘ Fin.succAbove (Fin.last (n + 1)) = id from ?_,
    stdSimplex.map_id_apply]
  funext k
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_predAbove_eq, val_succAbove_eq, Fin.val_last, id_eq]
  have := k.isLt
  split_ifs <;> omega

theorem prismTime_faceMap_last (y : stdSimplex ℝ (Fin (n + 1))) :
    prismTime (Fin.last n) (faceMap (Fin.last (n + 1)) y) = 1 := by
  rw [faceMap_eq_map]
  refine prismTime_of_const_one ?_ y
  funext k
  simp only [timeFun, Function.comp_apply, val_succAbove_eq, Fin.val_last]
  have := k.isLt
  split_ifs <;> omega

/-! ### The three face compatibilities -/

section

variable {i : Fin (n + 2)} {j : Fin (n + 1)}

theorem prismSpace_faceMap_castSucc (h : i ≤ j.castSucc) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismSpace j.succ (faceMap i.castSucc y) = faceMap i (prismSpace j y) := by
  have h' : (i : ℕ) ≤ (j : ℕ) := by simpa [Fin.le_def] using h
  rw [prismSpace, prismSpace, faceMap_eq_map, faceMap_eq_map, stdSimplex.map_comp_apply,
    stdSimplex.map_comp_apply]
  congr 1
  funext k
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_predAbove_eq, val_succAbove_eq, Fin.val_succ,
    Fin.val_castSucc]
  split_ifs <;> omega

theorem prismTime_faceMap_castSucc (h : i ≤ j.castSucc) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismTime j.succ (faceMap i.castSucc y) = prismTime j y := by
  have h' : (i : ℕ) ≤ (j : ℕ) := by simpa [Fin.le_def] using h
  rw [faceMap_eq_map]
  refine prismTime_of_eq ?_ y
  funext k
  simp only [timeFun, Function.comp_apply, val_succAbove_eq, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

theorem prism_faceMap_castSucc (h : i ≤ j.castSucc) (y : stdSimplex ℝ (Fin (n + 2))) :
    prism j.succ (faceMap i.castSucc y) = (faceMap i (prism j y).1, (prism j y).2) := by
  rw [prism_apply, prism_apply, prismSpace_faceMap_castSucc h, prismTime_faceMap_castSucc h]

theorem prismSpace_faceMap_succ (h : j.castSucc < i) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismSpace j.castSucc (faceMap i.succ y) = faceMap i (prismSpace j y) := by
  have h' : (j : ℕ) < (i : ℕ) := by simpa [Fin.lt_def] using h
  rw [prismSpace, prismSpace, faceMap_eq_map, faceMap_eq_map, stdSimplex.map_comp_apply,
    stdSimplex.map_comp_apply]
  congr 1
  funext k
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_predAbove_eq, val_succAbove_eq, Fin.val_succ,
    Fin.val_castSucc]
  split_ifs <;> omega

theorem prismTime_faceMap_succ (h : j.castSucc < i) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismTime j.castSucc (faceMap i.succ y) = prismTime j y := by
  have h' : (j : ℕ) < (i : ℕ) := by simpa [Fin.lt_def] using h
  rw [faceMap_eq_map]
  refine prismTime_of_eq ?_ y
  funext k
  simp only [timeFun, Function.comp_apply, val_succAbove_eq, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

theorem prism_faceMap_succ (h : j.castSucc < i) (y : stdSimplex ℝ (Fin (n + 2))) :
    prism j.castSucc (faceMap i.succ y) = (faceMap i (prism j y).1, (prism j y).2) := by
  rw [prism_apply, prism_apply, prismSpace_faceMap_succ h, prismTime_faceMap_succ h]

end

theorem prismSpace_faceMap_mid (j : Fin (n + 1)) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismSpace j.succ (faceMap j.castSucc.succ y) =
      prismSpace j.castSucc (faceMap j.castSucc.succ y) := by
  rw [prismSpace, prismSpace, faceMap_eq_map, stdSimplex.map_comp_apply,
    stdSimplex.map_comp_apply]
  congr 1
  funext k
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_predAbove_eq, val_succAbove_eq, Fin.val_succ,
    Fin.val_castSucc]
  split_ifs <;> omega

theorem prismTime_faceMap_mid (j : Fin (n + 1)) (y : stdSimplex ℝ (Fin (n + 2))) :
    prismTime j.succ (faceMap j.castSucc.succ y) =
      prismTime j.castSucc (faceMap j.castSucc.succ y) := by
  rw [prismTime, prismTime, faceMap_eq_map, stdSimplex.map_comp_apply,
    stdSimplex.map_comp_apply]
  congr 2
  funext k
  simp only [timeFun, Function.comp_apply, val_succAbove_eq, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

theorem prism_faceMap_mid (j : Fin (n + 1)) (y : stdSimplex ℝ (Fin (n + 2))) :
    prism j.succ (faceMap j.castSucc.succ y) = prism j.castSucc (faceMap j.castSucc.succ y) := by
  rw [prism_apply, prism_apply, prismSpace_faceMap_mid, prismTime_faceMap_mid]

/-! ### The first cosimplicial identity -/

/-- The first cosimplicial identity for the face inclusions of standard simplices. -/
theorem faceMap_faceMap {j : ℕ} {i₀ j₀ : Fin (j + 2)} (h : i₀ ≤ j₀)
    (w : stdSimplex ℝ (Fin (j + 1))) :
    faceMap j₀.succ (faceMap i₀ w) = faceMap i₀.castSucc (faceMap j₀ w) := by
  have h' : (i₀ : ℕ) ≤ (j₀ : ℕ) := Fin.le_def.1 h
  rw [faceMap_eq_map, faceMap_eq_map, faceMap_eq_map, faceMap_eq_map,
    stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext m
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, val_succAbove_eq, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

end Submission
