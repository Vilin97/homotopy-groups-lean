/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Submission.Hurewicz.SimplexHorn

/-!
# The singular simplicial set is a Kan complex

The explicit simplex-horn retraction gives a direct continuous filler for every compatible
topological horn.  We first glue the prescribed face maps over the closed cover on which a fixed
barycentric coordinate realizes the minimum, and then precompose with the horn retraction.

Translating this filler through the singular-simplex dictionary proves the horn-filling condition
for `Sng X`.  This supplies the Kan-complex input needed for simplicial multiplication and the
remaining homotopy-addition argument.
-/

open CategoryTheory Simplicial Opposite
open scoped Topology

noncomputable section

namespace Submission

variable {d : ℕ} {X : Type} [TopologicalSpace X]

/-- The closed region of the ambient simplex on which coordinate `j`, away from the missing
face `i`, realizes the least such coordinate. -/
def simplexHornFillRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | simplexHornMin i z = z.1 (i.succAbove j)}

theorem isClosed_simplexHornFillRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    IsClosed (simplexHornFillRegion i j) := by
  apply isClosed_eq
  · exact continuous_simplexHornMin i
  · exact (continuous_apply (i.succAbove j)).comp continuous_subtype_val

/-- The minimum regions cover the entire ambient simplex. -/
theorem exists_mem_simplexHornFillRegion (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), z ∈ simplexHornFillRegion i j :=
  exists_simplexHornMin_eq i z

/-- On fill region `j`, the horn retraction lands on face `i.succAbove j`. -/
theorem simplexHornRetract_coord_eq_zero_of_mem_fillRegion
    (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : stdSimplex ℝ (Fin (d + 2))) (hz : z ∈ simplexHornFillRegion i j) :
    (simplexHornRetract i z).1 (i.succAbove j) = 0 := by
  rw [simplexHornRetract_apply_coe, simplexHornRetractCoords_succAbove]
  exact sub_eq_zero.mpr hz.symm

/-- Coordinates on the remaining face obtained after applying the horn retraction. -/
def simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C({z // z ∈ simplexHornFillRegion i j}, stdSimplex ℝ (Fin (d + 1))) where
  toFun z := dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    change Continuous fun z : {z // z ∈ simplexHornFillRegion i j} ↦
      (simplexHornRetract i z.1).1 ((i.succAbove j).succAbove k)
    exact ((continuous_apply ((i.succAbove j).succAbove k)).comp continuous_subtype_val).comp
      ((simplexHornRetract i).continuous.comp continuous_subtype_val)

/-- The local face coordinates reconstruct the horn retraction. -/
theorem faceMap_simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornFillRegion i j}) :
    faceMap (i.succAbove j) (simplexHornFillFaceMap i j z) = simplexHornRetract i z.1 :=
  faceMap_dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)

/-- A canonical index of a minimum region containing an ambient simplex point. -/
def simplexHornFillIdx (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 1) :=
  (exists_mem_simplexHornFillRegion i z).choose

theorem simplexHornFillIdx_spec (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    z ∈ simplexHornFillRegion i (simplexHornFillIdx i z) :=
  (exists_mem_simplexHornFillRegion i z).choose_spec

/-- The pointwise horn filler obtained by selecting a minimum-coordinate face. -/
def simplexHornFillFun (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (z : stdSimplex ℝ (Fin (d + 2))) : X :=
  g (simplexHornFillIdx i z)
    (simplexHornFillFaceMap i (simplexHornFillIdx i z)
      ⟨z, simplexHornFillIdx_spec i z⟩)

/-- Compatibility of maps prescribed on all faces other than `i`. -/
def SimplexHornFaceCompatible (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X)) : Prop :=
  ∀ (j k : Fin (d + 1)) (y z : stdSimplex ℝ (Fin (d + 1))),
    faceMap (i.succAbove j) y = faceMap (i.succAbove k) z → g j y = g k z

/-- The selected-index definition of the filler agrees with any minimum region containing the
point. -/
theorem simplexHornFillFun_eq (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (z : stdSimplex ℝ (Fin (d + 2)))
    (j : Fin (d + 1)) (hj : z ∈ simplexHornFillRegion i j) :
    simplexHornFillFun i g z = g j (simplexHornFillFaceMap i j ⟨z, hj⟩) := by
  apply hg
  rw [faceMap_simplexHornFillFaceMap, faceMap_simplexHornFillFaceMap]

/-- Compatible maps on the faces of a topological horn extend continuously over the full
simplex. -/
def simplexHornFiller (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) :
    C(stdSimplex ℝ (Fin (d + 2)), X) where
  toFun := simplexHornFillFun i g
  continuous_toFun := by
    let S : Fin (d + 1) → Set (stdSimplex ℝ (Fin (d + 2))) :=
      fun j ↦ simplexHornFillRegion i j
    refine (locallyFinite_of_finite S).continuous ?_ (fun j ↦ ?_) (fun j ↦ ?_)
    · refine Set.eq_univ_of_forall fun z ↦ ?_
      obtain ⟨j, hj⟩ := exists_mem_simplexHornFillRegion i z
      exact Set.mem_iUnion.2 ⟨j, hj⟩
    · exact isClosed_simplexHornFillRegion i j
    · rw [continuousOn_iff_continuous_restrict]
      have heq : (S j).restrict (simplexHornFillFun i g) =
          fun z : S j ↦ g j (simplexHornFillFaceMap i j z) := by
        funext z
        exact simplexHornFillFun_eq i g hg z.1 j z.2
      rw [heq]
      exact (g j).continuous.comp (simplexHornFillFaceMap i j).continuous

/-- On every prescribed face, the topological horn filler recovers the given map. -/
theorem simplexHornFiller_face (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornFiller i g hg (faceMap (i.succAbove j) y) = g j y := by
  have hmem : faceMap (i.succAbove j) y ∈ simplexHorn i :=
    ⟨j, faceMap_coe_same (i.succAbove j) y⟩
  have hregion : faceMap (i.succAbove j) y ∈ simplexHornFillRegion i j := by
    change simplexHornMin i (faceMap (i.succAbove j) y) =
      (faceMap (i.succAbove j) y).1 (i.succAbove j)
    rw [simplexHornMin_eq_zero_of_mem i hmem, faceMap_coe_same]
  rw [show simplexHornFiller i g hg (faceMap (i.succAbove j) y) =
      simplexHornFillFun i g (faceMap (i.succAbove j) y) from rfl,
    simplexHornFillFun_eq i g hg _ j hregion]
  apply congrArg (g j)
  apply faceMap_injective (i.succAbove j)
  rw [faceMap_simplexHornFillFaceMap,
    simplexHornRetract_eq_self_of_mem i hmem]

/-! ### Translation to singular simplicial sets -/

/-- The topological map carried by one prescribed face of a simplicial horn in `Sng X`. -/
def singularHornFaceMap (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (j : Fin (d + 1)) : C(stdSimplex ℝ (Fin (d + 1)), X) :=
  sngEquiv (TopCat.of X) d
    (SSet.yonedaEquiv (f (i.succAbove j) (Fin.succAbove_ne i j)))

theorem yonedaEquiv_comp_δ {q : ℕ} (j : Fin (q + 2))
    (f : Δ[q + 1] ⟶ Sng (TopCat.of X)) :
    (Sng (TopCat.of X)).δ j (SSet.yonedaEquiv f) =
      SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ f) := by
  change (Sng (TopCat.of X)).map (SimplexCategory.δ j).op (SSet.yonedaEquiv f) =
    SSet.yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.δ j) ≫ f)
  exact SSet.yonedaEquiv_naturality (SimplexCategory.δ j) f

/-- Simplicial horn compatibility implies the pointwise compatibility required by the
topological closed-cover filler. -/
theorem singularHornFaceMap_compatible (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (hf : SSet.horn.IsCompatible f) :
    SimplexHornFaceCompatible i (singularHornFaceMap i f) := by
  intro a b y z h
  by_cases hab : a = b
  · subst b
    have hyz := faceMap_injective (i.succAbove a) h
    subst z
    rfl
  cases d with
  | zero => exact (hab (Fin.eq_zero a |>.trans (Fin.eq_zero b).symm)).elim
  | succ m =>
      let ja : Fin (m + 3) := i.succAbove a
      let jb : Fin (m + 3) := i.succAbove b
      have hjab : ja ≠ jb := fun e ↦ hab (Fin.succAbove_right_injective e)
      rcases lt_trichotomy ja jb with hjlt | hjeq | hjgt
      · obtain ⟨w, hy, hz⟩ := exists_faceMap_factor hjlt h
        rw [hy, hz]
        change sngEquiv (TopCat.of X) (m + 1)
              (SSet.yonedaEquiv (f ja (Fin.succAbove_ne i a)))
              (faceMap (jb.pred (Fin.ne_zero_of_lt hjlt)) w) =
            sngEquiv (TopCat.of X) (m + 1)
              (SSet.yonedaEquiv (f jb (Fin.succAbove_ne i b)))
              (faceMap (ja.castPred (Fin.ne_last_of_lt hjlt)) w)
        rw [← apply_δ, ← apply_δ]
        have hs := congrArg SSet.yonedaEquiv
          (hf.δ_pred_comp ja jb (Fin.succAbove_ne i a) (Fin.succAbove_ne i b) hjlt)
        have hs' := (yonedaEquiv_comp_δ (X := X)
          (jb.pred (Fin.ne_zero_of_lt hjlt)) (f ja (Fin.succAbove_ne i a))).trans
            (hs.trans (yonedaEquiv_comp_δ (X := X)
              (ja.castPred (Fin.ne_last_of_lt hjlt))
              (f jb (Fin.succAbove_ne i b))).symm)
        exact congrArg (fun q ↦ sngEquiv (TopCat.of X) m q w) hs'
      · exact (hjab hjeq).elim
      · obtain ⟨w, hz, hy⟩ := exists_faceMap_factor hjgt h.symm
        rw [hy, hz]
        change sngEquiv (TopCat.of X) (m + 1)
              (SSet.yonedaEquiv (f ja (Fin.succAbove_ne i a)))
              (faceMap (jb.castPred (Fin.ne_last_of_lt hjgt)) w) =
            sngEquiv (TopCat.of X) (m + 1)
              (SSet.yonedaEquiv (f jb (Fin.succAbove_ne i b)))
              (faceMap (ja.pred (Fin.ne_zero_of_lt hjgt)) w)
        rw [← apply_δ, ← apply_δ]
        have hs := congrArg SSet.yonedaEquiv
          (hf.δ_pred_comp jb ja (Fin.succAbove_ne i b) (Fin.succAbove_ne i a) hjgt)
        have hs' := (yonedaEquiv_comp_δ (X := X)
          (ja.pred (Fin.ne_zero_of_lt hjgt)) (f jb (Fin.succAbove_ne i b))).trans
            (hs.trans (yonedaEquiv_comp_δ (X := X)
              (jb.castPred (Fin.ne_last_of_lt hjgt))
              (f ja (Fin.succAbove_ne i a))).symm)
        exact (congrArg (fun q ↦ sngEquiv (TopCat.of X) m q w) hs').symm

/-- The singular simplex obtained from the explicit topological horn filler. -/
def singularHornFillerSimplex (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (hf : SSet.horn.IsCompatible f) : Sng (TopCat.of X) _⦋d + 1⦌ :=
  (sngEquiv (TopCat.of X) (d + 1)).symm
    (simplexHornFiller i (singularHornFaceMap i f)
      (singularHornFaceMap_compatible i f hf))

/-- Every prescribed face of the singular horn filler is the requested singular simplex. -/
theorem singularHornFillerSimplex_face (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (hf : SSet.horn.IsCompatible f) (j : Fin (d + 1)) :
    (Sng (TopCat.of X)).δ (i.succAbove j) (singularHornFillerSimplex i f hf) =
      SSet.yonedaEquiv (f (i.succAbove j) (Fin.succAbove_ne i j)) := by
  apply (sngEquiv (TopCat.of X) d).injective
  rw [sngEquiv_δ]
  change (simplexHornFiller i (singularHornFaceMap i f)
      (singularHornFaceMap_compatible i f hf)).comp (faceCM (i.succAbove j)) =
    singularHornFaceMap i f j
  apply ContinuousMap.ext
  exact simplexHornFiller_face i (singularHornFaceMap i f)
    (singularHornFaceMap_compatible i f hf) j

/-- The simplicial morphism represented by the explicit singular horn filler. -/
def singularHornFillerMorphism (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (hf : SSet.horn.IsCompatible f) : Δ[d + 1] ⟶ Sng (TopCat.of X) :=
  SSet.yonedaEquiv.symm (singularHornFillerSimplex i f hf)

/-- The filler morphism restricts to the original morphism on every horn face. -/
theorem δ_singularHornFillerMorphism (i : Fin (d + 2))
    (f : ∀ (k : Fin (d + 2)) (_ : k ≠ i), Δ[d] ⟶ Sng (TopCat.of X))
    (hf : SSet.horn.IsCompatible f) (j : Fin (d + 2)) (hj : j ≠ i) :
    SSet.stdSimplex.δ j ≫ singularHornFillerMorphism i f hf = f j hj := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
  subst j
  apply SSet.yonedaEquiv.injective
  calc
    SSet.yonedaEquiv
          (SSet.stdSimplex.δ (i.succAbove k) ≫ singularHornFillerMorphism i f hf) =
        (Sng (TopCat.of X)).δ (i.succAbove k)
          (SSet.yonedaEquiv (singularHornFillerMorphism i f hf)) :=
      (yonedaEquiv_comp_δ (X := X) (i.succAbove k)
        (singularHornFillerMorphism i f hf)).symm
    _ = SSet.yonedaEquiv
          (f (i.succAbove k) (Fin.succAbove_ne i k)) := by
      have hφ : SSet.yonedaEquiv (singularHornFillerMorphism i f hf) =
          singularHornFillerSimplex i f hf := by
        change SSet.yonedaEquiv (SSet.yonedaEquiv.symm _) = _
        exact SSet.yonedaEquiv.apply_symm_apply _
      rw [hφ, singularHornFillerSimplex_face]

/-- The singular simplicial set of every topological space is a Kan complex. -/
noncomputable instance singularKanComplex : SSet.KanComplex (Sng (TopCat.of X)) :=
  SSet.KanComplex.iff.mpr fun {n} {i} f hf ↦
    ⟨singularHornFillerMorphism (d := n) i f hf,
      δ_singularHornFillerMorphism (d := n) i f hf⟩

end Submission
