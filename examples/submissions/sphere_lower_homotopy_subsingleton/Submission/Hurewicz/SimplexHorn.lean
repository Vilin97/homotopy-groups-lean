/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.StickBoundary

/-!
# Retraction of a simplex onto a horn

For a chosen face `i` of a simplex, subtract the least barycentric coordinate away from `i`
from every coordinate away from `i`, and transfer the removed mass to coordinate `i`.  The
result lies in the horn obtained by deleting face `i`: at least one of the other coordinates is
zero.  This gives an explicit continuous retraction of the simplex onto that horn.

The straight-line homotopy to this retraction fixes the horn pointwise.  In particular, on the
missing face it fixes the whole boundary.  This is the geometric reduction used to replace one
face of a normalized simplex boundary by its attaching map through all the other faces.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {d : ℕ}

/-- The least barycentric coordinate away from `i`. -/
def simplexHornMin (i : Fin (d + 2)) (z : stdSimplex ℝ (Fin (d + 2))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j : Fin (d + 1) ↦ z.1 (i.succAbove j)

theorem simplexHornMin_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : 0 ≤ simplexHornMin i z := by
  apply Finset.le_inf' Finset.univ_nonempty
  intro j hj
  exact z.2.1 _

theorem simplexHornMin_le (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornMin i z ≤ z.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem exists_simplexHornMin_eq (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), simplexHornMin i z = z.1 (i.succAbove j) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin (d + 1)))) Finset.univ_nonempty
    (fun j ↦ z.1 (i.succAbove j))
  exact ⟨j, hj⟩

/-- Barycentric coordinates of the retraction onto the horn opposite face `i`. -/
def simplexHornRetractCoords (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 2) → ℝ :=
  i.insertNth (z.1 i + (d + 1 : ℝ) * simplexHornMin i z)
    (fun j ↦ z.1 (i.succAbove j) - simplexHornMin i z)

@[simp]
theorem simplexHornRetractCoords_same (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    simplexHornRetractCoords i z i = z.1 i + (d + 1 : ℝ) * simplexHornMin i z := by
  simp [simplexHornRetractCoords]

@[simp]
theorem simplexHornRetractCoords_succAbove (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornRetractCoords i z (i.succAbove j) =
      z.1 (i.succAbove j) - simplexHornMin i z := by
  simp [simplexHornRetractCoords]

theorem simplexHornRetractCoords_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    0 ≤ simplexHornRetractCoords i z k := by
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · rw [simplexHornRetractCoords_same]
    have hd : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    exact add_nonneg (z.2.1 i)
      (mul_nonneg hd (simplexHornMin_nonneg i z))
  · rw [simplexHornRetractCoords_succAbove]
    exact sub_nonneg.mpr (simplexHornMin_le i z j)

theorem sum_simplexHornRetractCoords (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∑ k, simplexHornRetractCoords i z k = 1 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [simplexHornRetractCoords_same, simplexHornRetractCoords_succAbove,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hz := z.2.2
  rw [Fin.sum_univ_succAbove _ i] at hz
  norm_num at hz ⊢
  linarith

/-- The explicit retraction of a simplex onto the horn obtained by deleting face `i`. -/
def simplexHornRetract (i : Fin (d + 2)) :
    C(stdSimplex ℝ (Fin (d + 2)), stdSimplex ℝ (Fin (d + 2))) where
  toFun z := ⟨simplexHornRetractCoords i z,
    simplexHornRetractCoords_nonneg i z, sum_simplexHornRetractCoords i z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
    · simp only [simplexHornRetractCoords_same]
      apply Continuous.add
      · exact (continuous_apply i).comp continuous_subtype_val
      · exact continuous_const.mul (Continuous.finset_inf'_apply Finset.univ_nonempty
          (fun j _ ↦ (continuous_apply (i.succAbove j)).comp continuous_subtype_val))
    · simp only [simplexHornRetractCoords_succAbove]
      exact ((continuous_apply (i.succAbove j)).comp continuous_subtype_val).sub
        (Continuous.finset_inf'_apply Finset.univ_nonempty
          (fun k _ ↦ (continuous_apply (i.succAbove k)).comp continuous_subtype_val))

@[simp]
theorem simplexHornRetract_apply_coe (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    (simplexHornRetract i z).1 k = simplexHornRetractCoords i z k :=
  rfl

/-- The horn opposite `i`, described as the points having a zero coordinate away from `i`. -/
def simplexHorn (i : Fin (d + 2)) : Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | ∃ j : Fin (d + 1), z.1 (i.succAbove j) = 0}

theorem simplexHornRetract_mem (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : simplexHornRetract i z ∈ simplexHorn i := by
  obtain ⟨j, hj⟩ := exists_simplexHornMin_eq i z
  refine ⟨j, ?_⟩
  rw [simplexHornRetract_apply_coe, simplexHornRetractCoords_succAbove, hj, sub_self]

theorem simplexHornMin_eq_zero_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornMin i z = 0 := by
  obtain ⟨j, hj⟩ := hz
  apply le_antisymm
  · simpa [hj] using simplexHornMin_le i z j
  · exact simplexHornMin_nonneg i z

theorem simplexHornRetract_eq_self_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornRetract i z = z := by
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]

/-- Straight-line deformation from the identity to the horn retraction. -/
def simplexHornDeformation (i : Fin (d + 2)) :
    C(I × stdSimplex ℝ (Fin (d + 2)), stdSimplex ℝ (Fin (d + 2))) where
  toFun p :=
    ⟨AffineMap.lineMap p.2.1 (simplexHornRetract i p.2).1 (p.1 : ℝ),
      (convex_stdSimplex ℝ (Fin (d + 2))).lineMap_mem p.2.2
        (simplexHornRetract i p.2).2 p.1.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply]
    have hr : Continuous fun p : I × stdSimplex ℝ (Fin (d + 2)) ↦
        (simplexHornRetract i p.2).1 :=
      continuous_subtype_val.comp ((simplexHornRetract i).continuous.comp continuous_snd)
    have hz : Continuous fun p : I × stdSimplex ℝ (Fin (d + 2)) ↦ p.2.1 :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous fun p : I × stdSimplex ℝ (Fin (d + 2)) ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact (ht.smul (hr.sub hz)).add hz

@[simp]
theorem simplexHornDeformation_zero (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : simplexHornDeformation i (0, z) = z := by
  apply Subtype.ext
  simp [simplexHornDeformation, AffineMap.lineMap_apply]

@[simp]
theorem simplexHornDeformation_one (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    simplexHornDeformation i (1, z) = simplexHornRetract i z := by
  apply Subtype.ext
  simp [simplexHornDeformation, AffineMap.lineMap_apply]

theorem simplexHornDeformation_eq_self_of_mem (i : Fin (d + 2))
    (t : I) {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornDeformation i (t, z) = z := by
  apply Subtype.ext
  change AffineMap.lineMap z.1 (simplexHornRetract i z).1 (t : ℝ) = z.1
  rw [show simplexHornRetract i z = z from simplexHornRetract_eq_self_of_mem i hz]
  simp

/-- A point on the boundary of the missing face lies in the horn. -/
theorem faceMap_mem_simplexHorn (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexHorn i := by
  obtain ⟨j, hj⟩ := hz
  refine ⟨j, ?_⟩
  rw [faceMap_coe_succAbove, hj]

/-- The missing face, pushed by the horn retraction through all the other faces. -/
def simplexHornAttachingMap (i : Fin (d + 2)) :
    C(stdSimplex ℝ (Fin (d + 1)), stdSimplex ℝ (Fin (d + 2))) :=
  (simplexHornRetract i).comp (faceCM i)

@[simp]
theorem simplexHornAttachingMap_apply (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornAttachingMap i z = simplexHornRetract i (faceMap i z) :=
  rfl

/-- The attaching map lands in the horn opposite the missing face. -/
theorem simplexHornAttachingMap_mem (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornAttachingMap i z ∈ simplexHorn i :=
  simplexHornRetract_mem i (faceMap i z)

/-- The attaching map agrees with the original face inclusion on its boundary. -/
theorem simplexHornAttachingMap_eq_faceMap_of_mem_bdry (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    simplexHornAttachingMap i z = faceMap i z :=
  simplexHornRetract_eq_self_of_mem i (faceMap_mem_simplexHorn i z hz)

/-- The relative deformation of the missing face to its attaching map through the horn. -/
def simplexFaceHornDeformation (i : Fin (d + 2)) :
    C(I × stdSimplex ℝ (Fin (d + 1)), stdSimplex ℝ (Fin (d + 2))) :=
  (simplexHornDeformation i).comp
    ⟨fun p ↦ (p.1, faceMap i p.2),
      continuous_fst.prodMk ((faceCM i).continuous.comp continuous_snd)⟩

@[simp]
theorem simplexFaceHornDeformation_zero (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) :
    simplexFaceHornDeformation i (0, z) = faceMap i z :=
  simplexHornDeformation_zero i (faceMap i z)

@[simp]
theorem simplexFaceHornDeformation_one (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) :
    simplexFaceHornDeformation i (1, z) = simplexHornAttachingMap i z :=
  simplexHornDeformation_one i (faceMap i z)

/-- The face-to-horn deformation fixes the boundary of the missing face pointwise. -/
theorem simplexFaceHornDeformation_eq_faceMap_of_mem_bdry (i : Fin (d + 2))
    (t : I) (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    simplexFaceHornDeformation i (t, z) = faceMap i z :=
  simplexHornDeformation_eq_self_of_mem i t (faceMap_mem_simplexHorn i z hz)

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

namespace NormalizedSimplexBoundary

/-- The horn attaching map of a face, parameterized by stick-breaking coordinates and followed
by the higher singular simplex. -/
noncomputable def hornAttachingStickMap (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) : C(I^Fin (n + 2), X) :=
  (sngEquiv (TopCat.of X) (n + 3) b.simplex).comp
    ((simplexHornAttachingMap i).comp (stickSimplex (n + 2)))

@[simp]
theorem hornAttachingStickMap_apply (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) (t : I^Fin (n + 2)) :
    b.hornAttachingStickMap i t =
      sngEquiv (TopCat.of X) (n + 3) b.simplex
        (simplexHornAttachingMap i (stickSimplex (n + 2) t)) :=
  rfl

/-- The horn attaching map is based on the whole cubical boundary. -/
theorem hornAttachingStickMap_boundary (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) (t : I^Fin (n + 2))
    (ht : t ∈ Cube.boundary (Fin (n + 2))) : b.hornAttachingStickMap i t = x := by
  rw [hornAttachingStickMap_apply,
    simplexHornAttachingMap_eq_faceMap_of_mem_bdry i (stickSimplex (n + 2) t)
      (stickSimplex_mem_bdry (n + 2) t ht)]
  apply b.simplex_eq_of_mem_codimTwo
  exact faceMap_stickSimplex_mem_codimTwo i t ht

/-- The horn attaching map as a generalized loop. -/
noncomputable def hornAttachingStickLoop (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) : Ω^ (Fin (n + 2)) X x :=
  ⟨b.hornAttachingStickMap i, b.hornAttachingStickMap_boundary i⟩

/-- Composing the relative face-to-horn deformation with the higher simplex and stick-breaking
coordinates gives a homotopy from the original normalized face to its horn attaching map. -/
noncomputable def faceHornAttachingHomotopy (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) :
    ContinuousMap.Homotopy (b.face i).stickMap (b.hornAttachingStickMap i) where
  toContinuousMap :=
    (sngEquiv (TopCat.of X) (n + 3) b.simplex).comp
      ((simplexFaceHornDeformation i).comp
        ⟨fun p ↦ (p.1, stickSimplex (n + 2) p.2),
          continuous_fst.prodMk ((stickSimplex (n + 2)).continuous.comp continuous_snd)⟩)
  map_zero_left t := by
    calc
      _ = sngEquiv (TopCat.of X) (n + 3) b.simplex
          (faceMap i (stickSimplex (n + 2) t)) :=
        congrArg _ (simplexFaceHornDeformation_zero i (stickSimplex (n + 2) t))
      _ = (b.face i).stickMap t := by
        rw [← apply_δ, ← b.face_simplex]
        rfl
  map_one_left t := by
    calc
      _ = sngEquiv (TopCat.of X) (n + 3) b.simplex
          (simplexHornAttachingMap i (stickSimplex (n + 2) t)) :=
        congrArg _ (simplexFaceHornDeformation_one i (stickSimplex (n + 2) t))
      _ = b.hornAttachingStickMap i t := rfl

/-- The face-to-horn homotopy fixes the whole cubical boundary. -/
theorem faceHornAttachingHomotopy_fixed (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) (a : I) (t : I^Fin (n + 2))
    (ht : t ∈ Cube.boundary (Fin (n + 2))) :
    b.faceHornAttachingHomotopy i (a, t) = (b.face i).stickMap t := by
  have hz : stickSimplex (n + 2) t ∈ bdry (n + 2) :=
    stickSimplex_mem_bdry (n + 2) t ht
  calc
    b.faceHornAttachingHomotopy i (a, t) =
        sngEquiv (TopCat.of X) (n + 3) b.simplex
          (faceMap i (stickSimplex (n + 2) t)) := by
      change sngEquiv (TopCat.of X) (n + 3) b.simplex
          (simplexFaceHornDeformation i (a, stickSimplex (n + 2) t)) = _
      rw [simplexFaceHornDeformation_eq_faceMap_of_mem_bdry i a _ hz]
    _ = (b.face i).stickMap t := by
      rw [← apply_δ, ← b.face_simplex]
      rfl

/-- Every normalized face loop is homotopic relative to the cube boundary to the attaching map
of that face through the union of all the other faces. -/
theorem faceLoop_homotopic_hornAttachingStickLoop
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4)) :
    GenLoop.Homotopic (b.face i).toStickGenLoop (b.hornAttachingStickLoop i) := by
  refine ⟨{
    toHomotopy := b.faceHornAttachingHomotopy i
    prop' := fun a t ht ↦ b.faceHornAttachingHomotopy_fixed i a t ht }⟩

/-- Replacing a normalized face by its horn attaching map does not change its stick-loop
homotopy class. -/
theorem faceStickHomotopyClass_eq_hornAttaching
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4)) :
    (b.face i).stickHomotopyClass =
      (⟦b.hornAttachingStickLoop i⟧ : π_ (n + 2) X x) :=
  Quotient.sound (b.faceLoop_homotopic_hornAttachingStickLoop i)

end NormalizedSimplexBoundary

end Submission
