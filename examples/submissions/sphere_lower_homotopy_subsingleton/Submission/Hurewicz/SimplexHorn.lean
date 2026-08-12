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

/-- The least coordinate away from the chosen face varies continuously. -/
theorem continuous_simplexHornMin (i : Fin (d + 2)) :
    Continuous (simplexHornMin i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ ↦ (continuous_apply (i.succAbove j)).comp continuous_subtype_val)

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
      · exact continuous_const.mul (continuous_simplexHornMin i)
    · simp only [simplexHornRetractCoords_succAbove]
      exact ((continuous_apply (i.succAbove j)).comp continuous_subtype_val).sub
        (continuous_simplexHornMin i)

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

/-! ### The barycentric regions of the horn attaching map -/

/-- The closed region of the missing face on which coordinate `j` realizes the minimum. -/
def simplexHornRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | simplexHornMin i (faceMap i z) = z.1 j}

theorem isClosed_simplexHornRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    IsClosed (simplexHornRegion i j) := by
  apply isClosed_eq
  · exact (continuous_simplexHornMin i).comp (faceCM i).continuous
  · exact (continuous_apply j).comp continuous_subtype_val

/-- The minimum regions cover the whole missing face. -/
theorem exists_mem_simplexHornRegion (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) :
    ∃ j : Fin (d + 1), z ∈ simplexHornRegion i j := by
  obtain ⟨j, hj⟩ := exists_simplexHornMin_eq i (faceMap i z)
  refine ⟨j, ?_⟩
  change simplexHornMin i (faceMap i z) = z.1 j
  simpa using hj

/-- A coordinate which is no larger than every other coordinate realizes the horn minimum on
the missing face. -/
theorem simplexHornMin_faceMap_eq_of_le (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (j : Fin (d + 1))
    (hj : ∀ k, z.1 j ≤ z.1 k) : simplexHornMin i (faceMap i z) = z.1 j := by
  apply le_antisymm
  · simpa using simplexHornMin_le i (faceMap i z) j
  · apply Finset.le_inf' Finset.univ_nonempty
    intro k hk
    simpa using hj k

/-- On minimum region `j`, the horn attaching map lies on the remaining face indexed by
`i.succAbove j`. -/
theorem simplexHornAttachingMap_coord_eq_zero_of_mem_region
    (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ simplexHornRegion i j) :
    (simplexHornAttachingMap i z).1 (i.succAbove j) = 0 := by
  rw [simplexHornAttachingMap_apply, simplexHornRetract_apply_coe,
    simplexHornRetractCoords_succAbove, faceMap_coe_succAbove]
  exact sub_eq_zero.mpr hz.symm

/-- The attaching map on minimum region `j`, expressed in the barycentric coordinates of the
remaining face `i.succAbove j`. -/
def simplexHornRegionFaceMap (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C({z // z ∈ simplexHornRegion i j}, stdSimplex ℝ (Fin (d + 1))) where
  toFun z := dropMap (i.succAbove j)
    (simplexHornAttachingMap_coord_eq_zero_of_mem_region i j z.1 z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    change Continuous fun z : {z // z ∈ simplexHornRegion i j} ↦
      (simplexHornAttachingMap i z.1).1 ((i.succAbove j).succAbove k)
    exact ((continuous_apply ((i.succAbove j).succAbove k)).comp continuous_subtype_val).comp
      ((simplexHornAttachingMap i).continuous.comp continuous_subtype_val)

/-- On a minimum region, the attaching map factors exactly through the corresponding remaining
face. -/
theorem faceMap_simplexHornRegionFaceMap (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornRegion i j}) :
    faceMap (i.succAbove j) (simplexHornRegionFaceMap i j z) =
      simplexHornAttachingMap i z.1 :=
  faceMap_dropMap (i.succAbove j)
    (simplexHornAttachingMap_coord_eq_zero_of_mem_region i j z.1 z.2)

/-- The distinguished coordinate of a minimum-region face map records the transferred minimum
mass. -/
theorem simplexHornRegionFaceMap_center (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornRegion i j}) :
    (simplexHornRegionFaceMap i j z).1 (j.predAbove i) =
      (d + 1 : ℝ) * z.1.1 j := by
  calc
    _ = (faceMap (i.succAbove j) (simplexHornRegionFaceMap i j z)).1
        ((i.succAbove j).succAbove (j.predAbove i)) := by
      rw [faceMap_coe_succAbove]
    _ = (simplexHornAttachingMap i z.1).1
        ((i.succAbove j).succAbove (j.predAbove i)) := by
      rw [faceMap_simplexHornRegionFaceMap]
    _ = (d + 1 : ℝ) * z.1.1 j := by
      rw [Fin.succAbove_succAbove_predAbove,
        simplexHornAttachingMap_apply, simplexHornRetract_apply_coe,
        simplexHornRetractCoords_same, faceMap_coe_same, zero_add]
      exact congrArg ((d + 1 : ℝ) * ·) z.2

/-- Every other coordinate of a minimum-region face map is obtained by subtracting the minimum
from the corresponding source coordinate. -/
theorem simplexHornRegionFaceMap_succAbove (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornRegion i j}) (k : Fin d) :
    (simplexHornRegionFaceMap i j z).1 ((j.predAbove i).succAbove k) =
      z.1.1 (j.succAbove k) - z.1.1 j := by
  calc
    _ = (faceMap (i.succAbove j) (simplexHornRegionFaceMap i j z)).1
        ((i.succAbove j).succAbove ((j.predAbove i).succAbove k)) := by
      rw [faceMap_coe_succAbove]
    _ = (simplexHornAttachingMap i z.1).1
        ((i.succAbove j).succAbove ((j.predAbove i).succAbove k)) := by
      rw [faceMap_simplexHornRegionFaceMap]
    _ = z.1.1 (j.succAbove k) - z.1.1 j := by
      rw [Fin.succAbove_succAbove_succAbove_predAbove,
        simplexHornAttachingMap_apply, simplexHornRetract_apply_coe,
        simplexHornRetractCoords_succAbove, faceMap_coe_succAbove, z.2]

/-- Barycentric coordinates for the inverse chart from a remaining face to its minimum region.
The distinguished target coordinate is divided equally among all source coordinates, while the
other target coordinates are added to their corresponding shares. -/
def simplexHornRegionInverseCoords (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) : Fin (d + 1) → ℝ :=
  j.insertNth (y.1 (j.predAbove i) / (d + 1 : ℝ))
    (fun k ↦ y.1 ((j.predAbove i).succAbove k) +
      y.1 (j.predAbove i) / (d + 1 : ℝ))

@[simp]
theorem simplexHornRegionInverseCoords_same (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornRegionInverseCoords i j y j = y.1 (j.predAbove i) / (d + 1 : ℝ) := by
  simp [simplexHornRegionInverseCoords]

@[simp]
theorem simplexHornRegionInverseCoords_succAbove (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) (k : Fin d) :
    simplexHornRegionInverseCoords i j y (j.succAbove k) =
      y.1 ((j.predAbove i).succAbove k) +
        y.1 (j.predAbove i) / (d + 1 : ℝ) := by
  simp [simplexHornRegionInverseCoords]

theorem simplexHornRegionInverseCoords_nonneg (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) (k : Fin (d + 1)) :
    0 ≤ simplexHornRegionInverseCoords i j y k := by
  refine Fin.succAboveCases j ?_ (fun l ↦ ?_) k
  · rw [simplexHornRegionInverseCoords_same]
    exact div_nonneg (y.2.1 _) (by positivity)
  · rw [simplexHornRegionInverseCoords_succAbove]
    exact add_nonneg (y.2.1 _) (div_nonneg (y.2.1 _) (by positivity))

theorem sum_simplexHornRegionInverseCoords (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    ∑ k, simplexHornRegionInverseCoords i j y k = 1 := by
  rw [Fin.sum_univ_succAbove _ j]
  simp only [simplexHornRegionInverseCoords_same,
    simplexHornRegionInverseCoords_succAbove, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hy := y.2.2
  rw [Fin.sum_univ_succAbove _ (j.predAbove i)] at hy
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  change y.1 (j.predAbove i) / (d + 1 : ℝ) +
      ((∑ k, y.1 ((j.predAbove i).succAbove k)) +
        d * (y.1 (j.predAbove i) / (d + 1 : ℝ))) = 1
  calc
    _ = (d + 1 : ℝ) * (y.1 (j.predAbove i) / (d + 1 : ℝ)) +
        ∑ k, y.1 ((j.predAbove i).succAbove k) := by ring
    _ = y.1 (j.predAbove i) +
        ∑ k, y.1 ((j.predAbove i).succAbove k) := by
      field_simp [hd]
    _ = 1 := hy

/-- The simplex-valued inverse chart before recording membership in the minimum region. -/
def simplexHornRegionInverseSimplex (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C(stdSimplex ℝ (Fin (d + 1)), stdSimplex ℝ (Fin (d + 1))) where
  toFun y := ⟨simplexHornRegionInverseCoords i j y,
    simplexHornRegionInverseCoords_nonneg i j y,
    sum_simplexHornRegionInverseCoords i j y⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    refine Fin.succAboveCases j ?_ (fun l ↦ ?_) k
    · simp only [simplexHornRegionInverseCoords, Fin.insertNth_apply_same]
      exact ((continuous_apply (j.predAbove i)).comp continuous_subtype_val).div_const _
    · simp only [simplexHornRegionInverseCoords, Fin.insertNth_apply_succAbove]
      exact ((continuous_apply ((j.predAbove i).succAbove l)).comp continuous_subtype_val).add
        (((continuous_apply (j.predAbove i)).comp continuous_subtype_val).div_const _)

/-- The inverse chart lands in the prescribed minimum region. -/
theorem simplexHornRegionInverseSimplex_mem (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornRegionInverseSimplex i j y ∈ simplexHornRegion i j := by
  apply simplexHornMin_faceMap_eq_of_le
  intro k
  refine Fin.succAboveCases j ?_ (fun l ↦ ?_) k
  · exact le_rfl
  · rw [show (simplexHornRegionInverseSimplex i j y).1 j =
        simplexHornRegionInverseCoords i j y j from rfl,
      show (simplexHornRegionInverseSimplex i j y).1 (j.succAbove l) =
        simplexHornRegionInverseCoords i j y (j.succAbove l) from rfl,
      simplexHornRegionInverseCoords_same, simplexHornRegionInverseCoords_succAbove]
    linarith [y.2.1 ((j.predAbove i).succAbove l)]

/-- The continuous inverse chart from a remaining face onto its minimum region. -/
def simplexHornRegionInverse (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C(stdSimplex ℝ (Fin (d + 1)), {z // z ∈ simplexHornRegion i j}) where
  toFun y := ⟨simplexHornRegionInverseSimplex i j y,
    simplexHornRegionInverseSimplex_mem i j y⟩
  continuous_toFun := Continuous.subtype_mk (simplexHornRegionInverseSimplex i j).continuous _

/-- Applying the minimum-region face chart after its inverse recovers the original simplex. -/
theorem simplexHornRegionFaceMap_inverse (i : Fin (d + 2)) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornRegionFaceMap i j (simplexHornRegionInverse i j y) = y := by
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases (j.predAbove i) ?_ (fun l ↦ ?_) k
  · rw [simplexHornRegionFaceMap_center]
    change (d + 1 : ℝ) *
      (simplexHornRegionInverseCoords i j y j) = y.1 (j.predAbove i)
    rw [simplexHornRegionInverseCoords_same]
    field_simp
  · rw [simplexHornRegionFaceMap_succAbove]
    change simplexHornRegionInverseCoords i j y (j.succAbove l) -
        simplexHornRegionInverseCoords i j y j =
      y.1 ((j.predAbove i).succAbove l)
    rw [simplexHornRegionInverseCoords_succAbove,
      simplexHornRegionInverseCoords_same]
    ring

/-- Applying the inverse chart after the minimum-region face chart recovers the region point. -/
theorem simplexHornRegionInverse_faceMap (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornRegion i j}) :
    simplexHornRegionInverse i j (simplexHornRegionFaceMap i j z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases j ?_ (fun l ↦ ?_) k
  · rw [show (simplexHornRegionInverse i j (simplexHornRegionFaceMap i j z)).1.1 j =
        simplexHornRegionInverseCoords i j (simplexHornRegionFaceMap i j z) j from rfl,
      simplexHornRegionInverseCoords_same]
    change (simplexHornRegionFaceMap i j z).1 (j.predAbove i) /
        (d + 1 : ℝ) = z.1.1 j
    rw [simplexHornRegionFaceMap_center]
    field_simp
  · rw [show
        (simplexHornRegionInverse i j (simplexHornRegionFaceMap i j z)).1.1
            (j.succAbove l) =
          simplexHornRegionInverseCoords i j (simplexHornRegionFaceMap i j z)
            (j.succAbove l) from rfl,
      simplexHornRegionInverseCoords_succAbove]
    change (simplexHornRegionFaceMap i j z).1 ((j.predAbove i).succAbove l) +
        (simplexHornRegionFaceMap i j z).1 (j.predAbove i) /
          (d + 1 : ℝ) = z.1.1 (j.succAbove l)
    rw [simplexHornRegionFaceMap_succAbove, simplexHornRegionFaceMap_center]
    field_simp
    ring

/-- Each minimum region is canonically homeomorphic to a standard simplex, and under this
homeomorphism the horn attaching map is the corresponding remaining-face inclusion. -/
def simplexHornRegionHomeomorph (i : Fin (d + 2)) (j : Fin (d + 1)) :
    stdSimplex ℝ (Fin (d + 1)) ≃ₜ {z // z ∈ simplexHornRegion i j} where
  toFun := simplexHornRegionInverse i j
  invFun := simplexHornRegionFaceMap i j
  left_inv := simplexHornRegionFaceMap_inverse i j
  right_inv := simplexHornRegionInverse_faceMap i j
  continuous_toFun := (simplexHornRegionInverse i j).continuous
  continuous_invFun := (simplexHornRegionFaceMap i j).continuous

/-- The boundary of a minimum-region chart consists exactly of the original missing-face
boundary together with its overlaps with the other minimum regions. -/
theorem simplexHornRegionFaceMap_mem_bdry_iff (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornRegion i j}) :
    simplexHornRegionFaceMap i j z ∈ bdry d ↔
      z.1 ∈ bdry d ∨
        ∃ k : Fin (d + 1), k ≠ j ∧ z.1 ∈ simplexHornRegion i k := by
  constructor
  · rintro ⟨l, hl⟩
    by_cases hla : l = j.predAbove i
    · subst l
      rw [simplexHornRegionFaceMap_center] at hl
      have hjzero : z.1.1 j = 0 := by
        rcases mul_eq_zero.mp hl with h | h
        · exact False.elim ((by positivity : (d + 1 : ℝ) ≠ 0) h)
        · exact h
      exact Or.inl ⟨j, hjzero⟩
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hla
      rw [← hk, simplexHornRegionFaceMap_succAbove] at hl
      have heq : z.1.1 (j.succAbove k) = z.1.1 j := sub_eq_zero.mp hl
      refine Or.inr ⟨j.succAbove k, Fin.succAbove_ne j k, ?_⟩
      exact z.2.trans heq.symm
  · rintro (hz | ⟨k, hkj, hk⟩)
    · obtain ⟨l, hl⟩ := hz
      have hjzero : z.1.1 j = 0 := by
        apply le_antisymm
        · calc
            z.1.1 j = simplexHornMin i (faceMap i z.1) := z.2.symm
            _ ≤ z.1.1 l := by simpa using simplexHornMin_le i (faceMap i z.1) l
            _ = 0 := hl
        · exact z.1.2.1 j
      refine ⟨j.predAbove i, ?_⟩
      rw [simplexHornRegionFaceMap_center, hjzero, mul_zero]
    · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hkj
      refine ⟨(j.predAbove i).succAbove l, ?_⟩
      rw [simplexHornRegionFaceMap_succAbove, hl]
      change simplexHornMin i (faceMap i z.1) = z.1.1 k at hk
      rw [← z.2, hk, sub_self]

/-- The overlap of two distinct minimum regions is sent into the codimension-two skeleton of
the ambient simplex. -/
theorem simplexHornAttachingMap_mem_codimTwo_of_mem_regions
    (i : Fin (d + 2)) {j k : Fin (d + 1)} (hjk : j ≠ k)
    (z : stdSimplex ℝ (Fin (d + 1)))
    (hj : z ∈ simplexHornRegion i j) (hk : z ∈ simplexHornRegion i k) :
    simplexHornAttachingMap i z ∈ simplexCodimTwo (d + 1) := by
  refine ⟨i.succAbove j, i.succAbove k, ?_,
    simplexHornAttachingMap_coord_eq_zero_of_mem_region i j z hj,
    simplexHornAttachingMap_coord_eq_zero_of_mem_region i k z hk⟩
  exact fun h ↦ hjk (Fin.succAbove_right_injective h)

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

/-- On one minimum region, the horn attaching map is exactly the corresponding remaining
normalized simplex face. -/
theorem simplex_hornAttaching_eq_face_on_region
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4)) (j : Fin (n + 3))
    (z : stdSimplex ℝ (Fin (n + 3))) (hz : z ∈ simplexHornRegion i j) :
    sngEquiv (TopCat.of X) (n + 3) b.simplex (simplexHornAttachingMap i z) =
      sngEquiv (TopCat.of X) (n + 2) (b.face (i.succAbove j)).simplex
        (simplexHornRegionFaceMap i j ⟨z, hz⟩) := by
  rw [← faceMap_simplexHornRegionFaceMap i j ⟨z, hz⟩]
  rw [← apply_δ, ← b.face_simplex]

/-- Distinct minimum-region pieces of the horn attaching map meet only at the normalized
basepoint. -/
theorem simplex_hornAttaching_eq_basepoint_of_mem_regions
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4))
    {j k : Fin (n + 3)} (hjk : j ≠ k) (z : stdSimplex ℝ (Fin (n + 3)))
    (hj : z ∈ simplexHornRegion i j) (hk : z ∈ simplexHornRegion i k) :
    sngEquiv (TopCat.of X) (n + 3) b.simplex (simplexHornAttachingMap i z) = x := by
  apply b.simplex_eq_of_mem_codimTwo
  exact simplexHornAttachingMap_mem_codimTwo_of_mem_regions i hjk z hj hk

/-- In stick-breaking coordinates, every minimum-region piece of the horn loop factors through
the corresponding remaining normalized face. -/
theorem hornAttachingStickMap_eq_face_on_region
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4)) (j : Fin (n + 3))
    (t : I^Fin (n + 2)) (ht : stickSimplex (n + 2) t ∈ simplexHornRegion i j) :
    b.hornAttachingStickMap i t =
      sngEquiv (TopCat.of X) (n + 2) (b.face (i.succAbove j)).simplex
        (simplexHornRegionFaceMap i j ⟨stickSimplex (n + 2) t, ht⟩) :=
  b.simplex_hornAttaching_eq_face_on_region i j _ ht

/-- In stick-breaking coordinates, overlaps of distinct minimum regions are collapsed to the
basepoint. -/
theorem hornAttachingStickMap_eq_basepoint_of_mem_regions
    (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4))
    {j k : Fin (n + 3)} (hjk : j ≠ k) (t : I^Fin (n + 2))
    (hj : stickSimplex (n + 2) t ∈ simplexHornRegion i j)
    (hk : stickSimplex (n + 2) t ∈ simplexHornRegion i k) :
    b.hornAttachingStickMap i t = x :=
  b.simplex_hornAttaching_eq_basepoint_of_mem_regions i hjk _ hj hk

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
