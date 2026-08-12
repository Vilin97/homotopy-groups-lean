/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.CubicalShell
import Submission.Hurewicz.NormalizedBoundary

/-!
# Stick-breaking coordinates on normalized simplex boundaries

The stick-breaking map turns a normalized simplex into a cubical loop without choosing a
cube--simplex homeomorphism.  More importantly, applying it to the simplex underlying a
normalized simplex boundary gives a cubical shell with an explicit list of faces:

* upper cube face `i` is normalized simplex face `i`;
* the final lower cube face is the final normalized simplex face;
* every other lower cube face is constant at the basepoint.

This is the geometric face decomposition needed for the cubical homotopy-addition theorem.  Its
orientation convention agrees directly with the alternating simplicial boundary.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

namespace NormalizedSimplex

/-- A normalized simplex parameterized by stick-breaking coordinates on the cube. -/
noncomputable def stickMap (s : NormalizedSimplex n X x) : C(I^Fin (n + 2), X) :=
  (sngEquiv (TopCat.of X) (n + 2) s.simplex).comp (stickSimplex (n + 2))

@[simp]
theorem stickMap_apply (s : NormalizedSimplex n X x) (t : I^Fin (n + 2)) :
    s.stickMap t = sngEquiv (TopCat.of X) (n + 2) s.simplex (stickSimplex (n + 2) t) :=
  rfl

/-- Stick-breaking parameterization is constant on the boundary of its cube. -/
theorem stickMap_boundary (s : NormalizedSimplex n X x) (t : I^Fin (n + 2))
    (ht : t ∈ Cube.boundary (Fin (n + 2))) : s.stickMap t = x :=
  s.simplex_boundary _ (stickSimplex_mem_bdry (n + 2) t ht)

/-- A normalized simplex as a cubical loop in stick-breaking coordinates. -/
noncomputable def toStickGenLoop (s : NormalizedSimplex n X x) : Ω^ (Fin (n + 2)) X x :=
  ⟨s.stickMap, s.stickMap_boundary⟩

/-- The homotopy class represented by the stick-breaking parameterization of a normalized
simplex. -/
noncomputable def stickHomotopyClass (s : NormalizedSimplex n X x) : π_ (n + 2) X x :=
  ⟦s.toStickGenLoop⟧

end NormalizedSimplex

namespace NormalizedSimplexBoundary

/-- The higher simplex of a normalized boundary, parameterized by the stick-breaking cube. -/
noncomputable def stickCubeMap (b : NormalizedSimplexBoundary n X x) :
    C(I^Fin (n + 3), X) :=
  (sngEquiv (TopCat.of X) (n + 3) b.simplex).comp (stickSimplex (n + 3))

/-- The stick-breaking cube of a normalized simplex boundary, packaged as a generic cubical
shell. -/
noncomputable def stickShell (b : NormalizedSimplexBoundary n X x) :
    CubicalShell (n + 2) X x where
  map := b.stickCubeMap
  codimTwo t ht := by
    apply b.simplex_eq_of_mem_codimTwo
    exact stickSimplex_mem_codimTwo_of_mem_cubeCodimTwo t ht

@[simp]
theorem stickShell_map_apply (b : NormalizedSimplexBoundary n X x)
    (t : I^Fin (n + 3)) :
    b.stickShell.map t = b.stickCubeMap t :=
  rfl

@[simp]
theorem stickCubeMap_apply (b : NormalizedSimplexBoundary n X x) (t : I^Fin (n + 3)) :
    b.stickCubeMap t =
      sngEquiv (TopCat.of X) (n + 3) b.simplex (stickSimplex (n + 3) t) :=
  rfl

/-- Upper cube face `i` is the stick-breaking parameterization of simplex face `i`. -/
theorem stickCubeMap_upper_face (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) (t : I^Fin (n + 2)) :
    b.stickCubeMap (cubeFace i 1 t) = (b.face i.castSucc).stickMap t := by
  rw [stickCubeMap_apply, stickSimplex_cubeFace_one]
  change sngEquiv (TopCat.of X) (n + 3) b.simplex
      (faceMap i.castSucc (stickSimplex (n + 2) t)) =
    sngEquiv (TopCat.of X) (n + 2) (b.face i.castSucc).simplex
      (stickSimplex (n + 2) t)
  rw [← apply_δ, ← b.face_simplex]

/-- The final lower cube face is the stick-breaking parameterization of the final simplex
face. -/
theorem stickCubeMap_last_lower_face (b : NormalizedSimplexBoundary n X x)
    (t : I^Fin (n + 2)) :
    b.stickCubeMap (cubeFace (Fin.last (n + 2)) 0 t) =
      (b.face (Fin.last (n + 3))).stickMap t := by
  rw [stickCubeMap_apply, stickSimplex_cubeFace_last_zero]
  change sngEquiv (TopCat.of X) (n + 3) b.simplex
      (faceMap (Fin.last (n + 3)) (stickSimplex (n + 2) t)) =
    sngEquiv (TopCat.of X) (n + 2) (b.face (Fin.last (n + 3))).simplex
      (stickSimplex (n + 2) t)
  rw [← apply_δ, ← b.face_simplex]

/-- Every nonfinal lower cube face is constant at the basepoint. -/
theorem stickCubeMap_lower_face (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) (t : I^Fin (n + 2)) :
    b.stickCubeMap (cubeFace i 0 t) = x := by
  apply b.simplex_eq_of_mem_codimTwo
  exact stickSimplex_cubeFace_zero_mem_codimTwo i hi t

/-- Every nonfinal lower face is constant in the ambient-face sense used by a generic cubical
shell. -/
theorem stickShell_lowerFace_isConstant (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) :
    b.stickShell.IsConstantFace i 0 := by
  intro t ht
  let u : I^Fin (n + 2) := Fin.removeNth i t
  have hrep : t = cubeFace i 0 u := by
    change t = i.insertNth 0 u
    rw [← ht]
    exact (Fin.insertNth_self_removeNth i t).symm
  rw [hrep]
  exact b.stickCubeMap_lower_face i hi u

/-- An upper face of the stick-breaking cube, regarded as a generalized loop. -/
noncomputable def stickUpperFaceLoop (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) : Ω^ (Fin (n + 2)) X x :=
  ⟨b.stickCubeMap.comp (cubeFace i 1), fun t ht ↦ by
    apply b.simplex_eq_of_mem_codimTwo
    exact stickSimplex_cubeFace_mem_codimTwo i 1 (Or.inr rfl) t ht⟩

/-- A lower face of the stick-breaking cube, regarded as a generalized loop. -/
noncomputable def stickLowerFaceLoop (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) : Ω^ (Fin (n + 2)) X x :=
  ⟨b.stickCubeMap.comp (cubeFace i 0), fun t ht ↦ by
    apply b.simplex_eq_of_mem_codimTwo
    exact stickSimplex_cubeFace_mem_codimTwo i 0 (Or.inl rfl) t ht⟩

/-- The specialized upper face loop agrees with the face supplied by the generic shell. -/
@[simp]
theorem stickShell_upperFaceLoop (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickShell.upperFaceLoop i = b.stickUpperFaceLoop i := by
  apply GenLoop.ext
  intro t
  rfl

/-- The specialized lower face loop agrees with the face supplied by the generic shell. -/
@[simp]
theorem stickShell_lowerFaceLoop (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickShell.lowerFaceLoop i = b.stickLowerFaceLoop i := by
  apply GenLoop.ext
  intro t
  rfl

/-- The upper cubical face loop is exactly the corresponding normalized simplex loop. -/
@[simp]
theorem stickUpperFaceLoop_eq (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickUpperFaceLoop i = (b.face i.castSucc).toStickGenLoop := by
  apply GenLoop.ext
  exact b.stickCubeMap_upper_face i

/-- The final lower cubical face loop is exactly the final normalized simplex loop. -/
@[simp]
theorem stickLowerFaceLoop_last (b : NormalizedSimplexBoundary n X x) :
    b.stickLowerFaceLoop (Fin.last (n + 2)) =
      (b.face (Fin.last (n + 3))).toStickGenLoop := by
  apply GenLoop.ext
  exact b.stickCubeMap_last_lower_face

/-- Every nonfinal lower cubical face is the constant generalized loop. -/
theorem stickLowerFaceLoop_eq_const (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) :
    b.stickLowerFaceLoop i = GenLoop.const := by
  apply GenLoop.ext
  exact b.stickCubeMap_lower_face i hi

/-- The homotopy class of an upper face of the stick-breaking cube, in additive notation. -/
noncomputable def stickUpperFaceClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) : Additive (π_ (n + 2) X x) :=
  Additive.ofMul (⟦b.stickUpperFaceLoop i⟧ : π_ (n + 2) X x)

/-- The homotopy class of a lower face of the stick-breaking cube, in additive notation. -/
noncomputable def stickLowerFaceClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) : Additive (π_ (n + 2) X x) :=
  Additive.ofMul (⟦b.stickLowerFaceLoop i⟧ : π_ (n + 2) X x)

@[simp]
theorem stickShell_upperFaceClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickShell.upperFaceClass i = b.stickUpperFaceClass i := by
  rw [CubicalShell.upperFaceClass, stickUpperFaceClass, stickShell_upperFaceLoop]

@[simp]
theorem stickShell_lowerFaceClass (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickShell.lowerFaceClass i = b.stickLowerFaceClass i := by
  rw [CubicalShell.lowerFaceClass, stickLowerFaceClass, stickShell_lowerFaceLoop]

@[simp]
theorem stickUpperFaceClass_eq (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) :
    b.stickUpperFaceClass i = Additive.ofMul (b.face i.castSucc).stickHomotopyClass := by
  rw [stickUpperFaceClass, stickUpperFaceLoop_eq]
  rfl

@[simp]
theorem stickLowerFaceClass_last (b : NormalizedSimplexBoundary n X x) :
    b.stickLowerFaceClass (Fin.last (n + 2)) =
      Additive.ofMul (b.face (Fin.last (n + 3))).stickHomotopyClass := by
  rw [stickLowerFaceClass, stickLowerFaceLoop_last]
  rfl

@[simp]
theorem stickLowerFaceClass_eq_zero (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 3)) (hi : i ≠ Fin.last (n + 2)) :
    b.stickLowerFaceClass i = 0 := by
  rw [stickLowerFaceClass, stickLowerFaceLoop_eq_const b i hi,
    ← HomotopyGroup.one_def]
  rfl

/-- The oriented sum of the upper and lower faces of the stick-breaking cube. -/
noncomputable def stickCubicalBoundaryClass (b : NormalizedSimplexBoundary n X x) :
    Additive (π_ (n + 2) X x) :=
  ∑ i : Fin (n + 3),
    (-1 : ℤ) ^ (i : ℕ) • (b.stickUpperFaceClass i - b.stickLowerFaceClass i)

/-- The specialized cubical boundary expression is the boundary class of the generic stick
shell. -/
@[simp]
theorem stickShell_boundaryClass (b : NormalizedSimplexBoundary n X x) :
    b.stickShell.boundaryClass = b.stickCubicalBoundaryClass := by
  rw [CubicalShell.boundaryClass, stickCubicalBoundaryClass]
  apply Finset.sum_congr rfl
  intro i hi
  rw [stickShell_upperFaceClass, stickShell_lowerFaceClass]

/-- The alternating sum of the normalized simplex faces in stick-breaking coordinates. -/
noncomputable def alternatingStickFaceClass (b : NormalizedSimplexBoundary n X x) :
    Additive (π_ (n + 2) X x) :=
  ∑ i : Fin (n + 4),
    (-1 : ℤ) ^ (i : ℕ) • Additive.ofMul (b.face i).stickHomotopyClass

/-- The cubical boundary orientation agrees with the alternating simplicial orientation. -/
theorem stickCubicalBoundaryClass_eq_alternatingStickFaceClass
    (b : NormalizedSimplexBoundary n X x) :
    b.stickCubicalBoundaryClass = b.alternatingStickFaceClass := by
  let f : Fin (n + 4) → Additive (π_ (n + 2) X x) := fun i ↦
    (-1 : ℤ) ^ (i : ℕ) • Additive.ofMul (b.face i).stickHomotopyClass
  have hupper :
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • b.stickUpperFaceClass i) =
        ∑ i : Fin (n + 3), f i.castSucc := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [f]
  have hlower :
      (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • b.stickLowerFaceClass i) =
        (-1 : ℤ) ^ (n + 2) •
          Additive.ofMul (b.face (Fin.last (n + 3))).stickHomotopyClass := by
    rw [Finset.sum_eq_single (Fin.last (n + 2))]
    · simp
    · intro i hi hne
      rw [b.stickLowerFaceClass_eq_zero i hne]
      simp
    · simp
  rw [stickCubicalBoundaryClass, alternatingStickFaceClass]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, hupper, hlower]
  change (∑ i : Fin (n + 3), f i.castSucc) -
      (-1 : ℤ) ^ (n + 2) •
        Additive.ofMul (b.face (Fin.last (n + 3))).stickHomotopyClass =
    ∑ i : Fin (n + 4), f i
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [f, Fin.val_last]
  rw [sub_eq_add_neg, ← neg_smul]
  simp [pow_succ]

end NormalizedSimplexBoundary

end Submission
