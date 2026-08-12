/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.SimplicialAddition

/-!
# Simplicial homotopy relations in cubical coordinates

A final-index `RelStruct` between two pointed simplices is a higher simplex whose final two
faces are the given simplices and whose remaining faces are constant.  Under stick-breaking
coordinates, those two faces become the lower and upper facets in the final cube direction,
while every transverse facet is constant.  The one-pair cubical-shell relation therefore says
that the two pointed simplices determine the same maintained homotopy class.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

variable
  {f g : (Sng (TopCat.of X)).PtSimplex (n + 2)
    (TopCat.toSSetObj₀Equiv.symm x)}

/-! ### The normalized boundary of a final simplicial relation -/

/-- The pointed simplex carried by a face of a final-index relation simplex.  Its
penultimate face is `f`, its final face is `g`, and every earlier face is constant. -/
def lastRelFace
    (_r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2)))
    (j : Fin (n + 4)) :
    (Sng (TopCat.of X)).PtSimplex (n + 2)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  if j = (Fin.last (n + 2)).castSucc then f
  else if j = (Fin.last (n + 2)).succ then g
  else .const

/-- The selected pointed face has the same map as the corresponding face of the relation
simplex. -/
theorem lastRelFace_map
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2)))
    (j : Fin (n + 4)) :
    (lastRelFace r j).map = SSet.stdSimplex.δ j ≫ r.map := by
  simp only [lastRelFace]
  split
  next h =>
    subst j
    exact r.δ_castSucc_map.symm
  next hpenultimate =>
    split
    next h =>
      subst j
      exact r.δ_succ_map.symm
    next hfinal =>
      have hj : j < (Fin.last (n + 2)).castSucc := by grind
      exact (r.δ_map_of_lt j hj).symm

/-- A final-index relation simplex and all its pointed faces, packaged as a normalized simplex
boundary. -/
def lastRelBoundary
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    NormalizedSimplexBoundary n X x where
  simplex := SSet.yonedaEquiv r.map
  face j := NormalizedSimplex.ofPtSimplex (lastRelFace r j)
  face_simplex j := by
    rw [NormalizedSimplex.ofPtSimplex_simplex, lastRelFace_map]
    exact (yonedaEquiv_comp_δ (X := X) (q := n + 2) j r.map).symm

@[simp]
theorem lastRelBoundary_simplex
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    (lastRelBoundary r).simplex = SSet.yonedaEquiv r.map :=
  rfl

@[simp]
theorem lastRelBoundary_face_penultimate
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    (lastRelBoundary r).face (Fin.last (n + 2)).castSucc =
      NormalizedSimplex.ofPtSimplex f := by
  simp [lastRelBoundary, lastRelFace]

@[simp]
theorem lastRelBoundary_face_final
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    (lastRelBoundary r).face (Fin.last (n + 3)) =
      NormalizedSimplex.ofPtSimplex g := by
  have hpenultimate :
      (Fin.last (n + 3) : Fin (n + 4)) ≠ (Fin.last (n + 2)).castSucc := by grind
  rw [show Fin.last (n + 3) = (Fin.last (n + 2)).succ by ext; simp]
  simp [lastRelBoundary, lastRelFace, hpenultimate]

/-- Every face before the final two faces of a final relation simplex is the constant
normalized simplex. -/
theorem lastRelBoundary_face_of_lt
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2)))
    (j : Fin (n + 4))
    (hj : j < (Fin.last (n + 2)).castSucc) :
    (lastRelBoundary r).face j = NormalizedSimplex.const n x := by
  have hpenultimate : j ≠ (Fin.last (n + 2)).castSucc := ne_of_lt hj
  have hfinal : j ≠ (Fin.last (n + 3) : Fin (n + 4)) := by grind
  simp [lastRelBoundary, lastRelFace, hpenultimate, hfinal]

/-- The stick-breaking shell of a final-index relation has constant facets transverse to its
final coordinate. -/
theorem lastRelBoundary_stickShell_transverseFacesConstant
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    (lastRelBoundary r).stickShell.TransverseFacesConstant (Fin.last (n + 2)) := by
  intro j hj
  constructor
  · exact (lastRelBoundary r).stickShell_lowerFace_isConstant j hj
  · intro t ht
    let u : I^Fin (n + 2) := Fin.removeNth j t
    have hrep : t = cubeFace j 1 u := by
      change t = j.insertNth 1 u
      rw [← ht]
      exact (Fin.insertNth_self_removeNth j t).symm
    rw [hrep]
    change (lastRelBoundary r).stickCubeMap (cubeFace j 1 u) = x
    rw [(lastRelBoundary r).stickCubeMap_upper_face j]
    have hj' : j.castSucc < (Fin.last (n + 2)).castSucc := by grind
    rw [lastRelBoundary_face_of_lt r j.castSucc hj',
      NormalizedSimplex.const_stickMap_apply]

/-! ### Invariance of the maintained homotopy class -/

/-- A final-index simplicial relation preserves the stick-breaking cubical homotopy class. -/
theorem stickHomotopyClass_ofPtSimplex_rel
    (r : SSet.PtSimplex.RelStruct f g (Fin.last (n + 2))) :
    (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass =
      (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass := by
  have hrel := CubicalShell.lowerFaceClass_eq_upperFaceClass
    (lastRelBoundary r).stickShell (Fin.last (n + 2))
      (lastRelBoundary_stickShell_transverseFacesConstant r)
  have hrel' :
      Additive.ofMul (NormalizedSimplex.ofPtSimplex g).stickHomotopyClass =
        Additive.ofMul (NormalizedSimplex.ofPtSimplex f).stickHomotopyClass := by
    simpa using hrel
  exact congrArg Additive.toMul hrel'.symm

end Submission
