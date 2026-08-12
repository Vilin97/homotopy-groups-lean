/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.NormalizedSimplex
import Submission.Hurewicz.SphereLoopBridge
import Submission.Hurewicz.StickSimplex

/-!
# Boundaries of normalized singular simplices

A coherent deformation of an `(n+3)`-simplex has `(n+2)`-dimensional faces which are normalized
at the chosen basepoint.  This file packages the higher simplex together with those normalized
faces and identifies the image of its singular boundary under `normalizedClassChain` with the
alternating sum of their cubical homotopy classes.

The resulting equivalence
`Submission.IsNConnected.normalizedClassChain_comp_d_eq_zero_iff` isolates the remaining
geometric input in the first-nonvanishing Hurewicz inverse: the chain map annihilates singular
boundaries exactly when every normalized simplex boundary has trivial alternating face class.
The sphere-map bridge makes each term available as a based map `S^(n+2) ⟶ X`, so the missing
statement is now purely the topological attaching relation for the boundary of one simplex.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not.
attribute [local implicit_reducible] AlgebraicTopology.alternatingFaceMapComplex
  AlgebraicTopology.AlternatingFaceMapComplex.obj SSet.chainComplexFunctor
  AlgebraicTopology.singularChainComplexFunctor CategoryTheory.Functor.postcompose₂
  CategoryTheory.SimplicialObject.whiskering CategoryTheory.Functor.whiskeringLeft
  CategoryTheory.Functor.comp

noncomputable section

namespace Submission

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

namespace NormalizedSimplex

/-- The based sphere map represented by a normalized simplex. -/
noncomputable def toBasedSphereMap (s : NormalizedSimplex n X x) :
    BasedSphereMap (n + 2) X x :=
  targetGenLoopBasedSphereMap (n + 1) s.toGenLoop

@[simp]
theorem toBasedSphereMap_val (s : NormalizedSimplex n X x) :
    s.toBasedSphereMap.1 = targetGenLoopSphereMap (n + 1) s.toGenLoop :=
  rfl

/-- Taking the cubical class of the based sphere map associated to a normalized simplex recovers
its original homotopy class. -/
@[simp]
theorem sphereTargetMapClass_toBasedSphereMap (s : NormalizedSimplex n X x) :
    sphereTargetMapClass (n + 2) s.toBasedSphereMap.1 s.toBasedSphereMap.2 = s.homotopyClass := by
  exact sphereTargetMapClass_targetGenLoopSphereMap (n + 1) s.toGenLoop

end NormalizedSimplex

/-- A normalized boundary consists of one singular `(n+3)`-simplex and normalized structures on
all of its `(n+2)`-dimensional faces.  Keeping the face structures as data avoids repeatedly
transporting their boundary proofs across proof-irrelevant equalities. -/
structure NormalizedSimplexBoundary (n : ℕ) (X : Type) [TopologicalSpace X] (x : X) where
  /-- The higher singular simplex whose faces are being assembled. -/
  simplex : Sng (TopCat.of X) _⦋n + 3⦌
  /-- Its normalized codimension-one faces. -/
  face (i : Fin (n + 4)) : NormalizedSimplex n X x
  /-- The underlying simplex of each normalized face is the corresponding simplicial face. -/
  face_simplex (i : Fin (n + 4)) :
    (face i).simplex = (Sng (TopCat.of X)).δ i simplex

namespace NormalizedSimplexBoundary

/-- A canonical codimension-two point of the boundary of the `(n+3)`-simplex.  It is obtained by
inserting two zero coordinates into a vertex. -/
def boundaryBasepoint (n : ℕ) : bdry (n + 3) :=
  ⟨faceMap (0 : Fin (n + 4))
      (faceMap (0 : Fin (n + 3)) (stdSimplex.vertex (0 : Fin (n + 2)))),
    faceMap_mem_bdry _ _⟩

@[simp]
theorem boundaryBasepoint_val (n : ℕ) :
    ((boundaryBasepoint n : bdry (n + 3)) : stdSimplex ℝ (Fin (n + 4))) =
      faceMap (0 : Fin (n + 4))
        (faceMap (0 : Fin (n + 3)) (stdSimplex.vertex (0 : Fin (n + 2)))) :=
  rfl

/-- Every codimension-two face of a normalized simplex boundary is constant at the basepoint. -/
theorem face_face_eq (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4))
    (j : Fin ((n + 1) + 2)) :
    (Sng (TopCat.of X)).δ j ((Sng (TopCat.of X)).δ i b.simplex) =
      constSimplex (X := TopCat.of X) (n + 1) x := by
  rw [← b.face_simplex i]
  exact (b.face i).face_eq j

/-- The higher simplex is constant at the basepoint on its entire codimension-two skeleton. -/
theorem simplex_eq_of_mem_codimTwo (b : NormalizedSimplexBoundary n X x)
    (z : stdSimplex ℝ (Fin (n + 4))) (hz : z ∈ simplexCodimTwo (n + 3)) :
    sngEquiv (TopCat.of X) (n + 3) b.simplex z = x := by
  obtain ⟨i, k, hik, hi, hk⟩ := hz
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hik.symm
  let w : stdSimplex ℝ (Fin (n + 3)) := dropMap i hi
  have hw : w j = 0 := by
    change z (i.succAbove j) = 0
    rw [hj]
    exact hk
  let y : stdSimplex ℝ (Fin (n + 2)) := dropMap j hw
  have hwy : faceMap j y = w := faceMap_dropMap j hw
  have hzw : faceMap i w = z := faceMap_dropMap i hi
  change sngEquiv (TopCat.of X) (n + 3) b.simplex z = x
  rw [← hzw, ← hwy, ← apply_δ, ← apply_δ, b.face_face_eq,
    constSimplex, sngEquiv_sng]
  rfl

/-- The higher simplex takes the canonical codimension-two boundary point to the chosen
basepoint. -/
@[simp]
theorem simplex_boundaryBasepoint (b : NormalizedSimplexBoundary n X x) :
    sngEquiv (TopCat.of X) (n + 3) b.simplex (boundaryBasepoint n) = x := by
  change sngEquiv (TopCat.of X) (n + 3) b.simplex
    (faceMap (0 : Fin (n + 4))
      (faceMap (0 : Fin (n + 3)) (stdSimplex.vertex (0 : Fin (n + 2))))) = x
  rw [← apply_δ, ← apply_δ, b.face_face_eq, constSimplex, sngEquiv_sng]
  rfl

/-- The affine contraction of a point of a standard simplex to a chosen centre. -/
def simplexCone {d : ℕ} (v z : stdSimplex ℝ (Fin (d + 1))) (t : I) :
    stdSimplex ℝ (Fin (d + 1)) :=
  ⟨AffineMap.lineMap z.1 v.1 (t : ℝ),
    (convex_stdSimplex ℝ (Fin (d + 1))).lineMap_mem z.2 v.2 t.2⟩

/-- The affine simplex contraction is jointly continuous in time and the moving point. -/
theorem continuous_simplexCone {d : ℕ} (v : stdSimplex ℝ (Fin (d + 1))) :
    Continuous (fun p : I × stdSimplex ℝ (Fin (d + 1)) ↦ simplexCone v p.2 p.1) := by
  refine Continuous.subtype_mk ?_ _
  fun_prop

@[simp]
theorem simplexCone_zero {d : ℕ} (v z : stdSimplex ℝ (Fin (d + 1))) :
    simplexCone v z 0 = z := by
  apply Subtype.ext
  simp [simplexCone, AffineMap.lineMap_apply]

@[simp]
theorem simplexCone_one {d : ℕ} (v z : stdSimplex ℝ (Fin (d + 1))) :
    simplexCone v z 1 = v := by
  apply Subtype.ext
  simp [simplexCone, AffineMap.lineMap_apply]

@[simp]
theorem simplexCone_self {d : ℕ} (v : stdSimplex ℝ (Fin (d + 1))) (t : I) :
    simplexCone v v t = v := by
  apply Subtype.ext
  simp [simplexCone]

/-- Cone the simplex boundary to its canonical codimension-two basepoint. -/
def boundaryCone (n : ℕ) :
    C(I × bdry (n + 3), stdSimplex ℝ (Fin (n + 4))) where
  toFun p := simplexCone (boundaryBasepoint n) p.2.1 p.1
  continuous_toFun := by
    have hb : Continuous (fun p : I × bdry (n + 3) ↦
        (p.2.1 : stdSimplex ℝ (Fin (n + 4)))) :=
      continuous_subtype_val.comp continuous_snd
    exact (continuous_simplexCone (d := n + 3)
      ((boundaryBasepoint n).1 : stdSimplex ℝ (Fin (n + 4)))).comp
        (continuous_fst.prodMk hb)

@[simp]
theorem boundaryCone_apply (n : ℕ) (p : I × bdry (n + 3)) :
    boundaryCone n p = simplexCone (boundaryBasepoint n) p.2.1 p.1 :=
  rfl

/-- Restriction of the higher simplex to its topological boundary. -/
noncomputable def boundaryMap (b : NormalizedSimplexBoundary n X x) :
    C(bdry (n + 3), X) :=
  (sngEquiv (TopCat.of X) (n + 3) b.simplex).comp (bdryIncl (n + 3))

@[simp]
theorem boundaryMap_apply (b : NormalizedSimplexBoundary n X x) (z : bdry (n + 3)) :
    b.boundaryMap z = sngEquiv (TopCat.of X) (n + 3) b.simplex z :=
  rfl

@[simp]
theorem boundaryMap_basepoint (b : NormalizedSimplexBoundary n X x) :
    b.boundaryMap (boundaryBasepoint n) = x :=
  b.simplex_boundaryBasepoint

/-- The boundary restriction is nullhomotopic through the higher simplex, by coning the whole
simplex boundary to the canonical codimension-two point. -/
noncomputable def boundaryNullhomotopy (b : NormalizedSimplexBoundary n X x) :
    ContinuousMap.Homotopy b.boundaryMap (ContinuousMap.const (bdry (n + 3)) x) where
  toContinuousMap := (sngEquiv (TopCat.of X) (n + 3) b.simplex).comp (boundaryCone n)
  map_zero_left z := by
    change sngEquiv (TopCat.of X) (n + 3) b.simplex
      (simplexCone (boundaryBasepoint n) z.1 0) = b.boundaryMap z
    rw [simplexCone_zero]
    rfl
  map_one_left z := by
    change sngEquiv (TopCat.of X) (n + 3) b.simplex
      (simplexCone (boundaryBasepoint n) z.1 1) = x
    rw [simplexCone_one, b.simplex_boundaryBasepoint]

/-- The canonical nullhomotopy fixes the chosen boundary basepoint at every time. -/
@[simp]
theorem boundaryNullhomotopy_basepoint (b : NormalizedSimplexBoundary n X x) (t : I) :
    b.boundaryNullhomotopy (t, boundaryBasepoint n) = x := by
  change sngEquiv (TopCat.of X) (n + 3) b.simplex
    (simplexCone (boundaryBasepoint n) (boundaryBasepoint n) t) = x
  rw [simplexCone_self, b.simplex_boundaryBasepoint]

/-- The alternating additive sum of the homotopy classes carried by the faces of a normalized
simplex boundary. -/
noncomputable def alternatingFaceClass (b : NormalizedSimplexBoundary n X x) :
    Additive (π_ (n + 2) X x) :=
  ∑ i : Fin (n + 4), (-1 : ℤ) ^ (i : ℕ) • Additive.ofMul (b.face i).homotopyClass

/-- The sphere-map form of a face occurring in a normalized boundary. -/
noncomputable def faceSphereMap (b : NormalizedSimplexBoundary n X x) (i : Fin (n + 4)) :
    BasedSphereMap (n + 2) X x :=
  (b.face i).toBasedSphereMap

@[simp]
theorem sphereTargetMapClass_faceSphereMap (b : NormalizedSimplexBoundary n X x)
    (i : Fin (n + 4)) :
    sphereTargetMapClass (n + 2) (b.faceSphereMap i).1 (b.faceSphereMap i).2 =
      (b.face i).homotopyClass :=
  NormalizedSimplex.sphereTargetMapClass_toBasedSphereMap (b.face i)

end NormalizedSimplexBoundary

namespace SimplicialDeformation

/-- The normalized boundary supplied by applying a coherent point-pair deformation to an
`(n+3)`-simplex. -/
noncomputable def normalizedBoundary
    (c : SimplicialDeformation (TopCat.of X) ({x} : Set X) (n + 1))
    (s : Sng (TopCat.of X) _⦋n + 3⦌) : NormalizedSimplexBoundary n X x where
  simplex := c.ρ (n + 3) s
  face i := c.normalizedTopSimplex ((Sng (TopCat.of X)).δ i s)
  face_simplex i := c.ρ_δ i s

end SimplicialDeformation

namespace IsNConnected

/-- The normalized boundary of a singular `(n+3)`-simplex in an `(n+1)`-connected space. -/
noncomputable def normalizeBoundary (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 3⦌) : NormalizedSimplexBoundary n X x :=
  (hX.pointDeformation x).normalizedBoundary s

@[simp]
theorem normalizeBoundary_face (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 3⦌) (i : Fin (n + 4)) :
    (hX.normalizeBoundary x s).face i =
      hX.normalizeTopSimplex x ((Sng (TopCat.of X)).δ i s) :=
  rfl

/-- On a singular `(n+3)`-simplex generator, applying `normalizedClassChain` to the boundary is
exactly the alternating class of its coherently normalized faces. -/
theorem normalizedClassChain_boundary_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 3⦌) :
    hX.normalizedClassChain x
        ((CsingSSet (Sng (TopCat.of X))).d (n + 3) (n + 2) (gen s)) =
      (hX.normalizeBoundary x s).alternatingFaceClass := by
  rw [d_gen, map_sum, NormalizedSimplexBoundary.alternatingFaceClass]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, normalizedClassChain_gen]
  rfl

/-- `normalizedClassChain` annihilates the incoming differential exactly when the alternating
face class of every coherently normalized higher simplex vanishes. -/
theorem normalizedClassChain_comp_d_eq_zero_iff
    (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).d (n + 3) (n + 2) ≫ hX.normalizedClassChain x = 0 ↔
      ∀ s : Sng (TopCat.of X) _⦋n + 3⦌,
        (hX.normalizeBoundary x s).alternatingFaceClass = 0 := by
  constructor
  · intro h s
    rw [← hX.normalizedClassChain_boundary_gen x s,
      ← ConcreteCategory.comp_apply, h, zero_hom_apply]
  · intro h
    refine chainComplexX_hom_ext fun s ↦ ?_
    rw [ConcreteCategory.comp_apply, zero_hom_apply,
      hX.normalizedClassChain_boundary_gen x s, h s]

end IsNConnected

end Submission
