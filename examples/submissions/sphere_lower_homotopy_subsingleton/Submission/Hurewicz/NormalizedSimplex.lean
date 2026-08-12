/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.HomotopyLesTools
import Submission.Hurewicz.DegreeOne.Affine
import Submission.Hurewicz.SimplexHEP
import Submission.Hurewicz.VanishingSorries
import Submission.SphereGenerator

/-!
# Normalized singular simplices in the first nonvanishing degree

Apply the bounded coherent simplex deformation to the point pair `(X, {x})`.  If `X` is
`(n+1)`-connected, the deformation sends every singular simplex through dimension `n+1` to the
point.  Consequently every face of the deformed `(n+2)`-simplices is the constant simplex at
`x`.  Such a simplex is constant on its whole boundary, so a simplex--disk--cube
reparametrisation turns it into a based cubical `(n+2)`-loop.

This is the geometric generator assignment used in the chain-level inverse in the
first-nonvanishing Hurewicz theorem.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The homeomorphism from the `d`-cube to the standard `d`-simplex obtained through the disk. -/
noncomputable def cubeHomeoSimplex (d : ℕ) :
    (I^Fin d) ≃ₜ stdSimplex ℝ (Fin (d + 1)) :=
  ((simplexHomeoDisk' d).trans (TopCat.diskHomeoCube.{0} d)).symm

/-- The cube--simplex homeomorphism carries the cube boundary to the simplex boundary. -/
theorem cubeHomeoSimplex_mem_bdry (d : ℕ) (y : I^Fin d) (hy : y ∈ ∂I^d) :
    cubeHomeoSimplex d y ∈ bdry d := by
  rw [mem_bdry, ← norm_simplexHomeoBall_eq_one_iff]
  change ‖((simplexHomeoDisk' d (cubeHomeoSimplex d y)).down.val :
    EuclideanSpace ℝ (Fin d))‖ = 1
  rw [show simplexHomeoDisk' d (cubeHomeoSimplex d y) =
    (TopCat.diskHomeoCube.{0} d).symm y by simp [cubeHomeoSimplex]]
  exact norm_diskHomeoCube_symm_eq_one_of_mem_boundary d y hy

/-- A singular `(n+2)`-simplex all of whose faces are the constant simplex at the basepoint. -/
structure NormalizedSimplex (n : ℕ) (X : Type) [TopologicalSpace X] (x : X) where
  /-- The underlying singular simplex. -/
  simplex : Sng (TopCat.of X) _⦋(n + 1) + 1⦌
  /-- Every codimension-one face is constant at the basepoint. -/
  face_eq (i : Fin ((n + 1) + 2)) :
    (Sng (TopCat.of X)).δ i simplex =
      constSimplex (X := TopCat.of X) (n + 1) x

namespace NormalizedSimplex

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- The map on the cube obtained by reparametrising a normalized singular simplex. -/
noncomputable def cubeMap (s : NormalizedSimplex n X x) : C(I^Fin (n + 2), X) :=
  (sngEquiv (TopCat.of X) (n + 2) s.simplex).comp
    ⟨cubeHomeoSimplex (n + 2), (cubeHomeoSimplex (n + 2)).continuous⟩

/-- A normalized singular simplex is constant on the entire boundary of its simplex. -/
theorem simplex_boundary (s : NormalizedSimplex n X x)
    (z : stdSimplex ℝ (Fin (n + 3))) (hz : z ∈ bdry (n + 2)) :
    sngEquiv (TopCat.of X) (n + 2) s.simplex z = x := by
  refine bdry_induction (j := n + 1) (P := fun z =>
    sngEquiv (TopCat.of X) (n + 2) s.simplex z = x) ?_ hz
  intro i y
  rw [← apply_δ, s.face_eq, constSimplex, sngEquiv_sng]
  rfl

/-- The cubical reparametrisation of a normalized simplex is constant on the cube boundary. -/
theorem cubeMap_boundary (s : NormalizedSimplex n X x) (y : I^Fin (n + 2))
    (hy : y ∈ ∂I^(n + 2)) : cubeMap s y = x :=
  s.simplex_boundary (cubeHomeoSimplex (n + 2) y)
    (cubeHomeoSimplex_mem_bdry (n + 2) y hy)

/-- A normalized singular simplex, regarded as a based cubical loop. -/
noncomputable def toGenLoop (s : NormalizedSimplex n X x) : Ω^ (Fin (n + 2)) X x :=
  ⟨cubeMap s, s.cubeMap_boundary⟩

/-- The homotopy class represented by a normalized singular simplex. -/
noncomputable def homotopyClass (s : NormalizedSimplex n X x) : π_ (n + 2) X x :=
  ⟦s.toGenLoop⟧

end NormalizedSimplex

/-- A singular simplex in a singleton subspace becomes the constant singular simplex after
inclusion into the ambient space. -/
theorem sngIncl_singleton_eq_const {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (s : Sng (TopCat.of ({x} : Set X)) _⦋m⦌) :
    (sngIncl ({x} : Set X)).app _ s = constSimplex (X := TopCat.of X) m x := by
  refine sng_ext fun y => ?_
  rw [sngEquiv_incl]
  have hy : (sngEquiv (TopCat.of ({x} : Set X)) m s y).val = x :=
    Set.mem_singleton_iff.mp (sngEquiv (TopCat.of ({x} : Set X)) m s y).property
  rw [constSimplex, sngEquiv_sng]
  exact hy

namespace SimplicialDeformation

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}

/-- The first layer above the compression range consists of normalized simplices for a point
pair: all faces of the deformed `(n+2)`-simplex are constant at the chosen point. -/
noncomputable def normalizedTopSimplex
    (c : SimplicialDeformation (TopCat.of X) ({x} : Set X) (n + 1))
    (s : Sng (TopCat.of X) _⦋n + 2⦌) : NormalizedSimplex n X x where
  simplex := c.ρ (n + 2) s
  face_eq i := by
    rw [← c.ρ_δ i s]
    obtain ⟨t, ht⟩ := c.ρ_mem (n := n + 1) (by omega) ((Sng (TopCat.of X)).δ i s)
    rw [← ht]
    exact sngIncl_singleton_eq_const t

end SimplicialDeformation

namespace IsNConnected

variable {M n : ℕ} {X : Type} [TopologicalSpace X]

/-- The coherent bounded simplex deformation of the point pair supplied by connectivity. -/
noncomputable def pointDeformation (hX : IsNConnected M X) (x : X) :
    SimplicialDeformation (TopCat.of X) ({x} : Set X) M := by
  let hPair := hX.singletonPair x
  exact (exists_simplicialDeformation M (TopCat.of X) ({x} : Set X) ⟨x, rfl⟩
    hPair.surjective_iStar_zero
    (fun k hk a => hPair.unique_piRel k (by omega) a)).some

/-- The normalized `(n+2)`-simplex obtained from a singular simplex in an `(n+1)`-connected
space. -/
noncomputable def normalizeTopSimplex (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) : NormalizedSimplex n X x :=
  (hX.pointDeformation x).normalizedTopSimplex s

/-- The based homotopy class carried by the normalized form of a top-dimensional singular
simplex. -/
noncomputable def normalizedSimplexClass (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) : π_ (n + 2) X x :=
  (hX.normalizeTopSimplex x s).homotopyClass

/-- The additive map on top-dimensional singular chains obtained by sending each generator to
the homotopy class of its normalized simplex. -/
noncomputable def normalizedClassChain (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).X (n + 2) ⟶
      AddCommGrpCat.of (Additive (π_ (n + 2) X x)) :=
  ccDesc fun s => intHom (Additive.ofMul (hX.normalizedSimplexClass x s))

@[simp]
theorem normalizedClassChain_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    hX.normalizedClassChain x (gen s) =
      Additive.ofMul (hX.normalizedSimplexClass x s) := by
  rw [normalizedClassChain, ccDesc_gen, intHom_one]
  rfl

end IsNConnected

end Submission
