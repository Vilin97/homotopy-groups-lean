/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.UCT.HomologyClass
import Submission.Hurewicz.SimplicialTelescope

/-!
# Descent of the simplicial homotopy-class map to homology

The simplicial homotopy-addition theorem says exactly that the stick-coordinate homotopy class
assigned to a normalized singular simplex annihilates incoming boundaries.  Consequently the
assignment descends from chains to the first potentially nonzero singular homology group.

This file constructs that descended homomorphism and records its value on every cycle.  It is a
stick-coordinate version of the inverse map in the first-nonvanishing Hurewicz theorem; comparing
it with the cube-coordinate representative used by the relative Hurewicz construction remains a
separate geometric change-of-coordinates statement.
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

variable {n : ℕ} {X : Type} [TopologicalSpace X]

namespace IsNConnected

/-- The stick-coordinate homotopy class of the normalized form of a singular simplex. -/
noncomputable def normalizedStickSimplexClass (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) : π_ (n + 2) X x :=
  (hX.normalizeTopSimplex x s).stickHomotopyClass

/-- The additive map on singular `(n+2)`-chains obtained from normalized stick-coordinate
homotopy classes. -/
noncomputable def normalizedStickClassChain (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).X (n + 2) ⟶
      AddCommGrpCat.of (Additive (π_ (n + 2) X x)) :=
  ccDesc fun s => intHom (Additive.ofMul (hX.normalizedStickSimplexClass x s))

@[simp]
theorem normalizedStickClassChain_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    hX.normalizedStickClassChain x (gen s) =
      Additive.ofMul (hX.normalizedStickSimplexClass x s) := by
  rw [normalizedStickClassChain, ccDesc_gen, intHom_one]
  rfl

/-- On a singular `(n+3)`-simplex generator, the stick-coordinate class map sends its boundary
to the alternating homotopy class of the coherently normalized faces. -/
theorem normalizedStickClassChain_boundary_gen (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 3⦌) :
    hX.normalizedStickClassChain x
        ((CsingSSet (Sng (TopCat.of X))).d (n + 3) (n + 2) (gen s)) =
      (hX.normalizeBoundary x s).alternatingStickFaceClass := by
  rw [d_gen, map_sum, NormalizedSimplexBoundary.alternatingStickFaceClass]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, normalizedStickClassChain_gen]
  rfl

/-- **Simplicial homotopy addition in chain form.**  The normalized stick-coordinate class map
annihilates the incoming singular differential. -/
theorem normalizedStickClassChain_comp_d (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).d (n + 3) (n + 2) ≫
      hX.normalizedStickClassChain x = 0 := by
  refine chainComplexX_hom_ext fun s ↦ ?_
  rw [ConcreteCategory.comp_apply, zero_hom_apply,
    hX.normalizedStickClassChain_boundary_gen x s,
    NormalizedSimplexBoundary.alternatingStickFaceClass_eq_zero]

/-- The stick-coordinate inverse candidate on the first potentially nonzero singular homology
group.  Its well-definedness is precisely the simplicial homotopy-addition theorem. -/
noncomputable def normalizedStickHomologyMap (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).homology (n + 2) ⟶
      AddCommGrpCat.of (Additive (π_ (n + 2) X x)) :=
  homologyDesc (CsingSSet (Sng (TopCat.of X))) (n + 2)
    (hX.normalizedStickClassChain x) (by
      rw [ChainComplex.prev ℕ (n + 2)]
      rw [show n + 2 + 1 = n + 3 by omega]
      exact hX.normalizedStickClassChain_comp_d x)

/-- The descended map sends the homology class of a cycle to the stick-coordinate class assigned
to that cycle before passage to the quotient. -/
@[simp]
theorem normalizedStickHomologyMap_homologyMk (hX : IsNConnected (n + 1) X) (x : X)
    (a : (CsingSSet (Sng (TopCat.of X))).X (n + 2))
    (ha : (CsingSSet (Sng (TopCat.of X))).d (n + 2)
      ((ComplexShape.down ℕ).next (n + 2)) a = 0) :
    hX.normalizedStickHomologyMap x (homologyMk a ha) =
      hX.normalizedStickClassChain x a := by
  apply homologyDesc_homologyMk

end IsNConnected

end Submission
