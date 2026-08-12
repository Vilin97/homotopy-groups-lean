/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.DeformationClass
import Submission.Hurewicz.SimplicialDescent
import Submission.Hurewicz.SimplicialRelationAt

/-!
# Relative descent of the normalized stick-class map

For a singleton point pair, the normalized stick-class chain map vanishes on chains supported at
the point.  It therefore factors through the relative chain complex.  Its annihilation of the
incoming differential descends as well, producing a map out of relative homology.  This relative
version evaluates directly on the explicit class of a normalized simplex and is compatible with
the absolute homology map through `relJ`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite
open scoped Topology Topology.Homotopy unitInterval

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X]

namespace IsNConnected

/-- The normalized stick-class chain map vanishes on singular chains of the singleton
basepoint. -/
theorem CsingMap_singleton_comp_normalizedStickClassChain
    (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingMap (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) ≫
      hX.normalizedStickClassChain x = 0 := by
  refine chainComplexX_hom_ext fun τ => ?_
  rw [ConcreteCategory.comp_apply, CsingMap_gen, normalizedStickClassChain_gen,
    zero_hom_apply]
  have hsimplex :
      hX.normalizeTopSimplex x
          ((sngIncl ({x} : Set X)).app _ τ) =
        NormalizedSimplex.const n x := by
    apply NormalizedSimplex.ext
    change (hX.pointDeformation x).ρ (n + 2)
        ((sngIncl ({x} : Set X)).app _ τ) =
      constSimplex (X := TopCat.of X) ((n + 1) + 1) x
    rw [(hX.pointDeformation x).ρ_fix τ, sngIncl_singleton_eq_const]
  change Additive.ofMul
      (hX.normalizeTopSimplex x
        ((sngIncl ({x} : Set X)).app _ τ)).stickHomotopyClass = 0
  rw [hsimplex, NormalizedSimplex.const_stickHomotopyClass]
  rfl

/-- The normalized stick-class map on relative chains in the first potentially nonzero
degree. -/
noncomputable def normalizedStickRelativeClassChain
    (hX : IsNConnected (n + 1) X) (x : X) :
    (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).X (n + 2) ⟶
      AddCommGrpCat.of (Additive (π_ (n + 2) X x)) :=
  cokDesc (CsingMap (subIncl (Y := TopCat.of X) ({x} : Set X))) (n + 2)
    (hX.normalizedStickClassChain x)
    (hX.CsingMap_singleton_comp_normalizedStickClassChain x)

/-- Projection to relative chains followed by the relative evaluator is the original absolute
chain evaluator. -/
theorem relProj_comp_normalizedStickRelativeClassChain
    (hX : IsNConnected (n + 1) X) (x : X) :
    (relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) ≫
      hX.normalizedStickRelativeClassChain x =
        hX.normalizedStickClassChain x := by
  exact π_cokDesc _ _ _ _

/-- The relative stick-class evaluator annihilates the incoming relative differential. -/
theorem normalizedStickRelativeClassChain_comp_d
    (hX : IsNConnected (n + 1) X) (x : X) :
    (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).d (n + 3) (n + 2) ≫
      hX.normalizedStickRelativeClassChain x = 0 := by
  letI : Epi
      ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 3)) := by
    change Epi
      ((cokernel.π (CsingMap (subIncl (Y := TopCat.of X) ({x} : Set X)))).f (n + 3))
    infer_instance
  have hzero :
      (Csing (TopCat.of X)).d (n + 3) (n + 2) ≫
        hX.normalizedStickClassChain x = 0 :=
    hX.normalizedStickClassChain_comp_d x
  apply (cancel_epi
    ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 3))).1
  rw [← Category.assoc,
    (relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).comm (n + 3) (n + 2),
    Category.assoc, hX.relProj_comp_normalizedStickRelativeClassChain x,
    hzero, comp_zero]

/-- The normalized stick-coordinate evaluator on singleton-pair relative homology. -/
noncomputable def normalizedStickRelativeHomologyMap
    (hX : IsNConnected (n + 1) X) (x : X) :
    HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) ⟶
      AddCommGrpCat.of (Additive (π_ (n + 2) X x)) :=
  homologyDesc (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))) (n + 2)
    (hX.normalizedStickRelativeClassChain x) (by
      rw [ChainComplex.prev ℕ (n + 2)]
      rw [show n + 2 + 1 = n + 3 by omega]
      exact hX.normalizedStickRelativeClassChain_comp_d x)

/-- Evaluation of the relative map on a relative cycle. -/
@[simp]
theorem normalizedStickRelativeHomologyMap_homologyMk
    (hX : IsNConnected (n + 1) X) (x : X)
    (a : (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).X (n + 2))
    (ha : (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).d (n + 2)
      ((ComplexShape.down ℕ).next (n + 2)) a = 0) :
    hX.normalizedStickRelativeHomologyMap x (homologyMk a ha) =
      hX.normalizedStickRelativeClassChain x a := by
  apply homologyDesc_homologyMk

/-- On the explicit relative class of a normalized simplex, the relative evaluator returns the
stick class of its coherently normalized image. -/
theorem normalizedStickRelativeHomologyMap_relativeClass
    (hX : IsNConnected (n + 1) X) (x : X)
    (s : NormalizedSimplex n X x) :
    hX.normalizedStickRelativeHomologyMap x s.relativeClass =
      Additive.ofMul
        (hX.normalizeTopSimplex x s.simplex).stickHomotopyClass := by
  unfold NormalizedSimplex.relativeClass relativeSimplexClass
  rw [hX.normalizedStickRelativeHomologyMap_homologyMk]
  change hX.normalizedStickRelativeClassChain x
      ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2)
        (gen s.simplex)) = _
  rw [← ConcreteCategory.comp_apply,
    hX.relProj_comp_normalizedStickRelativeClassChain x,
    normalizedStickClassChain_gen]
  rfl

/-- Equivalently, evaluation on a normalized simplex class is the injective sphere
reparameterization of its original cubical homotopy class. -/
theorem normalizedStickRelativeHomologyMap_relativeClass_eq_stickReparam
    (hX : IsNConnected (n + 1) X) (x : X)
    (s : NormalizedSimplex n X x) :
    hX.normalizedStickRelativeHomologyMap x s.relativeClass =
      Additive.ofMul (stickReparamClass (n + 1) s.homotopyClass) := by
  rw [hX.normalizedStickRelativeHomologyMap_relativeClass x s,
    s.normalizeTopSimplex_stickHomotopyClass hX]

/-- The relative evaluator after `relJ` agrees with the absolute evaluator. -/
theorem normalizedStickRelativeHomologyMap_relJ
    (hX : IsNConnected (n + 1) X) (x : X)
    (z : Hgrp (n + 2) (TopCat.of X)) :
    hX.normalizedStickRelativeHomologyMap x
        (relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X)) z) =
      hX.normalizedStickHomologyMap x z := by
  obtain ⟨a, ha, rfl⟩ := homologyMk_surjective z
  let ha' :
      (relComplex (subIncl (Y := TopCat.of X) ({x} : Set X))).d (n + 2)
          ((ComplexShape.down ℕ).next (n + 2))
          ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) a) = 0 := by
    rw [← ConcreteCategory.comp_apply,
      (relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).comm,
      ConcreteCategory.comp_apply, ha, map_zero]
  have hJ :
      relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X)) (homologyMk a ha) =
        homologyMk
          ((relProj (subIncl (Y := TopCat.of X) ({x} : Set X))).f (n + 2) a) ha' := by
    exact homologyMap_homologyMk
      (relProj (subIncl (Y := TopCat.of X) ({x} : Set X))) a ha ha'
  rw [hJ, hX.normalizedStickRelativeHomologyMap_homologyMk,
    ← ConcreteCategory.comp_apply,
    hX.relProj_comp_normalizedStickRelativeClassChain x,
    hX.normalizedStickHomologyMap_homologyMk]

end IsNConnected

end Submission
