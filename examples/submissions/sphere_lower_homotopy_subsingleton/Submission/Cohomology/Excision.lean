/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Pair
import Submission.Homology.Excision

/-!
# Excision for relative singular cohomology

Dualizing the relative small-chain comparison gives cohomological excision in positive degrees.
The proof uses the long exact sequences of the two relative short complexes: the ambient
small-chain inclusion is a chain-homotopy equivalence, while the subspace map is the identity.
The left-hand form of the five lemma then makes the relative dual map an isomorphism.

## Main results

* `Submission.mvSmallRelCohSC_shortExact` -- the dual relative small-chain sequence is short
  exact;
* `Submission.isIso_homologyMap_homDual_mvSmallRelMap` -- relative small cochains compute
  relative cohomology in positive degrees;
* `Submission.isIso_mvExcisionHrelCohMap` -- cohomological excision for a two-set cover.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X)

/-- The degreewise retraction of the inclusion of `B`-chains into `{A,B}`-small chains. -/
def mvSmallRelRetr (n : ℕ) : (mvSmallComplex A B).X n ⟶ (Csing (TopCat.of B)).X n :=
  mvRetr (mvPb A B) n

@[reassoc]
theorem mvPbChainMap_comp_mvSmallRelRetr (n : ℕ) :
    (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)).f n ≫
      mvSmallRelRetr A B n = 𝟙 ((Csing (TopCat.of B)).X n) := by
  change (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)).f n ≫
      mvRetr (mvPb A B) n =
    𝟙 ((CsingSSet (TopCat.toSSet.obj (TopCat.of B))).X n)
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  rw [SSet.ι_chainComplexMap_f_assoc,
    ι_mvRetr (mvPb A B) (injective_mvPb_app A B n), Category.comp_id]

/-- The relative small-chain sequence is split in every degree. -/
def mvSmallRelDegreeSplitting (n : ℕ) : ShortComplex.Splitting
    ((mvSmallRelShortComplex A B).map
      (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n)) := by
  let h := ((HomologicalComplex.shortExact_iff_degreewise_shortExact
    (mvSmallRelShortComplex A B)).1 (mvSmallRelShortComplex_shortExact A B) n)
  exact ShortComplex.Splitting.ofExactOfRetraction _ h.exact (mvSmallRelRetr A B n)
    (mvPbChainMap_comp_mvSmallRelRetr A B n) h.epi_g

variable (G : AddCommGrpCat.{0})

/-- The dual relative short complex formed from small chains. -/
abbrev mvSmallRelCohSC :
    ShortComplex (HomologicalComplex AddCommGrpCat.{0} (ComplexShape.down ℕ).symm) :=
  homDualShortComplex (mvSmallRelShortComplex A B) G

/-- The dual relative small-chain sequence is short exact. -/
theorem mvSmallRelCohSC_shortExact : (mvSmallRelCohSC A B G).ShortExact :=
  homDualShortComplex_shortExact (mvSmallRelShortComplex A B) G
    (mvSmallRelDegreeSplitting A B)

/-- Inclusion of relative small chains, dualized to a morphism from full relative cochains to
relative small cochains. -/
def mvSmallRelCohShortComplexMap :
    homDualShortComplex (relShortComplex (subIncl B)) G ⟶ mvSmallRelCohSC A B G :=
  homDualShortComplexMap (mvSmallRelShortComplexMap A B) G

/-- Relative small cochains compute relative cohomology in every positive degree. -/
theorem isIso_homologyMap_homDual_mvSmallRelMap
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (homDualMap (mvSmallRelMap A B) G) (n + 1)) := by
  letI : QuasiIso (mvSmallRelCohShortComplexMap A B G).τ₂ := by
    change QuasiIso (homDualMap (mvSmallIncl A B) G)
    exact (homDualHomotopyEquiv (mvSmallHomotopyEquiv A B h) G).quasiIso_hom
  letI : QuasiIso (mvSmallRelCohShortComplexMap A B G).τ₃ := by
    change QuasiIso (homDualMap (𝟙 (Csing (TopCat.of B))) G)
    rw [homDualMap_id]
    infer_instance
  have hi := isIso_homologyMap_τ₁_of_rel
    (mvSmallRelCohShortComplexMap A B G)
    (relCohSC_shortExact (subIncl B) G)
    (mvSmallRelCohSC_shortExact A B G) n (n + 1) (by rfl)
  change IsIso (HomologicalComplex.homologyMap
    (homDualMap (mvSmallRelMap A B) G) (n + 1)) at hi
  exact hi

/-- The contravariant map on relative dual-complex cohomology induced by the excision inclusion
`(A, A ∩ B) → (X,B)`. -/
def mvExcisionHrelCohMap (n : ℕ) :
    HrelCoh (subIncl B) G n ⟶ HrelCoh (mvInclLeft A B) G n :=
  HomologicalComplex.homologyMap
    (homDualMap
      (relComplexMap (mvInclLeft A B) (subIncl B)
        (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl)) G) n

/-- **Excision for relative singular cohomology in positive degrees.** If the interiors of `A`
and `B` cover `X`, pullback identifies `Hⁿ⁺¹(X,B;G)` with `Hⁿ⁺¹(A,A∩B;G)`. -/
theorem isIso_mvExcisionHrelCohMap
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (mvExcisionHrelCohMap A B G (n + 1)) := by
  letI : IsIso (mvExcisionToSmallChainMap A B) :=
    isIso_mvExcisionToSmallChainMap A B
  letI : IsIso (homDualMap (mvExcisionToSmallChainMap A B) G) := by
    exact (homDualIso (asIso (mvExcisionToSmallChainMap A B)) G).isIso_hom
  letI : IsIso (HomologicalComplex.homologyMap
      (homDualMap (mvSmallRelMap A B) G) (n + 1)) :=
    isIso_homologyMap_homDual_mvSmallRelMap A B G h n
  change IsIso (HomologicalComplex.homologyMap
    (homDualMap
      (relComplexMap (mvInclLeft A B) (subIncl B)
        (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl)) G)
      (n + 1))
  rw [← mvExcisionChainMap_comp A B, homDualMap_comp,
    HomologicalComplex.homologyMap_comp]
  infer_instance

end Submission
