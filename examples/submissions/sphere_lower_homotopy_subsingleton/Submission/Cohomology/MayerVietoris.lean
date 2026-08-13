/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.DualShortExact
import Submission.Cohomology.DualBridge
import Submission.Cohomology.DegreeZero
import Submission.Cohomology.Point
import Submission.Homology.MayerVietorisLES

/-!
# Mayer--Vietoris for singular cohomology

The singular-chain Mayer--Vietoris sequence is degreewise split.  Dualizing that explicit
splitting produces the short exact sequence of cochain complexes
```
0 ⟶ Hom(C_*^{A,B}(X), R) ⟶ Hom(C_*(A) ⊞ C_*(B), R)
    ⟶ Hom(C_*(A ∩ B), R) ⟶ 0.
```
The small-simplices equivalence identifies its first term with the singular cochains of `X` up to
chain homotopy.  This file exposes both inputs in a form suitable for the cohomological long exact
sequence.

## Main definitions

* `Submission.mvCohSC` -- the short complex of dual singular-chain complexes;
* `Submission.mvCohSC_shortExact` -- its short exactness;
* `Submission.mvSmallCohomologyIso` -- small cochains compute singular cohomology.
-/

open CategoryTheory Limits AlgebraicTopology

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X) (R : Type) [CommRing R]

/-- The degreewise dual of the Mayer--Vietoris short complex, with its arrows reversed. -/
abbrev mvCohSC :
    ShortComplex (HomologicalComplex AddCommGrpCat.{0} (ComplexShape.down ℕ).symm) :=
  homDualShortComplex (mvSC A B) (AddCommGrpCat.of R)

/-- **The cochain-level Mayer--Vietoris sequence is short exact.** -/
theorem mvCohSC_shortExact : (mvCohSC A B R).ShortExact :=
  homDualShortComplex_shortExact (mvSC A B) (AddCommGrpCat.of R) (mvSCSplitting A B)

/-- Dualizing the small-simplices chain-homotopy equivalence identifies the singular cohomology
of `X` with the cohomology of the small-cochain complex. -/
def mvSmallCohomologyIso (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (homDual (Csing X) (AddCommGrpCat.of R)).homology n ≅
      (homDual (mvSC A B).X₃ (AddCommGrpCat.of R)).homology n :=
  (homDualHomotopyEquiv (mvSmallHomotopyEquiv A B h) (AddCommGrpCat.of R)).toHomologyIso n

@[simp]
theorem mvSmallCohomologyIso_hom
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallCohomologyIso A B R h n).hom =
      HomologicalComplex.homologyMap
        (homDualMap (mvSmallIncl A B) (AddCommGrpCat.of R)) n := rfl

/-- The homology functor on dual (cochain) complexes. -/
abbrev cohFun (n : ℕ) :
    HomologicalComplex AddCommGrpCat.{0} (ComplexShape.down ℕ).symm ⥤ AddCommGrpCat.{0} :=
  HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.down ℕ).symm n

/-- Cohomology of the middle Mayer--Vietoris complex is the biproduct of the cohomologies of the
two pieces. -/
def mvCohMiddleIso (n : ℕ) :
    (mvCohSC A B R).X₂.homology n ≅
      (homDual (Csing (TopCat.of A)) (AddCommGrpCat.of R)).homology n ⊞
        (homDual (Csing (TopCat.of B)) (AddCommGrpCat.of R)).homology n :=
  (HomotopyEquiv.ofIso (homDualBiprodIso (Csing (TopCat.of A)) (Csing (TopCat.of B))
    (AddCommGrpCat.of R))).toHomologyIso n ≪≫
      additiveBiprodIso (cohFun n)
        (homDual (Csing (TopCat.of A)) (AddCommGrpCat.of R))
        (homDual (Csing (TopCat.of B)) (AddCommGrpCat.of R))

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero, the Mayer--Vietoris map from the two pieces to their path-connected
intersection is an epimorphism. -/
theorem epi_mvCohSC_g_homology_zero [PathConnectedSpace (A ∩ B : Set X)] :
    Epi (HomologicalComplex.homologyMap (mvCohSC A B R).g 0) := by
  change Epi (HomologicalComplex.homologyMap
    (homDualMap (mvSC A B).f (AddCommGrpCat.of R)) 0)
  let p :
      (homDual (Csing (TopCat.of A)) (AddCommGrpCat.of R)).homology 0 ⟶
        (homDual (Csing (TopCat.of A) ⊞ Csing (TopCat.of B))
          (AddCommGrpCat.of R)).homology 0 :=
    HomologicalComplex.homologyMap
      (homDualMap
        (biprod.fst : Csing (TopCat.of A) ⊞ Csing (TopCat.of B) ⟶ Csing (TopCat.of A))
        (AddCommGrpCat.of R)) 0
  let q :
      (homDual (Csing (TopCat.of A) ⊞ Csing (TopCat.of B))
        (AddCommGrpCat.of R)).homology 0 ⟶
        (homDual (Csing (TopCat.of (A ∩ B : Set X)))
          (AddCommGrpCat.of R)).homology 0 :=
    HomologicalComplex.homologyMap
      (homDualMap (mvSC A B).f (AddCommGrpCat.of R)) 0
  show Epi q
  have hpq : p ≫ q =
      HomologicalComplex.homologyMap
        (homDualMap (CsingMap (mvInclLeft A B)) (AddCommGrpCat.of R)) 0 := by
    dsimp only [p, q]
    rw [← HomologicalComplex.homologyMap_comp, ← homDualMap_comp]
    congr 2
    exact mvSC_f_fst A B
  have hsurj := surjective_dualHomologyMap_of_surjective_Hsing_map
    (R := R) (mvInclLeft A B) 0
    (surjective_Hsing_map_zero_of_pathConnected (R := R) (mvInclLeft A B))
  haveI : Epi (p ≫ q) := by
    rw [hpq, AddCommGrpCat.epi_iff_surjective]
    exact hsurj
  exact epi_of_epi p q

/-- If both pieces are contractible, the middle term of the cohomological Mayer--Vietoris
sequence vanishes in positive degrees. -/
theorem isZero_mvCohSC_X₂_homology_of_contractible
    [ContractibleSpace A] [ContractibleSpace B] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((mvCohSC A B R).X₂.homology n) := by
  refine IsZero.of_iso ?_ (mvCohMiddleIso A B R n)
  rw [biprod_isZero_iff]
  exact ⟨isZero_dualHomology_of_contractible R n hn,
    isZero_dualHomology_of_contractible R n hn⟩

/-- A space covered by two contractible pieces with path-connected intersection has vanishing
degree-one cohomology. -/
theorem isZero_dualHomology_one_of_contractible_cover
    (h : interior A ∪ interior B = Set.univ)
    [ContractibleSpace A] [ContractibleSpace B]
    [PathConnectedSpace (A ∩ B : Set X)] :
    IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology 1) := by
  haveI : Epi (HomologicalComplex.homologyMap (mvCohSC A B R).g 0) :=
    epi_mvCohSC_g_homology_zero A B R
  have hδ : (mvCohSC_shortExact A B R).δ 0 1 (by rfl) = 0 := by
    rw [← cancel_epi (HomologicalComplex.homologyMap (mvCohSC A B R).g 0)]
    exact (mvCohSC_shortExact A B R).comp_δ 0 1 (by rfl)
  have hzMiddle := isZero_mvCohSC_X₂_homology_of_contractible A B R 1 (by omega)
  have hzSmall : IsZero ((mvCohSC A B R).X₁.homology 1) :=
    ((mvCohSC_shortExact A B R).homology_exact₁ 0 1 (by rfl)).isZero_X₂
      hδ (hzMiddle.eq_of_tgt _ _)
  exact IsZero.of_iso hzSmall (mvSmallCohomologyIso A B R h 1)

/-- The successor relation in the cochain-complex shape. -/
lemma mvCohRel (n : ℕ) : (ComplexShape.down ℕ).symm.Rel n (n + 1) := rfl

/-- The connecting morphism on dual-complex cohomology,
`Hⁿ(A ∩ B;R) ⟶ Hⁿ⁺¹(X;R)`. -/
def mvCohδ (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (homDual (Csing (TopCat.of (A ∩ B : Set X))) (AddCommGrpCat.of R)).homology n ⟶
      (homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 1) :=
  (mvCohSC_shortExact A B R).δ n (n + 1) (mvCohRel n) ≫
    (mvSmallCohomologyIso A B R h (n + 1)).inv

/-- For a cover by two contractible pieces, the cohomological connecting map is the suspension
isomorphism `Hⁿ⁺¹(A ∩ B;R) ≅ Hⁿ⁺²(X;R)`. -/
def mvCohδIso_of_contractible (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    [ContractibleSpace A] [ContractibleSpace B] :
    (homDual (Csing (TopCat.of (A ∩ B : Set X))) (AddCommGrpCat.of R)).homology (n + 1) ≅
      (homDual (Csing X) (AddCommGrpCat.of R)).homology (n + 2) :=
  (mvCohSC_shortExact A B R).δIso (n + 1) (n + 2) (mvCohRel (n + 1))
      (isZero_mvCohSC_X₂_homology_of_contractible A B R (n + 1) (by omega))
      (isZero_mvCohSC_X₂_homology_of_contractible A B R (n + 2) (by omega)) ≪≫
    (mvSmallCohomologyIso A B R h (n + 2)).symm

/-- The preceding Mayer--Vietoris suspension isomorphism, transported to the concrete singular
cohomology groups. -/
def mvHsingδEquiv_of_contractible (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    [ContractibleSpace A] [ContractibleSpace B] :
    Hsing (n + 1) (TopCat.of (A ∩ B : Set X)) R ≃+
      Hsing (n + 2) X R :=
  (HsingEquivDualHomology R (TopCat.of (A ∩ B : Set X)) (n + 1)).trans
    ((mvCohδIso_of_contractible A B R h n).addCommGroupIsoToAddEquiv.trans
      (HsingEquivDualHomology R X (n + 2)).symm)

end Submission
