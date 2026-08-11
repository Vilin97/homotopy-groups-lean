/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Submission.Excision.SimplicialSet.ULift
public import Submission.Excision.SingularHomology.Basic

/-!
# The singular chain complex of `Ulift X`

-/

universe v u

@[expose] public section

open CategoryTheory Limits Simplicial

-- Reducibility attributes that upstream Mathlib gained after the revision pinned here;
-- the vendored library relies on them.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.AlternatingFaceMapComplex.obj AlgebraicTopology.alternatingFaceMapComplex
  SSet.chainComplexFunctor

namespace TopCat

/-- The bijection between the singular simplices of `uliftFunctor.{v}.obj X` and
the singular simplices of `X`. -/
noncomputable def toSSetULiftEquiv {X : TopCat.{u}} {n : ℕ} :
    toSSet.obj (uliftFunctor.{v}.obj X) _⦋n⦌ ≃ toSSet.obj X _⦋n⦌ :=
  (TopCat.toSSetObjEquiv ..).trans
    ((Homeomorph.continuousMapCongr (.refl _) X.uliftFunctorObjHomeo.symm).trans
      ((TopCat.toSSetObjEquiv ..).symm))

/-- If `X : TopCat.{u}`, the singular simplicial set of `uliftFunctor.{v}.obj X`
identifies to the simplicial set obtained by applying `SSet.uliftFunctor`
to the singular simplicial set of `X`. -/
noncomputable def toSSetObjULiftFunctorObjIso (X : TopCat.{u}) :
    toSSet.obj (uliftFunctor.{v}.obj X) ≅ SSet.uliftFunctor.obj (toSSet.obj X) :=
  NatIso.ofComponents
    (fun n ↦ (Equiv.toIso (toSSetULiftEquiv.trans Equiv.ulift.symm)))

/-- The functor `TopCat.toSSet : TopCat ⥤ SSet` commute with the application
of the `ULift`-functors on topological spaces and simplicial sets. -/
noncomputable def uliftFunctorCompToSSetIso :
    TopCat.uliftFunctor.{v, u} ⋙ TopCat.toSSet ≅
      TopCat.toSSet ⋙ SSet.uliftFunctor :=
  NatIso.ofComponents toSSetObjULiftFunctorObjIso

end TopCat

variable {C : Type*} [Category* C] [HasCoproducts.{max u v} C] [Preadditive C]

namespace AlgebraicTopology

/-- The isomorphism `(uliftFunctor.{v}.obj X).singularChainComplex R ≅ X.singularChainComplex R`
for `X : TopCat.{u}` and `R : C`, as a natural isomorphism of
bifunctors `C ⥤ TopCat.{u} ⥤ ChainComplex C ℕ`. -/
noncomputable def singularChainComplexFunctorULiftIso :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (singularChainComplexFunctor.{max u v} C) ⋙
      (Functor.whiskeringLeft _ _ _).obj TopCat.uliftFunctor.{v, u} ≅
    (singularChainComplexFunctor.{u} C) :=
  Functor.isoWhiskerLeft (SSet.chainComplexFunctor C)
    ((Functor.whiskeringLeft _ _ _).mapIso
      TopCat.uliftFunctorCompToSSetIso.{v, u}) ≪≫
  Functor.isoWhiskerRight SSet.chainComplexFunctorULiftIso.{v, u}
    ((Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{u})

/-- The isomorphism `(uliftFunctor.{v}.obj X).singularChainComplex R ≅ X.singularChainComplex R`
for `X : TopCat.{u}` and a fixed `R : C`, as a natural isomorphism of
functors `TopCat.{u} ⥤ ChainComplex C ℕ`. -/
noncomputable abbrev uliftFunctorCompSingularChainComplexFunctorIso (R : C) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    TopCat.uliftFunctor.{v, u} ⋙ (singularChainComplexFunctor.{max u v} C).obj R ≅
      (singularChainComplexFunctor.{u} C).obj R :=
  singularChainComplexFunctorULiftIso.app _

@[reassoc]
lemma ι_uliftFunctorCompSingularChainComplexFunctorIso_inv_app (X : TopCat.{u}) (R : C)
    {n : ℕ} (x : TopCat.toSSet.obj X _⦋n⦌) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    X.ιSingularChainComplex x ≫
      ((uliftFunctorCompSingularChainComplexFunctorIso.{v, u} R).inv.app X).f n =
        TopCat.ιSingularChainComplex _ ((TopCat.toSSetULiftEquiv).symm x) := by
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  have h : ((TopCat.toSSet.{u} ⋙ SSet.uliftFunctor.{v, u}).obj X).ιChainComplex (R := R)
        (⟨x⟩ : ULift.{v} _) ≫
      (SSet.chainComplexMap (TopCat.uliftFunctorCompToSSetIso.{v, u}.inv.app X) R).f n =
      ((TopCat.uliftFunctor.{v, u} ⋙ TopCat.toSSet).obj X).ιChainComplex
        (TopCat.toSSetULiftEquiv.{v}.symm x) := by
    rw [SSet.ι_chainComplexMap_f]
    rfl
  simp [uliftFunctorCompSingularChainComplexFunctorIso, singularChainComplexFunctorULiftIso,
    SSet.chainComplexFunctorULiftIso]
  erw [CategoryTheory.ι_sigmaConstObjObjULiftIso_inv_assoc]
  exact h

end AlgebraicTopology

open AlgebraicTopology

/-- Given `X : TopCat.{u}` and `R : C`, the singular chain complex
of `uliftFunctor.{v}.obj X` with coefficients is `R` is isomorphic to the
singular chain complex of `X`. -/
noncomputable abbrev TopCat.singularChainComplexULiftIso (X : TopCat.{u}) (R : C) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (uliftFunctor.{v}.obj X).singularChainComplex R ≅ X.singularChainComplex R :=
  (uliftFunctorCompSingularChainComplexFunctorIso R).app X
