/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Submission.Excision.Limits.SigmaConst

/-!
# ...

-/

universe v u

@[expose] public section

open CategoryTheory Limits

namespace SSet

variable {C : Type*} [Category* C] [HasCoproducts.{max u v} C] [Preadditive C]

/-- The isomorphism `(uliftFunctor.{v}.obj X).chainComplex R ≅ X.chainComplex R`
for `X : SSet.{u}` and `R : C`, as a natural isomorphism of
bifunctors `C ⥤ SSet.{u} ⥤ ChainComplex C ℕ`. -/
noncomputable def chainComplexFunctorULiftIso :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (chainComplexFunctor.{max u v} C) ⋙
      (Functor.whiskeringLeft _ _ _).obj uliftFunctor.{v, u} ≅
    (chainComplexFunctor.{u} C) :=
  (Functor.postcompose₂.obj (AlgebraicTopology.alternatingFaceMapComplex C)).mapIso
    (Functor.isoWhiskerRight sigmaConstULiftIso.{v, u} (SimplicialObject.whiskering (Type u) C))

/-- The isomorphism `(uliftFunctor.{v}.obj X).chainComplex R ≅ X.chainComplex R`
for `X : SSet.{u}` and a fixed `R : C`, as a natural isomorphism of
functors `SSet.{u} ⥤ ChainComplex C ℕ`. -/
noncomputable abbrev uliftFunctorCompChainComplexFunctorIso (R : C) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    uliftFunctor.{v, u} ⋙ (chainComplexFunctor.{max u v} C).obj R ≅
      (chainComplexFunctor.{u} C).obj R :=
  chainComplexFunctorULiftIso.app _

/-- Given `X : SSet.{u}` and `R : C`, the chain complex of `uliftFunctor.{v}.obj X`
with coefficients is `R` is isomorphic to the chain complex of `X`. -/
noncomputable abbrev chainComplexULiftIso (X : SSet.{u}) (R : C) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (uliftFunctor.{v}.obj X).chainComplex R ≅ X.chainComplex R :=
  (uliftFunctorCompChainComplexFunctorIso R).app X

end SSet
