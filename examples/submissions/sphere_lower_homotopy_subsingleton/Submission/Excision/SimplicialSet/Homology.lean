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

universe w

@[expose] public section

open CategoryTheory Limits

-- Reducibility attributes that upstream Mathlib gained after the revision pinned here;
-- the vendored library relies on them.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.AlternatingFaceMapComplex.obj AlgebraicTopology.alternatingFaceMapComplex
  SSet.chainComplexFunctor

namespace SSet

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

instance {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) (n : ℕ) :
    Mono ((chainComplexMap f R).f n) :=
  inferInstanceAs (Mono ((sigmaConst.obj R).map (f.app (Opposite.op (SimplexCategory.mk n)))))

instance {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) :
    Mono (chainComplexMap f R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

/-- The isomorphism of chain complexes that is induced by an isomorphism of simplicial sets. -/
noncomputable abbrev chainComplexMapIso {X Y : SSet.{w}} (e : X ≅ Y) (R : C) :
    X.chainComplex R ≅ Y.chainComplex R where
  hom := chainComplexMap e.hom R
  inv := chainComplexMap e.inv R

end SSet
