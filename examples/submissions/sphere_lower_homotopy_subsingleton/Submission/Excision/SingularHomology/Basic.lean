/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic


/-!
# Constructor for natural transformations on singular chains

-/

@[expose] public section

universe w v u

open AlgebraicTopology CategoryTheory Limits Simplicial

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The singular chain complex of a topological space with coefficients in `R`. -/
noncomputable abbrev singularChainComplex (X : TopCat.{w}) (R : C) :
    ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

/-- The morphism of singular chain complexes that is induced by a morphism in `TopCat`. -/
noncomputable abbrev singularChainComplexMap {X Y : TopCat.{w}} (f : X ⟶ Y) (R : C) :
    X.singularChainComplex R ⟶ Y.singularChainComplex R :=
  ((singularChainComplexFunctor C).obj R).map f

/-- Inclusion of a summand of an object in the singular chain complex of
a topological space. -/
noncomputable abbrev ιSingularChainComplex
    (X : TopCat.{w}) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    R ⟶ (X.singularChainComplex R).X n :=
  Sigma.ι (fun _ ↦ R) x

lemma singularChainComplexX_hom_ext {X : TopCat.{w}} {R : C} {n : ℕ} {T : C}
    {f g : (X.singularChainComplex R).X n ⟶ T}
    (h : ∀ (x : (toSSet.obj X) _⦋n⦌),
      X.ιSingularChainComplex x ≫ f = X.ιSingularChainComplex x ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

@[reassoc]
lemma ι_singularChainComplex_d
    (X : TopCat.{w}) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n + 1⦌) :
    X.ιSingularChainComplex (R := R) x ≫ (X.singularChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1 : ℤ) ^ (i : ℕ) • X.ιSingularChainComplex ((toSSet.obj X).δ i x) :=
  SSet.ιChainComplex_d (toSSet.obj X) R x

/-- The universal element in `(toSSet.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌`. -/
noncomputable def toSSet.univObj (n : ℕ) :
    (toSSet.{w}.obj (SimplexCategory.toTop ^⦋n⦌)) _⦋n⦌ := ⟨𝟙 _⟩

lemma toSSet.δ_univObj {n : ℕ} (i : Fin (n + 2)) :
    (toSSet.{w}.obj (SimplexCategory.toTop ^⦋n + 1⦌)).δ i (univObj.{w} (n + 1)) =
      (toSSet.map (SimplexCategory.toTop.{w}.map (SimplexCategory.δ i))).app _ (univObj.{w} n) :=
  rfl

lemma toSSet.exists_map_app_univObj_eq
    {X : TopCat.{w}} {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    ∃ (f : SimplexCategory.toTop ^⦋n⦌ ⟶ X),
      (toSSet.map f).app _ (univObj n) = s := by
  obtain ⟨s, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
  exact ⟨ofHom (s.comp ⟨ULift.down, by fun_prop⟩), rfl⟩

@[reassoc (attr := simp)]
lemma ι_singularChainComplexMap
    {X Y : TopCat.{w}} (f : X ⟶ Y) {R : C} {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) :
    X.ιSingularChainComplex (R := R) x ≫ (singularChainComplexMap f R).f n =
        Y.ιSingularChainComplex ((toSSet.map f).app _ x) :=
  SSet.ι_chainComplexMap_f _ _ (toSSet.map f) R x

end TopCat
