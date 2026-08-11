/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Submission.Excision.SingularHomology.Basic


/-!
# Constructor for natural transformations on singular chains

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Simplicial

namespace AlgebraicTopology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C]

namespace singularChainComplexFunctor

variable {R : C} {n : ℕ} {F : TopCat.{w} ⥤ C}

/-- Constructor for natural transformations from the functor of `n`-singular chains. -/
noncomputable def natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) :
    (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F where
  app X := Sigma.desc (fun s ↦ f ≫ F.map s.down)
  naturality {X Y} g := Sigma.hom_ext _ _ (fun s ↦ by
    erw [TopCat.ι_singularChainComplexMap_assoc, Sigma.ι_desc, Sigma.ι_desc_assoc,
      Category.assoc, ← Functor.map_comp]
    rfl)

@[reassoc (attr := simp)]
lemma ι_natTransMk (f : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌))
    (X : TopCat.{w}) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    X.ιSingularChainComplex s ≫ (natTransMk f).app X =
      f ≫ F.map s.down :=
  Sigma.ι_desc ..

lemma natTrans_ext
    {f g : (singularChainComplexFunctor C).obj R ⋙ HomologicalComplex.eval _ _ n ⟶ F}
    (h : TopCat.ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫ f.app _ =
      TopCat.ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫ g.app _) :
    f = g := by
  ext X
  refine Sigma.hom_ext _ _ (fun s ↦ ?_)
  have H := h =≫ F.map s.down
  rw [Category.assoc, Category.assoc] at H
  erw [← f.naturality, ← g.naturality] at H
  erw [TopCat.ι_singularChainComplexMap_assoc, TopCat.ι_singularChainComplexMap_assoc] at H
  exact H

@[simp]
lemma natTransMk_zero :
    natTransMk (0 : R ⟶ F.obj (SimplexCategory.toTop.{w} ^⦋n⦌)) = 0 :=
  natTrans_ext (by
    simp
    exact comp_zero.symm)

end singularChainComplexFunctor

end AlgebraicTopology
