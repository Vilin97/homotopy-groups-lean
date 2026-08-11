/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Submission.Excision.Mathlib.SimplicialSetHomologyRelative
public import Submission.Excision.Limits.SigmaConst
public import Submission.Excision.Preadditive.HasZeroObject

/-!
# ...

-/

universe w

@[expose] public section

open CategoryTheory Limits Simplicial Opposite

-- Reducibility attributes that upstream Mathlib gained after the revision pinned here;
-- the vendored library relies on them.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.AlternatingFaceMapComplex.obj AlgebraicTopology.alternatingFaceMapComplex
  SSet.chainComplexFunctor CategoryTheory.Functor.id

namespace SSetPair

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

section

/-- The isomorphism of chain complexes that is induced by an isomorphism of
pairs of simplicial sets. -/
noncomputable abbrev chainComplexMapIso {X Y : SSetPair.{w}} (e : X ≅ Y) (R : C) :
    X.chainComplex R ≅ Y.chainComplex R where
  hom := chainComplexMap e.hom R
  inv := chainComplexMap e.inv R

end

section

variable (X : SSetPair.{w})

/-- If `X : SSetPair` and `n : ℕ`, this is the kernel fork with point `(X.left.chainComplex R).X n`
for the map `(X.chainComplexπ R).f n : (X.right.chainComplex R).X n ⟶ (X.chainComplex R).X n`. -/
noncomputable def kernelForkChainComplexX (R : C) (n : ℕ) :
    KernelFork ((X.chainComplexπ R).f n) :=
  KernelFork.ofι _ (X.chainComplex_condition_f R n)

variable (R : C) (n : ℕ)

attribute [local instance] Preadditive.hasZeroObject_of_hasCoproducts in
/-- If `X : SSetPair` and `n : ℕ`, the kernel of the morphism
`(X.chainComplexπ R).f n : (X.right.chainComplex R).X n ⟶ (X.chainComplex R).X n`
identifies to `(X.left.chainComplex R).X n`. -/
@[no_expose]
noncomputable def isLimitKernelForkChainComplexX (R : C) (n : ℕ) :
    IsLimit (X.kernelForkChainComplexX R n) :=
  isLimitKernelForkOfIsColimitCokernelCoforkSigmaConst _ _ (injective_of_mono _)
    (X.isColimitCokernelCoforkChainComplexX R n)

/-- If `X : SSetPair`, this is the kernel fork with point `X.left.chainComplex R`
for the map `X.chainComplexπ R : X.right.chainComplex R ⟶ X.chainComplex R`. -/
noncomputable def kernelForkChainComplex (R : C) :
    KernelFork (X.chainComplexπ R) :=
  KernelFork.ofι _ (X.chainComplex_condition R)

/-- If `X : SSetPair`, the kernel of `X.chainComplexπ R : X.right.chainComplex R ⟶ X.chainComplex R`
identifies to `X.left.chainComplex R`. -/
@[no_expose]
noncomputable def isLimitKernelForkChainComplex (R : C) :
    IsLimit (X.kernelForkChainComplex R) :=
  HomologicalComplex.isLimitOfEval _ _
    (fun n ↦ (KernelFork.isLimitMapConeEquiv _ _).2
      (X.isLimitKernelForkChainComplexX R n))

end

@[reassoc (attr := simp)]
lemma ιChainComplex_π_f_eq_zero
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.left _⦋n⦌) :
    dsimp% X.right.ιChainComplex (X.hom.app _ x) ≫ (X.chainComplexπ R).f n = 0 := by
  simpa only [comp_zero, SSet.ι_chainComplexMap_f_assoc] using
    X.left.ιChainComplex x ≫= X.chainComplex_condition_f R n

@[reassoc]
lemma ιChainComplex_π_f_eq_zero_of_mem_range
    (X : SSetPair.{w}) (R : C) {n : ℕ} (x : X.right _⦋n⦌) (hx : x ∈ Set.range (X.hom.app _)) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n = 0 := by
  obtain ⟨x, rfl⟩ := hx
  rw [X.ιChainComplex_π_f_eq_zero]

@[reassoc]
lemma ιChainComplex_π_f_eq_zero_of_subcomplex {X : SSet.{w}} (A : X.Subcomplex) (R : C) {n : ℕ}
    (x : X _⦋n⦌) (hx : x ∈ A.obj _) :
    X.ιChainComplex x ≫ (A.pair.chainComplexπ R).f n = 0 :=
  A.pair.ιChainComplex_π_f_eq_zero_of_mem_range _ _ ⟨⟨x, hx⟩, rfl⟩

lemma chainComplexX_hom_ext {X : SSetPair.{w}} {R T : C} {n : ℕ}
    {f g : (X.chainComplex R).X n ⟶ T}
    (h : ∀ (x : X.right _⦋n⦌) (_ : x ∉ Set.range (X.hom.app (op ⦋n⦌))),
      X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫ f =
      X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫ g) : f = g := by
  rw [← cancel_epi ((X.chainComplexπ R).f n)]
  ext x
  by_cases hx : x ∈ Set.range (X.hom.app (op ⦋n⦌))
  · simp [X.ιChainComplex_π_f_eq_zero_of_mem_range_assoc _ x hx]
  · exact h _ hx

section

variable {X : SSetPair.{w}} {R T : C} {n : ℕ}
  (f : X.right _⦋n⦌ → (R ⟶ T))
  (hf : ∀ (x : X.left _⦋n⦌), f (X.hom.app _ x) = 0)

/-- Constructor for morphisms from the `n`-chains of a pair of simplicial sets. -/
noncomputable def chainComplexXDesc :
    (X.chainComplex R).X n ⟶ T :=
  (CokernelCofork.IsColimit.desc' (X.isColimitCokernelCoforkChainComplexX R n)
    (Sigma.desc f) (by
      ext x
      simp only [Functor.id_obj, SSet.ι_chainComplexMap_f_assoc, comp_zero]
      exact (Sigma.ι_desc ..).trans (hf x))).1

@[reassoc]
lemma ι_chainComplexXDesc (x : X.right _⦋n⦌) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫
      chainComplexXDesc f hf = f x := by
  have : (X.chainComplexπ R).f n ≫ chainComplexXDesc f hf = Sigma.desc f :=
    (CokernelCofork.IsColimit.desc' (X.isColimitCokernelCoforkChainComplexX R n)
      (Sigma.desc f) _).2
  rw [this]
  apply Sigma.ι_desc

end

@[reassoc]
lemma chainComplexπ_naturality {X Y : SSetPair.{w}} (f : X ⟶ Y) (R : C) :
    X.chainComplexπ R ≫ chainComplexMap f _ =
      SSet.chainComplexMap f.right _ ≫ Y.chainComplexπ R :=
  (((chainComplexFunctorπ C).app R).naturality f).symm

@[reassoc]
lemma chainComplexπ_f_naturality {X Y : SSetPair.{w}} (f : X ⟶ Y) (R : C) (n : ℕ) :
    (X.chainComplexπ R).f n ≫ (chainComplexMap f _).f n =
      (SSet.chainComplexMap f.right _).f n ≫ (Y.chainComplexπ R).f n := by
  simp only [← HomologicalComplex.comp_f, chainComplexπ_naturality]

@[reassoc (attr := simp)]
lemma ι_chainComplexMap_f {X Y : SSetPair.{w}} (f : X ⟶ Y) (R : C) {n : ℕ} (x : X.right _⦋n⦌) :
    X.right.ιChainComplex x ≫ (X.chainComplexπ R).f n ≫ (chainComplexMap f R).f n =
      Y.right.ιChainComplex (f.right.app _ x) ≫ (Y.chainComplexπ R).f n := by
  simp [chainComplexπ_f_naturality]

end SSetPair
