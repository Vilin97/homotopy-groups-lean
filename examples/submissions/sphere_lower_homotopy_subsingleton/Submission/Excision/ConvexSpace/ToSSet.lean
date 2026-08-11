/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Submission.Excision.ConvexSpace.StdSimplex
public import Submission.Excision.SimplexCategory.Basic
public import Submission.Excision.Preadditive.HasZeroObject
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Affine simplices in the singular simplicial set of a convex space

-/

universe w u

@[expose] public section

open CategoryTheory Limits Simplicial

-- Reducibility attributes that upstream Mathlib gained after the revision pinned here;
-- the vendored library relies on them.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.AlternatingFaceMapComplex.obj AlgebraicTopology.alternatingFaceMapComplex
  SSet.chainComplexFunctor

namespace Convexity

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

namespace ConvexSpace

variable (Y Z : Type w) [ConvexSpace R Y] [ConvexSpace R Z]

variable {Y} in
/-- The cone of an affine map from the standard simplex. -/
noncomputable def AffineMap.cone
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y :=
  StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i)))

variable {Y} in
lemma AffineMap.cone_def
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    s.cone y = StdSimplex.affineMapMk (Fin.cases y (fun i ↦ s (.single i))) := rfl

variable {Y} in
@[simp]
lemma AffineMap.cone_single_zero
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y) :
    s.cone y (.single 0) = y := by
  simp [cone_def]

variable {Y} in
@[simp]
lemma AffineMap.cone_single_succ
    {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin n)) Y) (y : Y)
    (j : Fin n) :
    s.cone y (.single j.succ) = s (.single j) := by
  simp [cone_def]

@[simp]
lemma AffineMap.cone_mk₁ (y y₀ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀]).cone y =
      StdSimplex.affineMapMk ![y, y₀] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

@[simp]
lemma AffineMap.cone_mk₂ (y y₀ y₁ : Y) :
    (StdSimplex.affineMapMk (R := R) ![y₀, y₁]).cone y =
      StdSimplex.affineMapMk ![y, y₀, y₁] := by
  rw [cone_def]
  congr
  ext i
  fin_cases i <;> aesop

lemma AffineMap.comp_cone {n : ℕ} (φ : ConvexSpace.AffineMap R Y Z)
    (ψ : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) (y : Y) :
    (φ.comp ψ).cone (φ y) = φ.comp (ψ.cone y) := by
  ext i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ <;> simp

variable (R) in
/-- Given a convex space `Y`, this is the simplicial set whose `n`-simplices are
affine maps from the `n`-dimensional standard simplex to `Y`. -/
@[simps -isSimp]
noncomputable abbrev toSSet : SSet where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)
  map_comp _ _ := by
    ext
    dsimp
    rw [← StdSimplex.map_comp]
    rfl

variable {Y Z} in
/-- The morphism `toSSet R Y ⟶ toSSet R Z` of simplicial sets of
affine simplices that is induced by an affine map from `Y` to `Z`. -/
@[simps]
noncomputable def AffineMap.toSSetMap (φ : ConvexSpace.AffineMap R Y Z) :
    toSSet R Y ⟶ toSSet R Z where
  app n := ↾fun g ↦ φ.comp g

section

variable {Y}

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply

@[simp]
lemma toSSet.δ_zero_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₁] := by
  ext i; fin_cases i; simp

@[simp high]
lemma toSSet.δ_one_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₀] := by
  ext i; fin_cases i; simp

@[simp]
lemma toSSet.δ_zero_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₁, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet.δ_one_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet.δ_two_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 2 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₁] := by
  ext i; fin_cases i <;> simp [Fin.succAbove]

@[simp]
lemma toSSet.δ_zero (y : Y) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    (toSSet R Y).δ 0 (s.cone y) = s := by
  ext
  simp [SimplicialObject.δ_def, SimplexCategory.δ_apply,
    AffineMap.cone_def, StdSimplex.affineMapMk_apply]

lemma toSSet.δ_affineMapMk {n : ℕ} (s : Fin (n + 2) → Y)
    (i : Fin (n + 2)) :
    (toSSet R Y).δ i (StdSimplex.affineMapMk s) = StdSimplex.affineMapMk (s ∘ i.succAbove) := by
  aesop

end

variable (R) in
/-- Given a convex space `Y`, this is the augmented simplicial set
whose `n`-simplices are affine maps from the `n`-dimensional standard simplex to `Y`. -/
noncomputable abbrev toSSetAugmented : SSet.Augmented where
  left := toSSet R Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply AffineMap.cone_def
  StdSimplex.affineMapMk_apply in
variable {Y} in
/-- Given a convex space `Y` (over a semiring `R`) and `y : Y`, this is an extra degeneracy
for `ConvexSpace.toSSetAugmented R Y`. In degree `0`, it is given by `[y]`, and otherwise
it sends a `n`-simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, where affine maps
from the standard `n`-simplex to `Y` are identified to tuples `[y₀, ..., yₙ]` given
by the images of the vertices. -/
@[simps]
noncomputable def toSSet.extraDegeneracy (y : Y) :
    (toSSetAugmented R Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ f.cone y
  s₀_comp_δ₁ := by ext _ i; fin_cases i; simp
  s_comp_δ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp

variable {Y Z} {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{max u w} C]

/-- Given a convex space `Y`, `y : Y` and `n : ℕ`, this is the morphism from
affine `n`-chains (with coefficients in `M`) to affine `n + 1`-chains which
sends a simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`. -/
noncomputable def toSSet.cone (y : Y) (M : C) (n : ℕ) :
    ((toSSet R Y).chainComplex M).X n ⟶
      ((toSSet R Y).chainComplex M).X (n + 1) :=
  ((extraDegeneracy y).map (sigmaConst.obj M)).s n

/-- Composing the inclusion of a summand of a coproduct of copies of `M` with the map
induced by a reindexing map `p` gives the inclusion of the reindexed summand. -/
lemma _root_.CategoryTheory.Limits.Sigma.ι_comp_map'_const
    {D : Type*} [Category* D] {α β : Type*} (M : D)
    [HasCoproduct (fun (_ : α) ↦ M)] [HasCoproduct (fun (_ : β) ↦ M)]
    (p : α → β) (a : α) :
    Sigma.ι (fun (_ : α) ↦ M) a ≫ Sigma.map' p (fun _ ↦ 𝟙 M) =
      Sigma.ι (fun (_ : β) ↦ M) (p a) := by
  simp

/-- Rearrangement lemma in a preadditive category: an identity
`0 = d ≫ (-s) + (-t) ≫ d' + 𝟙 B` is the same as `d ≫ s + t ≫ d' = 𝟙 B`. -/
lemma _root_.CategoryTheory.Preadditive.comp_add_comp_eq_id
    {D : Type*} [Category* D] [Preadditive D] {A B E : D}
    (d : B ⟶ A) (s : A ⟶ B) (t : B ⟶ E) (d' : E ⟶ B)
    (h : 0 = d ≫ (-s) + (-t) ≫ d' + 𝟙 B) :
    d ≫ s + t ≫ d' = 𝟙 B := by
  have key : 𝟙 B - (d ≫ s + t ≫ d') = 0 := by
    rw [h, Preadditive.comp_neg, Preadditive.neg_comp]; abel
  exact (sub_eq_zero.1 key).symm

@[simp]
lemma toSSet.d_comp_cone_add_cone_comp_d (y : Y) (M : C) {n : ℕ} :
    ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n +
    toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) = 𝟙 _ := by
  have := Preadditive.hasZeroObject_of_hasCoproducts C
  have h := (((extraDegeneracy (R := R) y).map
    (sigmaConst.obj M)).homotopyEquiv.homotopyHomInvId).comm (n + 1)
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex] at h
  have h1 : ((extraDegeneracy (R := R) y).map
      (sigmaConst.obj M)).homotopyEquiv.homotopyHomInvId.hom n (n + 1) =
      -toSSet.cone y M n := by
    simp [SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, cone]; rfl
  have h2 : ((extraDegeneracy (R := R) y).map
      (sigmaConst.obj M)).homotopyEquiv.homotopyHomInvId.hom (n + 1) (n + 1 + 1) =
      -toSSet.cone y M (n + 1) := by
    simp [SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv, cone]; rfl
  have h0 : (((extraDegeneracy (R := R) y).map (sigmaConst.obj M)).homotopyEquiv.hom ≫
      ((extraDegeneracy (R := R) y).map (sigmaConst.obj M)).homotopyEquiv.inv).f (n + 1) = 0 := by
    simp only [SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
      HomologicalComplex.comp_f, AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_succ]
    exact zero_comp
  rw [h1, h2, h0, HomologicalComplex.id_f] at h
  exact CategoryTheory.Preadditive.comp_add_comp_eq_id _ _ _ _ h

lemma toSSet.d_comp_cone_eq_sub (y : Y) (M : C) {n : ℕ} :
    ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n =
    𝟙 _ - toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

lemma toSSet.cone_comp_d_eq_sub (y : Y) (M : C) {n : ℕ} :
    toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) =
    𝟙 _ - ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

@[reassoc (attr := simp)]
lemma toSSet.ι_cone
    (y : Y) (M : C) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ toSSet.cone (R := R) y M n =
      SSet.ιChainComplex _ (s.cone y) := by
  simp only [cone, SimplicialObject.Augmented.ExtraDegeneracy.map, SSet.ιChainComplex,
    sigmaConst_obj_map]
  exact Sigma.ι_comp_map'_const M _ s

@[reassoc]
lemma AffineMap.cone_naturality
    (φ : ConvexSpace.AffineMap R Y Z) (y : Y) (M : C) (n : ℕ) :
    (SSet.chainComplexMap φ.toSSetMap M).f n ≫ toSSet.cone (φ y) M n =
    toSSet.cone y M n ≫ (SSet.chainComplexMap φ.toSSetMap M).f (n + 1) := by
  ext x
  simp [AffineMap.comp_cone]

end ConvexSpace

end Convexity
