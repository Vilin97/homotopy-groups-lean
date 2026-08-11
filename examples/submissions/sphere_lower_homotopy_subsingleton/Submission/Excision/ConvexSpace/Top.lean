/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Submission.Excision.ConvexSpace.ToSSet

/-!
# ...

-/

@[expose] public section

universe w

open CategoryTheory Opposite Simplicial

-- Reducibility attribute needed because `rw`/`erw` match at `instances` transparency and
-- `CosimplicialObject C` is a `def` for `SimplexCategory ⥤ C`.
attribute [local implicit_reducible] CategoryTheory.CosimplicialObject
  SimplexCategory.toTop₀

lemma TopCat.toSSet_map_app_toSSetObjEquiv_symm
    {Y Z : TopCat.{w}} (f : Y ⟶ Z) {n : ℕ}
    (x : C(stdSimplex ℝ (Fin (n + 1)), Y)) :
    (toSSet.map f).app (op ⦋n⦌) ((toSSetObjEquiv _ _).symm x) =
    (toSSetObjEquiv _ _).symm (f.hom.comp x) := rfl

namespace stdSimplex

@[fun_prop]
lemma continuous_apply {ι : Type*} [Fintype ι] (i : ι) :
    Continuous (fun (s : stdSimplex ℝ ι) ↦ s i) :=
  (_root_.continuous_apply i).comp continuous_subtype_val

lemma total {ι : Type*} [Fintype ι] (s : stdSimplex ℝ ι) :
    ∑ (i : ι), s i = 1 := s.2.2

lemma apply_nonneg {ι : Type*} [Fintype ι] (x : stdSimplex ℝ ι) (i : ι) :
    0 ≤ x i :=
  x.2.1 i

@[simp]
lemma map_id {ι : Type*} [Fintype ι] :
    stdSimplex.map (S := ℝ) (id : ι → ι) = id := by
  aesop

end stdSimplex

namespace Convexity

/-- The inclusion of `StdSimplex ℝ α` to `α → ℝ`, as an affine map. -/
@[simps]
def StdSimplex.ι {α : Type*} :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ α) (α → ℝ) where
  toFun s := s.weights
  isAffineMap_toFun.map_sConvexComb s := by
    ext i
    induction s using StdSimplex.rec' with
    | sum n w m hw₀ hw =>
      dsimp
      simp only [weights_sConvexComb, Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, iConvexComb_eq_sum, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single]
      rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_mul]),
        Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_mul])]
      congr
      simp

-- TODO: remove `stdSimplex`?
/-- The bijection between `StdSimplex ℝ ι` and `stdSimplex ℝ ι`. -/
@[simps]
noncomputable def StdSimplex.equiv
    {R ι : Type*} [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R] [Fintype ι] :
    StdSimplex R ι ≃ stdSimplex R ι where
  toFun s := ⟨s.weights, s.nonneg, by
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this ⟩
  invFun s :=
    { weights := ∑ (i : ι), .single i (s i)
      nonneg := Finset.sum_nonneg (by simp)
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        rw [← s.2.2]
        congr
        ext i
        rw [Finset.sum_eq_single i (by aesop) (by simp)]
        simp
        rfl }
  left_inv s := by
    ext i
    dsimp
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ Finsupp.single_eq_of_ne' hj) (by simp),
      Finsupp.single_eq_same]
    rfl
  right_inv s := by
    ext i
    change (∑ (i : ι), Finsupp.single i (s i)) i = s i
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single i (by aesop) (by simp)]
    simp

@[simp]
lemma StdSimplex.equiv_apply_apply
    {R ι : Type*} [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R] [Fintype ι]
    (s : StdSimplex R ι) (i : ι) :
    equiv s i = s.weights i := by
  rfl

private lemma StdSimplex.equiv_comp_affineMapMk_comp_equiv_symm
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f : ι₁ → StdSimplex ℝ ι₂) :
    equiv ∘ ⇑(StdSimplex.affineMapMk (R := ℝ) f) ∘ equiv.symm =
      fun s ↦ ⟨∑ (i : ι₁), s i • (f i).weights,
        fun i₂ ↦ by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_nonneg'
            (fun i ↦ mul_nonneg (stdSimplex.apply_nonneg _ _) (by simp)), by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_comm, ← stdSimplex.total s]
          congr
          ext i₁
          have := (f i₁).total
          rw [Finsupp.sum_fintype _ _ (by simp)] at this
          rw [← Finset.mul_sum, this, mul_one]⟩ := by
  ext s : 1
  obtain ⟨g, rfl⟩ := equiv.surjective s
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  have := DFunLike.congr_fun (comp_affineMapMk ι f) g
  dsimp at this
  change StdSimplex.ι (affineMapMk f g) = _
  rw [this, affineMapMk_apply_eq_sum]
  simp
  rfl

/-- The continuous map in `C(stdSimplex ℝ ι₁, stdSimplex ℝ ι₂)` that is given
by an affine map from `StdSimplex ℝ ι₁` to `StdSimplex ℝ ι₂`. -/
noncomputable def ConvexSpace.AffineMap.toContinuousMap
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    C(stdSimplex ℝ ι₁, stdSimplex ℝ ι₂) where
  toFun := StdSimplex.equiv ∘ s ∘ StdSimplex.equiv.symm
  continuous_toFun := by
    obtain ⟨f, rfl⟩ := StdSimplex.affineMapMk_surjective s
    rw [StdSimplex.equiv_comp_affineMapMk_comp_equiv_symm]
    fun_prop

lemma ConvexSpace.AffineMap.toContinuousMap_comp
    {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₂) (StdSimplex ℝ ι₃))
    (t : ConvexSpace.AffineMap ℝ (StdSimplex ℝ ι₁) (StdSimplex ℝ ι₂)) :
    (s.comp t).toContinuousMap = s.toContinuousMap.comp t.toContinuousMap := by
  ext
  simp [toContinuousMap]

open Classical in
@[simp]
lemma StdSimplex.equiv_map
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (f : ι₁ → ι₂)
    (s : StdSimplex ℝ ι₁) :
    equiv (map f s) = stdSimplex.map f (equiv s) := by
  ext i₂
  simp only [equiv_apply_apply, weights_map, Finsupp.mapDomain, Finsupp.single_zero,
    implies_true, Finsupp.sum_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [← Finset.sum_add_sum_compl { x | f x = i₂}]
  nth_rw 2 [Finset.sum_eq_zero (by aesop)]
  rw [add_zero]
  exact Finset.sum_congr rfl (by aesop)

@[simp]
lemma StdSimplex.affineMap_toContinuousMap
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (f : ι₁ → ι₂) :
    ⇑(affineMap f).toContinuousMap = stdSimplex.map f := by
  ext s : 1
  obtain ⟨s, rfl⟩ := equiv.surjective s
  simp [ConvexSpace.AffineMap.toContinuousMap]

@[simp]
lemma ConvexSpace.AffineMap.toContinuousMap_id
    (ι : Type*) [Fintype ι] :
    (ConvexSpace.AffineMap.id (StdSimplex ℝ ι)).toContinuousMap = .id _ :=
  DFunLike.ext'
    (by simpa using StdSimplex.affineMap_toContinuousMap (_root_.id : ι → ι))

/-- The inclusion of affine maps into continuous maps between standard simplices,
as a morphism of simplicial sets. -/
noncomputable def StdSimplex.toSSetNatTrans (ι : Type*) [Fintype ι] :
    ConvexSpace.toSSet ℝ (StdSimplex ℝ ι) ⟶
      TopCat.toSSet.obj (.of (stdSimplex ℝ ι)) where
  app _ := ↾((TopCat.toSSetObjEquiv _ _).symm ∘ ConvexSpace.AffineMap.toContinuousMap)
  naturality n m f := by
    ext s
    apply (TopCat.toSSetObjEquiv _ _).injective
    dsimp
    apply DFunLike.ext'
    change (s.comp (affineMap f.unop)).toContinuousMap.toFun = _
    rw [ConvexSpace.AffineMap.toContinuousMap_comp]
    dsimp
    rw [StdSimplex.affineMap_toContinuousMap]
    rfl

@[simp]
lemma StdSimplex.toSSetNatTrans_app_apply {n : ℕ} {ι : Type*} [Fintype ι]
    (x : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ ι)) :
    (StdSimplex.toSSetNatTrans ι).app (op ⦋n⦌) x =
      (TopCat.toSSetObjEquiv _ _).symm x.toContinuousMap := rfl

@[reassoc]
lemma StdSimplex.toSSetNatTrans_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (StdSimplex.affineMap f).toSSetMap ≫ StdSimplex.toSSetNatTrans _ =
    StdSimplex.toSSetNatTrans _ ≫
      TopCat.toSSet.map (SimplexCategory.toTop₀.map f) := by
  ext ⟨⟨k⟩⟩ g
  dsimp at g ⊢
  rw [StdSimplex.toSSetNatTrans_app_apply,
    StdSimplex.toSSetNatTrans_app_apply,
    TopCat.toSSet_map_app_toSSetObjEquiv_symm]
  congr 1
  erw [ConvexSpace.AffineMap.toContinuousMap_comp]
  congr 1
  exact DFunLike.ext' (StdSimplex.affineMap_toContinuousMap _)

end Convexity

open Convexity

namespace TopCat

lemma δ_toSSetObjEquiv_symm {X : TopCat} {n : ℕ}
    (x : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (toSSet.obj X).δ i ((toSSetObjEquiv _ _).symm x) =
    (toSSetObjEquiv _ _).symm (x.comp
      (Convexity.StdSimplex.affineMap i.succAbove).toContinuousMap) := by
  trans (toSSetObjEquiv _ _).symm (x.comp ⟨_, stdSimplex.continuous_map i.succAbove⟩)
  · rfl
  · congr 2
    exact DFunLike.ext' (StdSimplex.affineMap_toContinuousMap _).symm

end TopCat
