/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.MayerVietoris

/-!
# The Mayer–Vietoris long exact sequence

Let `A B : Set X` with `interior A ∪ interior B = Set.univ`.  The small-simplices theorem
(`TopCat.SmallSimplicesCondition.homotopyEquiv`, ported from `joelriou/excision`) says that the
inclusion `C^{A,B}_*(X) ⟶ C_*(X)` of the complex of small chains is a chain homotopy equivalence.
Combining this with the short exact sequence
`0 ⟶ C_*(A ∩ B) ⟶ C_*(A) ⊞ C_*(B) ⟶ C^{A,B}_*(X) ⟶ 0`
of `Submission/Homology/MayerVietoris.lean` gives the Mayer–Vietoris long exact sequence
```
⋯ ⟶ Hₙ(A ∩ B) ⟶ Hₙ(A) ⊞ Hₙ(B) ⟶ Hₙ(X) ⟶ Hₙ₋₁(A ∩ B) ⟶ ⋯
```

## Main definitions

* `mvSum A B n` — the group `Hₙ(A) ⊞ Hₙ(B)`;
* `mvIota A B n : Hₙ(A ∩ B) ⟶ Hₙ(A) ⊞ Hₙ(B)`, `x ↦ (x, x)`;
* `mvKappa A B n : Hₙ(A) ⊞ Hₙ(B) ⟶ Hₙ(X)`, `(x, y) ↦ x - y`;
* `mvδ A B h n : Hₙ₊₁(X) ⟶ Hₙ(A ∩ B)` — the connecting homomorphism;
* `mayerVietoris_exact_δ_iota`, `mayerVietoris_exact_iota_kappa`, `mayerVietoris_exact_kappa_δ` —
  exactness at the three spots.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

noncomputable section

namespace Submission

/-! ### An additive functor preserves binary biproducts -/

section AdditiveBiprod

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] (Y Z : C) [HasBinaryBiproduct Y Z]
  [HasBinaryBiproduct (F.obj Y) (F.obj Z)]

/-- An additive functor between preadditive categories preserves binary biproducts. -/
def additiveBiprodIso : F.obj (Y ⊞ Z) ≅ F.obj Y ⊞ F.obj Z where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;>
      refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← F.map_comp]

@[reassoc]
lemma map_lift_additiveBiprodIso {W : C} (f : W ⟶ Y) (g : W ⟶ Z) :
    F.map (biprod.lift f g) ≫ (additiveBiprodIso F Y Z).hom =
      biprod.lift (F.map f) (F.map g) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [additiveBiprodIso, ← F.map_comp]

@[reassoc]
lemma additiveBiprodIso_inv_map_desc {W : C} (f : Y ⟶ W) (g : Z ⟶ W) :
    (additiveBiprodIso F Y Z).inv ≫ F.map (biprod.desc f g) =
      biprod.desc (F.map f) (F.map g) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [additiveBiprodIso, ← F.map_comp]

end AdditiveBiprod

/-! ### The small-simplices input -/

variable {X : TopCat.{0}} (A B : Set X)

/-- If the interiors of `A` and `B` cover `X`, the family `![A, B]` satisfies the small-simplices
condition. -/
lemma mvSmallSimplicesCondition (h : interior A ∪ interior B = Set.univ) :
    TopCat.SmallSimplicesCondition (mvFamily A B) where
  iUnion_interior := by
    rw [← h]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      match i with
      | false => exact Or.inl hi
      | true => exact Or.inr hi
    · rintro (hx | hx)
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩

/-- **Small simplices compute singular homology.**  If the interiors of `A` and `B` cover `X`, the
inclusion of the complex of `{A,B}`-small chains into `C_*(X)` is a chain homotopy equivalence.
This is the excision / barycentric-subdivision input, supplied by
`TopCat.SmallSimplicesCondition.homotopyEquiv`. -/
def mvSmallHomotopyEquiv (h : interior A ∪ interior B = Set.univ) :
    HomotopyEquiv (mvSC A B).X₃ (Csing X) :=
  (mvSmallSimplicesCondition A B h).homotopyEquiv (AddCommGrpCat.of ℤ)

lemma mvSmallHomotopyEquiv_hom (h : interior A ∪ interior B = Set.univ) :
    (mvSmallHomotopyEquiv A B h).hom = mvSmallIncl A B := rfl

/-- The homology of the complex of small chains is the homology of `X`. -/
def mvSmallHomologyIso (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSC A B).X₃.homology n ≅ Hgrp n X :=
  (mvSmallHomotopyEquiv A B h).toHomologyIso n

lemma mvSmallHomologyIso_hom (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallHomologyIso A B h n).hom = HomologicalComplex.homologyMap (mvSmallIncl A B) n := rfl

/-! ### The Mayer–Vietoris maps -/

/-- The homology functor on chain complexes of abelian groups. -/
abbrev homFun (n : ℕ) : ChainComplex AddCommGrpCat.{0} ℕ ⥤ AddCommGrpCat.{0} :=
  HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.down ℕ) n

lemma homologyMap_neg {K L : ChainComplex AddCommGrpCat.{0} ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (-φ) n = -HomologicalComplex.homologyMap φ n :=
  (homFun n).map_neg

lemma biprod_desc_comp {C : Type*} [Category* C] [Preadditive C] {W Y Z T : C}
    [HasBinaryBiproduct Y Z] (f : Y ⟶ W) (g : Z ⟶ W) (k : W ⟶ T) :
    biprod.desc f g ≫ k = biprod.desc (f ≫ k) (g ≫ k) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

/-- The relation `n + 1 ⟶ n` in the chain complex shape, named so that `rw` can see it. -/
lemma mvRel (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

/-- The middle term `Hₙ(A) ⊞ Hₙ(B)` of the Mayer–Vietoris sequence. -/
abbrev mvSum (n : ℕ) : AddCommGrpCat.{0} := Hgrp n (TopCat.of A) ⊞ Hgrp n (TopCat.of B)

/-- The identification `Hₙ(C_*(A) ⊞ C_*(B)) ≅ Hₙ(A) ⊞ Hₙ(B)`. -/
def mvSumIso (n : ℕ) : (mvSC A B).X₂.homology n ≅ mvSum A B n :=
  additiveBiprodIso (homFun n) (Csing (TopCat.of A)) (Csing (TopCat.of B))

/-- The map `Hₙ(A) ⟶ Hₙ(C^{A,B}_*(X))`. -/
def mvPaH (n : ℕ) : Hgrp n (TopCat.of A) ⟶ (mvSC A B).X₃.homology n :=
  HomologicalComplex.homologyMap (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ)) n

/-- The map `Hₙ(B) ⟶ Hₙ(C^{A,B}_*(X))`. -/
def mvPbH (n : ℕ) : Hgrp n (TopCat.of B) ⟶ (mvSC A B).X₃.homology n :=
  HomologicalComplex.homologyMap (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) n

/-- The map `Hₙ(A ∩ B) ⟶ Hₙ(A) ⊞ Hₙ(B)`, `x ↦ (x, x)`. -/
def mvIota (n : ℕ) : Hgrp n (TopCat.of (A ∩ B : Set X)) ⟶ mvSum A B n :=
  biprod.lift (HgrpMap n (mvInclLeft A B)) (HgrpMap n (mvInclRight A B))

/-- The map `Hₙ(A) ⊞ Hₙ(B) ⟶ Hₙ(X)`, `(x, y) ↦ x - y`. -/
def mvKappa (n : ℕ) : mvSum A B n ⟶ Hgrp n X :=
  biprod.desc (HgrpMap n (subIncl A)) (-HgrpMap n (subIncl B))

/-- `mvIota` is the map induced on homology by `C_*(A ∩ B) ⟶ C_*(A) ⊞ C_*(B)`. -/
lemma homologyMap_mvSC_f (n : ℕ) :
    HomologicalComplex.homologyMap (mvSC A B).f n ≫ (mvSumIso A B n).hom = mvIota A B n :=
  map_lift_additiveBiprodIso (homFun n) _ _ _ _

lemma mvPaH_comp (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvPaH A B n ≫ (mvSmallHomologyIso A B h n).hom = HgrpMap n (subIncl A) := by
  show HomologicalComplex.homologyMap (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ)) n ≫
      HomologicalComplex.homologyMap (mvSmallIncl A B) n = HgrpMap n (subIncl A)
  rw [← HomologicalComplex.homologyMap_comp, mvPa_smallIncl]
  rfl

lemma mvPbH_comp (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvPbH A B n ≫ (mvSmallHomologyIso A B h n).hom = HgrpMap n (subIncl B) := by
  show HomologicalComplex.homologyMap (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) n ≫
      HomologicalComplex.homologyMap (mvSmallIncl A B) n = HgrpMap n (subIncl B)
  rw [← HomologicalComplex.homologyMap_comp, mvPb_smallIncl]
  rfl

lemma mvSumIso_inv_comp (n : ℕ) :
    (mvSumIso A B n).inv ≫ HomologicalComplex.homologyMap (mvSC A B).g n =
      biprod.desc (mvPaH A B n) (-mvPbH A B n) := by
  have key := additiveBiprodIso_inv_map_desc (homFun n) (Csing (TopCat.of A))
    (Csing (TopCat.of B)) (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ))
    (-SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
  refine key.trans ?_
  congr 1
  exact (homFun n).map_neg

/-- `mvKappa` is the map induced on homology by `C_*(A) ⊞ C_*(B) ⟶ C^{A,B}_*(X)`, followed by the
identification of the homology of small chains with `Hₙ(X)`. -/
lemma homologyMap_mvSC_g (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSumIso A B n).hom ≫ mvKappa A B n =
      HomologicalComplex.homologyMap (mvSC A B).g n ≫ (mvSmallHomologyIso A B h n).hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, mvSumIso_inv_comp, biprod_desc_comp,
    Preadditive.neg_comp, mvPaH_comp, mvPbH_comp]
  rfl

/-! ### The connecting homomorphism -/

/-- The Mayer–Vietoris connecting homomorphism `∂ : Hₙ₊₁(X) ⟶ Hₙ(A ∩ B)`. -/
def mvδ (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    Hgrp (n + 1) X ⟶ Hgrp n (TopCat.of (A ∩ B : Set X)) :=
  (mvSmallHomologyIso A B h (n + 1)).inv ≫ (mvSC_shortExact A B).δ (n + 1) n (mvRel n)

lemma mvSmallHomologyIso_hom_comp_mvδ (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (mvSmallHomologyIso A B h (n + 1)).hom ≫ mvδ A B h n =
      (mvSC_shortExact A B).δ (n + 1) n (mvRel n) :=
  Iso.hom_inv_id_assoc _ _

/-! ### The three composites vanish -/

lemma mvIota_comp_mvKappa (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvIota A B n ≫ mvKappa A B n = 0 := by
  have key : HomologicalComplex.homologyMap (mvSC A B).f n ≫
      ((mvSumIso A B n).hom ≫ mvKappa A B n) = 0 := by
    rw [homologyMap_mvSC_g A B h, ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      (mvSC A B).zero, HomologicalComplex.homologyMap_zero, zero_comp]
  rw [← homologyMap_mvSC_f]
  exact (Category.assoc _ _ _).trans key

lemma mvδ_comp_mvIota (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvδ A B h n ≫ mvIota A B n = 0 := by
  have key : ((mvSmallHomologyIso A B h (n + 1)).inv ≫
      (mvSC_shortExact A B).δ (n + 1) n (mvRel n)) ≫
      (HomologicalComplex.homologyMap (mvSC A B).f n ≫ (mvSumIso A B n).hom) = 0 := by
    simp
  rw [← homologyMap_mvSC_f]
  exact key

lemma mvKappa_comp_mvδ (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    mvKappa A B (n + 1) ≫ mvδ A B h n = 0 := by
  have key : HomologicalComplex.homologyMap (mvSC A B).g (n + 1) ≫
      ((mvSmallHomologyIso A B h (n + 1)).hom ≫ mvδ A B h n) = 0 := by
    rw [mvSmallHomologyIso_hom_comp_mvδ]
    exact (mvSC_shortExact A B).comp_δ _ _ _
  refine (cancel_epi (mvSumIso A B (n + 1)).hom).1 ?_
  rw [comp_zero]
  calc (mvSumIso A B (n + 1)).hom ≫ mvKappa A B (n + 1) ≫ mvδ A B h n
      = ((mvSumIso A B (n + 1)).hom ≫ mvKappa A B (n + 1)) ≫ mvδ A B h n :=
        (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap (mvSC A B).g (n + 1) ≫
          (mvSmallHomologyIso A B h (n + 1)).hom) ≫ mvδ A B h n :=
        congrArg (fun z => z ≫ mvδ A B h n) (homologyMap_mvSC_g A B h (n + 1))
    _ = 0 := (Category.assoc _ _ _).trans key

/-! ### Exactness -/

/-- **Mayer–Vietoris, exactness at `Hₙ(A ∩ B)`:**
`Hₙ₊₁(X) ⟶ Hₙ(A ∩ B) ⟶ Hₙ(A) ⊞ Hₙ(B)`. -/
theorem mayerVietoris_exact_δ_iota (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvδ A B h n) (mvIota A B n) (mvδ_comp_mvIota A B h n)).Exact := by
  have hex := (mvSC_shortExact A B).homology_exact₁ (n + 1) n (mvRel n)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (mvSmallHomologyIso A B h (n + 1)) (Iso.refl _) (mvSumIso A B n)
    ?_ ?_
  · exact (mvSmallHomologyIso_hom_comp_mvδ A B h n).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (homologyMap_mvSC_f A B n).symm

/-- **Mayer–Vietoris, exactness at `Hₙ(A) ⊞ Hₙ(B)`:**
`Hₙ(A ∩ B) ⟶ Hₙ(A) ⊞ Hₙ(B) ⟶ Hₙ(X)`. -/
theorem mayerVietoris_exact_iota_kappa (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvIota A B n) (mvKappa A B n) (mvIota_comp_mvKappa A B h n)).Exact := by
  have hex := (mvSC_shortExact A B).homology_exact₂ n
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (Iso.refl _) (mvSumIso A B n) (mvSmallHomologyIso A B h n) ?_ ?_
  · exact (Category.id_comp _).trans (homologyMap_mvSC_f A B n).symm
  · exact homologyMap_mvSC_g A B h n

/-- **Mayer–Vietoris, exactness at `Hₙ₊₁(X)`:**
`Hₙ₊₁(A) ⊞ Hₙ₊₁(B) ⟶ Hₙ₊₁(X) ⟶ Hₙ(A ∩ B)`. -/
theorem mayerVietoris_exact_kappa_δ (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvKappa A B (n + 1)) (mvδ A B h n) (mvKappa_comp_mvδ A B h n)).Exact := by
  have hex := (mvSC_shortExact A B).homology_exact₃ (n + 1) n (mvRel n)
  refine ShortComplex.exact_of_iso ?_ hex
  refine ShortComplex.isoMk (mvSumIso A B (n + 1)) (mvSmallHomologyIso A B h (n + 1)) (Iso.refl _)
    ?_ ?_
  · exact homologyMap_mvSC_g A B h (n + 1)
  · exact (mvSmallHomologyIso_hom_comp_mvδ A B h n).trans (Category.comp_id _).symm

end Submission
