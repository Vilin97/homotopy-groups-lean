/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.SimplicialSplitting
import Submission.Homology.LesTools
import Submission.Excision.SmallSimplices

/-!
# The Mayer–Vietoris short exact sequence of singular chain complexes

Let `A B : Set X` be two subsets of a topological space.  Write `C^{A,B}_*(X)` for the subcomplex
of `C_*(X)` spanned by the singular simplices whose image lies in `A` or in `B` (this is
`CsingSSet (mvSubcomplex A B)`, the chain complex of the simplicial subcomplex
`TopCat.toSSet.subcomplexOfSets ![A, B]` of the singular simplicial set of `X`).  This file proves
that
```
0 ⟶ C_*(A ∩ B) ⟶ C_*(A) ⊞ C_*(B) ⟶ C^{A,B}_*(X) ⟶ 0
```
is a short exact sequence of chain complexes, by instantiating the abstract degreewise splitting of
`Submission/Homology/SimplicialSplitting.lean`.

No hypothesis on `A` and `B` is needed here — that comes in only when one wants to replace
`C^{A,B}_*(X)` by `C_*(X)`, which is the small-simplices theorem (see
`Submission/Homology/MayerVietorisLES.lean`).

## Main definitions

* `mvSubcomplex A B` — the simplicial subcomplex of small simplices;
* `mvSmallComplex A B` — the chain complex `C^{A,B}_*(X)`;
* `mvSmallIncl A B : mvSmallComplex A B ⟶ Csing X` — the inclusion;
* `mvSC A B` — the Mayer–Vietoris short complex;
* `mvSC_shortExact A B` — it is short exact.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not, and without
-- it `rw`/`simp` fail on goals that are not type-correct at `instances` transparency.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X)

/-! ### The subcomplex of small simplices -/

/-- The two subsets `A` and `B`, packaged as a family indexed by `Bool`. -/
def mvFamily : Bool → Set X := Bool.rec A B

@[simp] lemma mvFamily_false : mvFamily A B false = A := rfl
@[simp] lemma mvFamily_true : mvFamily A B true = B := rfl

/-- The subcomplex `S^{A,B}` of the singular simplicial set of `X` spanned by the simplices whose
image lies entirely in `A` or entirely in `B`. -/
def mvSubcomplex : (TopCat.toSSet.obj X).Subcomplex :=
  TopCat.toSSet.subcomplexOfSets (mvFamily A B)

lemma mvSubcomplex_eq_sup :
    mvSubcomplex A B = TopCat.toSSet.subcomplexOfSet A ⊔ TopCat.toSSet.subcomplexOfSet B :=
  TopCat.toSSet.subcomplexOfSets_bool _

lemma subcomplexOfSet_le_mvSubcomplex_left :
    TopCat.toSSet.subcomplexOfSet A ≤ mvSubcomplex A B := by
  rw [mvSubcomplex_eq_sup]; exact le_sup_left

lemma subcomplexOfSet_le_mvSubcomplex_right :
    TopCat.toSSet.subcomplexOfSet B ≤ mvSubcomplex A B := by
  rw [mvSubcomplex_eq_sup]; exact le_sup_right

/-- The chain complex `C^{A,B}_*(X)` of small chains. -/
abbrev mvSmallComplex : ChainComplex AddCommGrpCat.{0} ℕ := CsingSSet (mvSubcomplex A B)

/-- The inclusion `C^{A,B}_*(X) ⟶ C_*(X)`. -/
def mvSmallIncl : mvSmallComplex A B ⟶ Csing X :=
  SSet.chainComplexMap (mvSubcomplex A B).ι (AddCommGrpCat.of ℤ)

/-! ### The four spaces and the maps between them -/

/-- The inclusion `A ∩ B ⟶ A`. -/
def mvInclLeft : TopCat.of (A ∩ B : Set X) ⟶ TopCat.of A :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left)

/-- The inclusion `A ∩ B ⟶ B`. -/
def mvInclRight : TopCat.of (A ∩ B : Set X) ⟶ TopCat.of B :=
  TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_right)

@[simp] lemma mvInclLeft_comp : mvInclLeft A B ≫ subIncl A = subIncl (A ∩ B) := rfl
@[simp] lemma mvInclRight_comp : mvInclRight A B ≫ subIncl B = subIncl (A ∩ B) := rfl

/-- `Sing(A ∩ B) ⟶ Sing A`. -/
abbrev mvQa : TopCat.toSSet.obj (TopCat.of (A ∩ B : Set X)) ⟶
    TopCat.toSSet.obj (TopCat.of A) := TopCat.toSSet.map (mvInclLeft A B)

/-- `Sing(A ∩ B) ⟶ Sing B`. -/
abbrev mvQb : TopCat.toSSet.obj (TopCat.of (A ∩ B : Set X)) ⟶
    TopCat.toSSet.obj (TopCat.of B) := TopCat.toSSet.map (mvInclRight A B)

/-- `Sing A ⟶ S^{A,B}`. -/
def mvPa : TopCat.toSSet.obj (TopCat.of A) ⟶ (mvSubcomplex A B : SSet.{0}) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (subIncl A)) (subcomplexOfSet_le_mvSubcomplex_left A B)

/-- `Sing B ⟶ S^{A,B}`. -/
def mvPb : TopCat.toSSet.obj (TopCat.of B) ⟶ (mvSubcomplex A B : SSet.{0}) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (subIncl B)) (subcomplexOfSet_le_mvSubcomplex_right A B)

@[reassoc (attr := simp)]
lemma mvPa_ι : mvPa A B ≫ (mvSubcomplex A B).ι = TopCat.toSSet.map (subIncl A) := rfl

@[reassoc (attr := simp)]
lemma mvPb_ι : mvPb A B ≫ (mvSubcomplex A B).ι = TopCat.toSSet.map (subIncl B) := rfl

/-! ### Injectivity -/

/-- If `f` is injective then so is every component of `Sing f`. -/
lemma injective_toSSet_map_app {Y Z : TopCat.{0}} (f : Y ⟶ Z) (hf : Function.Injective f)
    (n : ℕ) : Function.Injective ((TopCat.toSSet.map f).app (op ⦋n⦌)) := by
  have hm : Mono f := by rw [TopCat.mono_iff_injective]; exact hf
  have h : Mono (TopCat.toSSet.map f) := Functor.map_mono _ _
  rw [NatTrans.mono_iff_mono_app] at h
  exact (CategoryTheory.mono_iff_injective _).1 (h _)

lemma injective_mvQb_app (n : ℕ) : Function.Injective ((mvQb A B).app (op ⦋n⦌)) := by
  refine injective_toSSet_map_app _ (fun u v h => ?_) n
  have h' : (u : X) = (v : X) := congrArg (fun w : (B : Set X) => (w : X)) h
  exact Subtype.ext h'

lemma injective_mvPa_app (n : ℕ) : Function.Injective ((mvPa A B).app (op ⦋n⦌)) := by
  intro u v h
  exact injective_toSSet_map_app (subIncl A) Subtype.val_injective n (congrArg Subtype.val h)

lemma injective_mvPb_app (n : ℕ) : Function.Injective ((mvPb A B).app (op ⦋n⦌)) := by
  intro u v h
  exact injective_toSSet_map_app (subIncl B) Subtype.val_injective n (congrArg Subtype.val h)

/-! ### The Mayer–Vietoris short complex -/

lemma mvQa_comp_mvPa : mvQa A B ≫ mvPa A B = mvQb A B ≫ mvPb A B := by
  refine (cancel_mono (mvSubcomplex A B).ι).1 ?_
  rw [Category.assoc, Category.assoc, mvPa_ι, mvPb_ι, ← Functor.map_comp, ← Functor.map_comp,
    mvInclLeft_comp, mvInclRight_comp]

/-- The Mayer–Vietoris short complex
`C_*(A ∩ B) ⟶ C_*(A) ⊞ C_*(B) ⟶ C^{A,B}_*(X)`. -/
def mvSC : ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ) :=
  mvShortComplex (mvQa A B) (mvQb A B) (mvPa A B) (mvPb A B) (mvQa_comp_mvPa A B)

lemma mvSC_X₃ : (mvSC A B).X₃ = mvSmallComplex A B := rfl

lemma mvSC_f_eq : (mvSC A B).f =
    biprod.lift (SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap (mvQb A B) (AddCommGrpCat.of ℤ)) := rfl

lemma mvSC_g_eq : (mvSC A B).g =
    biprod.desc (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ))
      (-SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) := rfl

lemma mvSmallIncl_def :
    mvSmallIncl A B = SSet.chainComplexMap (mvSubcomplex A B).ι (AddCommGrpCat.of ℤ) := rfl

lemma mvPa_smallIncl :
    SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ) ≫ mvSmallIncl A B =
      CsingMap (subIncl A) :=
  (((SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map_comp
    (mvPa A B) (mvSubcomplex A B).ι).symm

lemma mvPb_smallIncl :
    SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ) ≫ mvSmallIncl A B =
      CsingMap (subIncl B) :=
  (((SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map_comp
    (mvPb A B) (mvSubcomplex A B).ι).symm

/-- Every small simplex comes from `A` or from `B`. -/
lemma mvCover (n : ℕ) (d : (mvSubcomplex A B : SSet.{0}) _⦋n⦌) :
    (∃ x, (mvPa A B).app (op ⦋n⦌) x = d) ∨ (∃ y, (mvPb A B).app (op ⦋n⦌) y = d) := by
  obtain ⟨i, t, ht⟩ := (TopCat.toSSet.mem_subcomplexOfSets_iff' (U := mvFamily A B) d.1).1 d.2
  match i with
  | false => exact Or.inl ⟨t, Subtype.ext ht⟩
  | true => exact Or.inr ⟨t, Subtype.ext ht⟩

/-- A simplex lying both in `A` and in `B` lies in `A ∩ B`. -/
lemma mvInter (n : ℕ) (x : TopCat.toSSet.obj (TopCat.of A) _⦋n⦌)
    (y : TopCat.toSSet.obj (TopCat.of B) _⦋n⦌)
    (hxy : (mvPa A B).app (op ⦋n⦌) x = (mvPb A B).app (op ⦋n⦌) y) :
    ∃ z, (mvQb A B).app (op ⦋n⦌) z = y := by
  have hval : (TopCat.toSSet.map (subIncl A)).app (op ⦋n⦌) x =
      (TopCat.toSSet.map (subIncl B)).app (op ⦋n⦌) y := congrArg Subtype.val hxy
  have hmemA : (TopCat.toSSet.map (subIncl B)).app (op ⦋n⦌) y ∈
      (TopCat.toSSet.subcomplexOfSet A).obj (op ⦋n⦌) := ⟨x, hval⟩
  have hmemB : (TopCat.toSSet.map (subIncl B)).app (op ⦋n⦌) y ∈
      (TopCat.toSSet.subcomplexOfSet B).obj (op ⦋n⦌) := ⟨y, rfl⟩
  have hmem : (TopCat.toSSet.map (subIncl B)).app (op ⦋n⦌) y ∈
      (TopCat.toSSet.subcomplexOfSet (A ∩ B)).obj (op ⦋n⦌) := by
    rw [TopCat.toSSet.subcomplexOfSet_inter]
    exact ⟨hmemA, hmemB⟩
  obtain ⟨z, hz⟩ := hmem
  have hcomp : mvQb A B ≫ TopCat.toSSet.map (subIncl B) =
      TopCat.toSSet.map (subIncl (A ∩ B)) := by
    rw [← Functor.map_comp, mvInclRight_comp]
  refine ⟨z, injective_toSSet_map_app (subIncl B) Subtype.val_injective n ?_⟩
  rw [← hz]
  exact congrArg (fun (φ : TopCat.toSSet.obj (TopCat.of (A ∩ B : Set X)) ⟶ TopCat.toSSet.obj X) =>
    (ConcreteCategory.hom (NatTrans.app φ (op ⦋n⦌))) z) hcomp

/-- **The Mayer–Vietoris short exact sequence of chain complexes.**
`0 ⟶ C_*(A ∩ B) ⟶ C_*(A) ⊞ C_*(B) ⟶ C^{A,B}_*(X) ⟶ 0`. -/
theorem mvSC_shortExact : (mvSC A B).ShortExact :=
  mvShortComplex_shortExact (mvQa_comp_mvPa A B) (injective_mvQb_app A B)
    (injective_mvPa_app A B) (injective_mvPb_app A B) (mvCover A B) (mvInter A B)

/-- The explicit degreewise splitting underlying `mvSC_shortExact`.  Naming this splitting lets
contravariant additive functors, in particular `Hom(-, G)`, reuse the stronger input rather than
only the resulting short exactness. -/
def mvSCSplitting (n : ℕ) : ShortComplex.Splitting
    ((mvSC A B).map
      (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n)) :=
  mvSplitting (mvQa A B) (mvQb A B) (mvPa A B) (mvPb A B) (mvQa_comp_mvPa A B) n
    (injective_mvQb_app A B n) (injective_mvPa_app A B n) (injective_mvPb_app A B n)
    (mvCover A B n) (mvInter A B n)

end Submission
