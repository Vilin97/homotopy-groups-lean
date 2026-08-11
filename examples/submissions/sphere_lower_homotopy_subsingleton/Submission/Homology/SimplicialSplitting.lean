/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Pair
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# The degreewise splitting behind the Mayer–Vietoris short exact sequence

This file contains the purely combinatorial heart of Mayer–Vietoris.  Suppose we are given four
simplicial sets and four maps
```
G --qa--> Sa --pa--> D ,   G --qb--> Sb --pb--> D
```
which, in each degree, exhibit `D` as the union of (the images of) `Sa` and `Sb`, with `G` the
intersection.  Then the sequence of chain complexes
```
0 ⟶ ℤ[G] ⟶ ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D] ⟶ 0 ,
  z ↦ (qa z, qb z) ,   (x, y) ↦ pa x - pb y
```
is short exact, because it is *degreewise split*: in each degree the three groups are free on the
relevant sets of simplices, and one can split by choosing, for every simplex of `D`, a preimage in
`Sa` if there is one and in `Sb` otherwise.

## Main definitions

* `mvShortComplex` — the short complex `ℤ[G] ⟶ ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D]`;
* `mvSplitting` — the degreewise splitting;
* `mvShortComplex_shortExact` — short exactness.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not, and without
-- it `rw`/`simp` fail on goals that are not type-correct at `instances` transparency.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor

noncomputable section

namespace Submission

/-- The chain complex of a simplicial set with `ℤ` coefficients, in `AddCommGrpCat`. -/
abbrev CsingSSet (Y : SSet.{0}) : ChainComplex AddCommGrpCat.{0} ℕ :=
  Y.chainComplex (AddCommGrpCat.of ℤ)

/-- A map out of the degree `n` part of `CsingSSet Y`, prescribed on the generators. -/
def ccDesc {Y : SSet.{0}} {n : ℕ} {T : AddCommGrpCat.{0}}
    (v : Y _⦋n⦌ → (AddCommGrpCat.of ℤ ⟶ T)) : (CsingSSet Y).X n ⟶ T :=
  Cofan.IsColimit.desc (Y.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n) v

@[reassoc (attr := simp)]
lemma ι_ccDesc {Y : SSet.{0}} {n : ℕ} {T : AddCommGrpCat.{0}}
    (v : Y _⦋n⦌ → (AddCommGrpCat.of ℤ ⟶ T)) (y : Y _⦋n⦌) :
    Y.ιChainComplex y ≫ ccDesc v = v y :=
  Cofan.IsColimit.fac _ _ _

section

variable {G Sa Sb D : SSet.{0}} (qa : G ⟶ Sa) (qb : G ⟶ Sb) (pa : Sa ⟶ D) (pb : Sb ⟶ D)

/-- The Mayer–Vietoris short complex `ℤ[G] ⟶ ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D]`. -/
def mvShortComplex (h : qa ≫ pa = qb ≫ pb) : ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ) :=
  ShortComplex.mk
    (biprod.lift (SSet.chainComplexMap qa (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap qb (AddCommGrpCat.of ℤ)))
    (biprod.desc (SSet.chainComplexMap pa (AddCommGrpCat.of ℤ))
      (-SSet.chainComplexMap pb (AddCommGrpCat.of ℤ)))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp, h,
        add_neg_cancel])

@[simp]
lemma mvShortComplex_X₁ (h : qa ≫ pa = qb ≫ pb) :
    (mvShortComplex qa qb pa pb h).X₁ = CsingSSet G := rfl

@[simp]
lemma mvShortComplex_X₃ (h : qa ≫ pa = qb ≫ pb) :
    (mvShortComplex qa qb pa pb h).X₃ = CsingSSet D := rfl

/-- The degreewise retraction of `ℤ[G] ⟶ ℤ[Sb]`: a simplex of `Sb` in the image of `G` is sent
back to its (unique) preimage, and all other simplices are sent to `0`. -/
def mvRetr (n : ℕ) : (CsingSSet Sb).X n ⟶ (CsingSSet G).X n :=
  open scoped Classical in
  ccDesc fun y =>
    if h : ∃ z, qb.app (op ⦋n⦌) z = y then G.ιChainComplex h.choose else 0

@[reassoc]
lemma ι_mvRetr {n : ℕ} (hqb : Function.Injective (qb.app (op ⦋n⦌))) (z : G _⦋n⦌) :
    Sb.ιChainComplex (R := AddCommGrpCat.of ℤ) (qb.app _ z) ≫ mvRetr qb n =
      G.ιChainComplex z := by
  classical
  rw [mvRetr, ι_ccDesc, dif_pos ⟨z, rfl⟩]
  congr 1
  exact hqb (Exists.choose_spec (⟨z, rfl⟩ : ∃ w, qb.app (op ⦋n⦌) w = qb.app _ z))

@[reassoc]
lemma ι_mvRetr_of_not_mem {n : ℕ} (y : Sb _⦋n⦌) (h : ¬ ∃ z, qb.app (op ⦋n⦌) z = y) :
    Sb.ιChainComplex (R := AddCommGrpCat.of ℤ) y ≫ mvRetr qb n = 0 := by
  classical
  rw [mvRetr, ι_ccDesc, dif_neg h]

variable {qa qb pa pb} in
/-- The degreewise section of `ℤ[Sa] ⊞ ℤ[Sb] ⟶ ℤ[D]`: a simplex of `D` coming from `Sa` is sent
to its preimage in the first summand, and a simplex coming only from `Sb` is sent to minus its
preimage in the second summand. -/
def mvSect {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d)) :
    (CsingSSet D).X n ⟶ (CsingSSet Sa ⊞ CsingSSet Sb).X n :=
  open scoped Classical in
  ccDesc fun d =>
    if h : ∃ x, pa.app (op ⦋n⦌) x = d then
      Sa.ιChainComplex h.choose ≫ (biprod.inl : CsingSSet Sa ⟶ _).f n
    else
      -(Sb.ιChainComplex ((hcover d).resolve_left h).choose ≫
        (biprod.inr : CsingSSet Sb ⟶ _).f n)

variable {qa qb pa pb}

@[reassoc]
lemma ι_mvSect_of_mem {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpa : Function.Injective (pa.app (op ⦋n⦌))) (x : Sa _⦋n⦌) :
    D.ιChainComplex (R := AddCommGrpCat.of ℤ) (pa.app _ x) ≫ mvSect hcover =
      Sa.ιChainComplex x ≫ (biprod.inl : CsingSSet Sa ⟶ _).f n := by
  classical
  rw [mvSect, ι_ccDesc, dif_pos ⟨x, rfl⟩]
  congr 2
  exact hpa (Exists.choose_spec (⟨x, rfl⟩ : ∃ w, pa.app (op ⦋n⦌) w = pa.app _ x))

@[reassoc]
lemma ι_mvSect_of_not_mem {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpb : Function.Injective (pb.app (op ⦋n⦌))) (y : Sb _⦋n⦌)
    (h : ¬ ∃ x, pa.app (op ⦋n⦌) x = pb.app _ y) :
    D.ιChainComplex (R := AddCommGrpCat.of ℤ) (pb.app _ y) ≫ mvSect hcover =
      -(Sb.ιChainComplex y ≫ (biprod.inr : CsingSSet Sb ⟶ _).f n) := by
  classical
  rw [mvSect, ι_ccDesc, dif_neg h]
  congr 3
  exact hpb (Exists.choose_spec (((hcover (pb.app _ y)).resolve_left h)))

@[reassoc]
lemma ι_mvLift {n : ℕ} (z : G _⦋n⦌) :
    G.ιChainComplex (R := AddCommGrpCat.of ℤ) z ≫
        (biprod.lift (SSet.chainComplexMap qa (AddCommGrpCat.of ℤ))
          (SSet.chainComplexMap qb (AddCommGrpCat.of ℤ))).f n =
      Sa.ιChainComplex (qa.app _ z) ≫ (biprod.inl : CsingSSet Sa ⟶ _).f n +
        Sb.ιChainComplex (qb.app _ z) ≫ (biprod.inr : CsingSSet Sb ⟶ _).f n := by
  rw [biprod.lift_eq]
  simp [HomologicalComplex.add_f_apply]

/-- `mvRetr` is a retraction of the first map of the Mayer–Vietoris short complex. -/
lemma mvLift_comp_mvRetr {n : ℕ} (hqb : Function.Injective (qb.app (op ⦋n⦌))) :
    (biprod.lift (SSet.chainComplexMap qa (AddCommGrpCat.of ℤ))
        (SSet.chainComplexMap qb (AddCommGrpCat.of ℤ))).f n ≫
      ((biprod.snd : CsingSSet Sa ⊞ CsingSSet Sb ⟶ _).f n ≫ mvRetr qb n) =
      𝟙 ((CsingSSet G).X n) := by
  rw [← Category.assoc, HomologicalComplex.biprod_lift_snd_f]
  refine SSet.chainComplex_hom_ext fun z => ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ι_mvRetr qb hqb, Category.comp_id]

/-- `mvSect` is a section of the second map of the Mayer–Vietoris short complex. -/
lemma mvSect_comp_mvDesc {n : ℕ}
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌))) :
    mvSect hcover ≫ (biprod.desc (SSet.chainComplexMap pa (AddCommGrpCat.of ℤ))
        (-SSet.chainComplexMap pb (AddCommGrpCat.of ℤ))).f n = 𝟙 ((CsingSSet D).X n) := by
  refine SSet.chainComplex_hom_ext fun d => ?_
  rw [Category.comp_id]
  by_cases hd : ∃ x, pa.app (op ⦋n⦌) x = d
  · obtain ⟨x, rfl⟩ := hd
    rw [ι_mvSect_of_mem_assoc hcover hpa, HomologicalComplex.biprod_inl_desc_f,
      SSet.ι_chainComplexMap_f]
  · obtain ⟨y, rfl⟩ := (hcover d).resolve_left hd
    rw [ι_mvSect_of_not_mem_assoc hcover hpb y hd, Preadditive.neg_comp, Category.assoc,
      HomologicalComplex.biprod_inr_desc_f, HomologicalComplex.neg_f_apply,
      Preadditive.comp_neg, neg_neg, SSet.ι_chainComplexMap_f]

/-- The retraction and the section add up to the identity. -/
lemma mvRetr_add_mvSect {n : ℕ}
    (h : qa ≫ pa = qb ≫ pb)
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hqb : Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌)))
    (hinter : ∀ (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    ((biprod.snd : CsingSSet Sa ⊞ CsingSSet Sb ⟶ _).f n ≫ mvRetr qb n) ≫
        (biprod.lift (SSet.chainComplexMap qa (AddCommGrpCat.of ℤ))
          (SSet.chainComplexMap qb (AddCommGrpCat.of ℤ))).f n +
      (biprod.desc (SSet.chainComplexMap pa (AddCommGrpCat.of ℤ))
          (-SSet.chainComplexMap pb (AddCommGrpCat.of ℤ))).f n ≫ mvSect hcover =
      𝟙 ((CsingSSet Sa ⊞ CsingSSet Sb).X n) := by
  refine HomologicalComplex.biprodX_ext_from ?_ ?_
  · simp only [Preadditive.comp_add, Category.assoc,
      HomologicalComplex.biprod_inl_snd_f_assoc, zero_comp, zero_add,
      HomologicalComplex.biprod_inl_desc_f_assoc, Category.comp_id]
    refine SSet.chainComplex_hom_ext fun x => ?_
    rw [SSet.ι_chainComplexMap_f_assoc, ι_mvSect_of_mem hcover hpa]
  · simp only [Preadditive.comp_add, Category.assoc,
      HomologicalComplex.biprod_inr_snd_f_assoc,
      HomologicalComplex.biprod_inr_desc_f_assoc, Category.comp_id,
      HomologicalComplex.neg_f_apply, Preadditive.neg_comp]
    rw [← sub_eq_add_neg, sub_eq_iff_eq_add]
    refine SSet.chainComplex_hom_ext fun y => ?_
    rw [Preadditive.comp_add]
    by_cases hy : ∃ z, qb.app (op ⦋n⦌) z = y
    · obtain ⟨z, rfl⟩ := hy
      have hz : pb.app (op ⦋n⦌) (qb.app (op ⦋n⦌) z) = pa.app (op ⦋n⦌) (qa.app (op ⦋n⦌) z) := by
        have hh := NatTrans.congr_app h (op ⦋n⦌)
        have hz' := congrArg (fun u : G _⦋n⦌ ⟶ D _⦋n⦌ => u z) hh
        simpa using hz'.symm
      rw [ι_mvRetr_assoc qb hqb, ι_mvLift, SSet.ι_chainComplexMap_f_assoc, hz,
        ι_mvSect_of_mem hcover hpa, add_comm]
    · rw [ι_mvRetr_of_not_mem_assoc qb y hy, zero_comp, SSet.ι_chainComplexMap_f_assoc,
        ι_mvSect_of_not_mem hcover hpb y (fun ⟨x, hx⟩ => hy (hinter x y hx)),
        add_neg_cancel]

variable (qa qb pa pb) in
/-- The Mayer–Vietoris short complex is degreewise split. -/
def mvSplitting (h : qa ≫ pa = qb ≫ pb) (n : ℕ)
    (hqb : Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : Function.Injective (pb.app (op ⦋n⦌)))
    (hcover : ∀ d : D _⦋n⦌, (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hinter : ∀ (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    ShortComplex.Splitting
      ((mvShortComplex qa qb pa pb h).map (HomologicalComplex.eval _ _ n)) where
  r := (biprod.snd : CsingSSet Sa ⊞ CsingSSet Sb ⟶ _).f n ≫ mvRetr qb n
  s := mvSect hcover
  f_r := mvLift_comp_mvRetr hqb
  s_g := mvSect_comp_mvDesc hcover hpa hpb
  id := mvRetr_add_mvSect h hcover hqb hpa hpb hinter

/-- The Mayer–Vietoris sequence of chain complexes is short exact. -/
theorem mvShortComplex_shortExact (h : qa ≫ pa = qb ≫ pb)
    (hqb : ∀ n : ℕ, Function.Injective (qb.app (op ⦋n⦌)))
    (hpa : ∀ n : ℕ, Function.Injective (pa.app (op ⦋n⦌)))
    (hpb : ∀ n : ℕ, Function.Injective (pb.app (op ⦋n⦌)))
    (hcover : ∀ (n : ℕ) (d : D _⦋n⦌),
      (∃ x, pa.app (op ⦋n⦌) x = d) ∨ (∃ y, pb.app (op ⦋n⦌) y = d))
    (hinter : ∀ (n : ℕ) (x : Sa _⦋n⦌) (y : Sb _⦋n⦌),
      pa.app (op ⦋n⦌) x = pb.app (op ⦋n⦌) y → ∃ z, qb.app (op ⦋n⦌) z = y) :
    (mvShortComplex qa qb pa pb h).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mvSplitting qa qb pa pb h n (hqb n) (hpa n) (hpb n) (hcover n) (hinter n)).shortExact)

end

end Submission
