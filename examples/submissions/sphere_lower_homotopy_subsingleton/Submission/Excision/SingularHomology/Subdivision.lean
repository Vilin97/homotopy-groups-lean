/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Submission.Excision.ConvexSpace.AffineChains
public import Submission.Excision.ConvexSpace.Top
public import Submission.Excision.SingularHomology.NatTrans
public import Submission.Excision.SingularHomology.ULift
public import Submission.Excision.HomologicalComplex.NullHomotopy

/-!
# The subdivision endomorphism of the singular chain complex

-/

universe w

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Convexity Simplicial
  Opposite

namespace TopCat

open ConvexSpace

-- to be moved
lemma toSSetULiftEquiv_symm_toSSetNatTrans_affineMapId (n : ℕ) :
    dsimp% toSSetULiftEquiv.symm ((StdSimplex.toSSetNatTrans _).app _  (.id _)) =
    toSSet.univObj.{w} n := by
  simp [StdSimplex.toSSetNatTrans]
  rfl

end TopCat

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C]

namespace AlgebraicTopology

namespace singularChainComplexFunctor

/-- The natural transformations that are part of the homotopy between
the identity of the singular chain complex of a topological space and
the subdivision endomorphism. -/
noncomputable def hSd (R : C) (n : ℕ) :
    (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor C).obj R ⋙ eval _ _ (n + 1) :=
  haveI : HasCoproducts.{0} C := hasCoproducts_shrink
  natTransMk (SSet.ιChainComplex _ (ConvexSpace.AffineMap.id _) ≫
    ConvexSpace.toSSet.hSd (R := R) (Y := StdSimplex ℝ (Fin (n + 1))) n ≫
      (SSet.chainComplexMap (StdSimplex.toSSetNatTrans _) R).f (n + 1) ≫
        (TopCat.singularChainComplexULiftIso.{w} _ R).inv.f (n + 1))

@[inherit_doc hSd]
noncomputable def hSd' (R : C) (n m : ℕ) :
    (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ n ⟶
      (singularChainComplexFunctor.{w} C).obj R ⋙ eval _ _ m :=
  if h : n + 1 = m then hSd R n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hSd'_eq (R : C) (n : ℕ) : hSd'.{w} R n (n + 1) = hSd R n := by simp [hSd']

lemma hSd'_eq_zero (R : C) (n m : ℕ) (h : n + 1 ≠ m) : hSd' R n m = 0 := by grind [hSd']

@[simp]
lemma hSd_zero (R : C) : hSd.{w} R 0 = 0 := by simp [hSd]

end singularChainComplexFunctor

open singularChainComplexFunctor in
/-- The subdivision operator on the singular chain complexes of
topological spaces as an endomorphism of the functor
`(singularChainComplexFunctor.{w} C).obj R : TopCat.{w} ⥤ ChainComplex C ℕ`. -/
noncomputable def singularChainComplexFunctorSd (R : C) :
    (singularChainComplexFunctor.{w} C).obj R ⟶
      (singularChainComplexFunctor.{w} C).obj R where
  app X := 𝟙 _ - Homotopy.nullHomotopicMap (fun n m ↦ (hSd' R n m).app X)
  naturality {X Y} f := by
    simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.id_comp,
      sub_right_inj]
    rw [Homotopy.nullHomotopicMap_comp, Homotopy.comp_nullHomotopicMap]
    congr
    ext n m
    exact (hSd' R n m).naturality f

end AlgebraicTopology

namespace TopCat

variable (X Y : TopCat.{w}) (f : X ⟶ Y) {R : C}

/-- The subdivision endomorphism of the singular chain complex of a topological space `X`
with coefficients in `R`. -/
noncomputable abbrev singularChainComplexSd :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  (singularChainComplexFunctorSd R).app X

@[reassoc]
lemma ι_map_app_singularChainComplexSd_f {n : ℕ} (x : toSSet.obj X _⦋n⦌) :
    Y.ιSingularChainComplex (R := R) ((toSSet.map f).app _ x) ≫
        Y.singularChainComplexSd.f n =
    X.ιSingularChainComplex x ≫ X.singularChainComplexSd.f n ≫
      (singularChainComplexMap f R).f n := by
  rw [← comp_f, ← (singularChainComplexFunctorSd R).naturality f,
    ← ι_singularChainComplexMap_assoc]
  rfl

@[simp]
lemma singularChainComplexSd_f_zero :
    X.singularChainComplexSd.f 0 = 𝟙 ((X.singularChainComplex R).X 0) := by
  simp [singularChainComplexSd, singularChainComplexFunctorSd,
    ChainComplex.nullHomotopicMap_f_zero]
  exact zero_comp

open singularChainComplexFunctor in
/-- The homotopy from the identity to the subdivision endomorphism
`X.singularChainComplexSd` of the singular chain complex of a topological
space `X` with coefficients in `R`. -/
noncomputable def singularChainComplexHomotopyIdSd :
    _root_.Homotopy (𝟙 (X.singularChainComplex R)) X.singularChainComplexSd :=
  Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [singularChainComplexSd, singularChainComplexFunctorSd]))
      (Homotopy.nullHomotopy (fun n m ↦ (hSd' R n m).app X)
        (fun n m h ↦ by simp [hSd'_eq_zero _ _ _ h]; rfl)))

private lemma singularChainComplexHomotopyIdSd_hom_eq_hSd' (n m : ℕ) :
    (X.singularChainComplexHomotopyIdSd (R := R)).hom n m =
      (singularChainComplexFunctor.hSd' R n m).app X := by
  dsimp [singularChainComplexHomotopyIdSd, Homotopy.equivSubZero]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  apply Homotopy.nullHomotopy_hom

variable {X Y} in
@[reassoc]
lemma singularChainComplexHomotopyIdSd_hom_naturality (n m : ℕ) :
    (singularChainComplexMap f R).f n ≫ Y.singularChainComplexHomotopyIdSd.hom n m =
      X.singularChainComplexHomotopyIdSd.hom n m ≫ (singularChainComplexMap f R).f m := by
  simp only [singularChainComplexHomotopyIdSd_hom_eq_hSd']
  exact (singularChainComplexFunctor.hSd' R n m).naturality f

variable {X Y} in
@[reassoc]
lemma ι_map_app_singularChainComplexHomotopyIdSd_hom
    {n : ℕ} (x : toSSet.obj X _⦋n⦌) (m : ℕ) :
    Y.ιSingularChainComplex (R := R) ((toSSet.map f).app _ x) ≫
      Y.singularChainComplexHomotopyIdSd.hom n m =
    X.ιSingularChainComplex x ≫ X.singularChainComplexHomotopyIdSd.hom n m ≫
      (singularChainComplexMap f R).f m := by
  simpa using X.ιSingularChainComplex (R := R) x ≫=
    singularChainComplexHomotopyIdSd_hom_naturality f n m

open singularChainComplexFunctor in
@[reassoc]
lemma ι_univObj_singularChainComplexHomotopyIdSd_hom (n : ℕ) :
    haveI : HasCoproducts.{0} C := hasCoproducts_shrink
    ιSingularChainComplex (SimplexCategory.toTop.{w} ^⦋n⦌) (R := R) (toSSet.univObj.{w} n) ≫
      (singularChainComplexHomotopyIdSd _).hom n (n + 1) =
    SSet.ιChainComplex (ConvexSpace.toSSet ℝ _) (.id _) ≫
      (ConvexSpace.toSSet.homotopyIdSd (StdSimplex ℝ (Fin (n + 1))) R).hom n (n + 1) ≫
      (SSet.chainComplexMap (StdSimplex.toSSetNatTrans (Fin (n + 1))) R).f (n + 1) ≫
      ((singularChainComplexFunctorULiftIso.{w}.inv.app R).app _).f (n + 1) := by
  simp only [singularChainComplexHomotopyIdSd_hom_eq_hSd', hSd'_eq, hSd,
    ConvexSpace.toSSet.homotopyIdSd_hom_eq_hSd', ConvexSpace.toSSet.hSd'_eq]
  erw [ι_natTransMk]
  simp only [toSSet.univObj]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

namespace toSSet

variable {X}

/-- The subdivisions of a singular `n`-simplex of a topological space. It takes
a permutation of `Fin (n + 1)` as an input. -/
noncomputable def sd {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Equiv.Perm (Fin (n + 1))) :
    (toSSet.obj X) _⦋n⦌ :=
  (toSSetObjEquiv _ _).symm
    ((toSSetObjEquiv _ _ s).comp
      ((ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))).sd σ).toContinuousMap)

lemma sd_toSSetObjEquiv_symm {n : ℕ} (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1))) :
    sd ((toSSetObjEquiv _ (op ⦋n⦌)).symm s) σ =
      (toSSetObjEquiv _ (op ⦋n⦌)).symm
        (s.comp ((ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1)))).sd σ).toContinuousMap) :=
  rfl

@[simp]
lemma sd_zero (s : (toSSet.obj X) _⦋0⦌)
    (σ : Equiv.Perm (Fin 1)) :
    sd s σ = s := by
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective s
  rfl

lemma range_toSSetObjEquiv_sd_subset
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (toSSetObjEquiv _ _ (sd s σ)) ⊆ Set.range (toSSetObjEquiv _ _ s) := by
  obtain ⟨s, rfl⟩ := (toSSetObjEquiv  _ _).symm.surjective s
  simp only [sd_toSSetObjEquiv_symm, Equiv.apply_symm_apply, ContinuousMap.coe_comp]
  apply Set.range_comp_subset_range

/-- The `k`-iterated subdivisions of a singular `n`-simplex of a topological space.
It takes a family of `k` permutations of `Fin (n + 1)` as an input. -/
@[no_expose]
noncomputable def sdIter
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    (toSSet.obj X) _⦋n⦌ := by
  induction k generalizing s with
  | zero => exact s
  | succ k hk => exact sd (hk s (σ ∘ Fin.succ)) (σ 0)

@[simp]
lemma sdIter_zero
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = s := by
  rfl

lemma sdIter_succ
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) {k : ℕ} (σ : Fin (k + 1) → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = sd (sdIter s (σ ∘ Fin.succ)) (σ 0) := by
  rfl

@[simp]
lemma sdIter_one
    {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (σ : Fin 1 → Equiv.Perm (Fin (n + 1))) :
    sdIter s σ = sd s (σ 0) := by
  rfl

lemma sdIter_toSSetObjEquiv_symm {n : ℕ} (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    sdIter ((toSSetObjEquiv _ (op ⦋n⦌)).symm s) σ =
      (toSSetObjEquiv _ (op ⦋n⦌)).symm
        (s.comp ((ConvexSpace.AffineMap.id _).sdIter σ).toContinuousMap) := by
  induction k generalizing s with
  | zero => simp
  | succ k hk =>
    simp [sdIter_succ, hk, sd_toSSetObjEquiv_symm,
      ← ConvexSpace.AffineMap.toContinuousMap_comp,
      ConvexSpace.AffineMap.comp_sd, ConvexSpace.AffineMap.sdIter_succ]

lemma exists_sdIter_δ_eq
    {n : ℕ} (s : (toSSet.obj X) _⦋n + 1⦌)
    (i : Fin (n + 2)) {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    ∃ (σ' : Fin k → Equiv.Perm (Fin (n + 2))) (i' : Fin (n + 2)),
      sdIter ((toSSet.obj X).δ i s) σ =
        (toSSet.obj X).δ i' (sdIter s σ') := by
  obtain ⟨s, rfl⟩ := (toSSetObjEquiv _ (op ⦋n + 1⦌)).symm.surjective s
  obtain ⟨σ', i', h⟩ := ConvexSpace.AffineMap.exists_sdIter_δ_eq (K := ℝ) (.id _) i σ
  refine ⟨σ', i', ?_⟩
  simp only [sdIter_toSSetObjEquiv_symm, TopCat.δ_toSSetObjEquiv_symm,
    ContinuousMap.comp_assoc, ← ConvexSpace.AffineMap.toContinuousMap_comp,
    ConvexSpace.AffineMap.comp_sdIter]
  congr

end toSSet

/-- The `k`th iteration of the subdivision operator `TopCat.singularChainComplexSd`. -/
@[no_expose]
noncomputable def singularChainComplexSdIter (k : ℕ) :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  letI x : End _ := singularChainComplexSd (R := R) X
  x ^ k

@[simp]
lemma singularChainComplexSdIter_zero :
    singularChainComplexSdIter (R := R) X 0 = 𝟙 _ := by
  simp [singularChainComplexSdIter]

@[simp high]
lemma singularChainComplexSdIter_one :
    singularChainComplexSdIter (R := R) X 1 = singularChainComplexSd X := by
  simp [singularChainComplexSdIter]

@[simp]
lemma singularChainComplexSdIter_add (k l : ℕ) :
    singularChainComplexSdIter (R := R) X (k + l) =
      singularChainComplexSdIter X k ≫ singularChainComplexSdIter X l := by
  simp [add_comm k l, singularChainComplexSdIter, pow_add]

@[simp]
lemma singularChainComplexSdIter_succ (k : ℕ) :
    singularChainComplexSdIter (R := R) X (k + 1) =
      singularChainComplexSdIter X k ≫ singularChainComplexSd X := by
  simp [singularChainComplexSdIter_add]

@[reassoc]
lemma ι_univObj_singularChainComplexSd_f (n : ℕ) :
    ιSingularChainComplex _ (TopCat.toSSet.univObj n) ≫
      (singularChainComplexSd _ (R := R)).f n =
    ∑ (σ : Equiv.Perm (Fin (n + 1))),
      σ.sign • ιSingularChainComplex _
        ((toSSetObjEquiv _ _).symm
          (ContinuousMap.comp ⟨ULift.up, by fun_prop⟩
            ((ConvexSpace.AffineMap.id  _).sd σ).toContinuousMap)) := by
  obtain _ | n := n
  · simp
    rfl
  · have : HasCoproducts.{0} C := hasCoproducts_shrink
    convert! ConvexSpace.toSSet.ι_sd_f_eq_sum R (n := n + 1) (s := .id _) =≫
      ((SSet.chainComplexMap (StdSimplex.toSSetNatTrans _) R).f (n + 1) ≫
      (TopCat.singularChainComplexULiftIso.{w} _ R).inv.f (n + 1)) using 1
    · rw [(singularChainComplexHomotopyIdSd _).eq_sub_nullHomotopicMap,
        (ConvexSpace.toSSet.homotopyIdSd ..).eq_sub_nullHomotopicMap]
      dsimp
      simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
        SSet.ι_chainComplexMap_f_assoc, Category.assoc]
      congr 1
      · erw [ι_uliftFunctorCompSingularChainComplexFunctorIso_inv_app]
        rw [toSSetULiftEquiv_symm_toSSetNatTrans_affineMapId]
        rfl
      · simp only [ChainComplex.nullHomotopicMap_f_succ,
          Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
          SSet.ιChainComplex_d_assoc, ι_singularChainComplex_d_assoc,
          Preadditive.sum_comp, Linear.smul_comp]
        congr 1
        · congr 1
          ext i
          congr 1
          erw [toSSet.δ_univObj, ι_map_app_singularChainComplexHomotopyIdSd_hom]
          rw [ι_univObj_singularChainComplexHomotopyIdSd_hom_assoc,
            SimplicialObject.δ_def, ConvexSpace.toSSet_map]
          dsimp only [TypeCat.Fun.coe_mk, TypeCat.hom_ofHom, Quiver.Hom.unop_op]
          rw [ConvexSpace.AffineMap.id_comp]
          erw [reassoc_of% ConvexSpace.toSSet.ι_toSSetMap_app_homotopyIdSd_hom
            (φ := StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ i)) (x := .id _) (m := n + 1)]
          erw [Category.assoc, Category.assoc, Category.assoc]
          congr 2
          erw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
          erw [← NatTrans.naturality]
          erw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
          congr 1
          have key : SSet.chainComplexMap (StdSimplex.toSSetNatTrans (Fin (n + 1))) R ≫
              ((singularChainComplexFunctor C).obj R).map
                (SimplexCategory.toTop₀.map (SimplexCategory.δ i)) =
              SSet.chainComplexMap
                  (StdSimplex.affineMap (R := ℝ) (SimplexCategory.δ i)).toSSetMap R ≫
                SSet.chainComplexMap (StdSimplex.toSSetNatTrans (Fin (n + 1 + 1))) R := by
            erw [← Functor.map_comp, ← Functor.map_comp]
            rw [StdSimplex.toSSetNatTrans_naturality]
            rfl
          erw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc]
          rfl
        · erw [ι_univObj_singularChainComplexHomotopyIdSd_hom_assoc,
            Category.assoc, Category.assoc, Category.assoc,
            HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc]
          rfl
    · simp only [Preadditive.sum_comp]
      congr 1
      ext σ
      simp only [Iso.app_inv, Linear.units_smul_comp]
      congr 1
      rw [SSet.ι_chainComplexMap_f_assoc]
      dsimp
      erw [ι_uliftFunctorCompSingularChainComplexFunctorIso_inv_app]
      rfl

@[reassoc]
lemma ι_singularChainComplexSd_f {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) :
    ιSingularChainComplex _ s ≫ (singularChainComplexSd X (R := R)).f n =
      ∑ (σ : Equiv.Perm (Fin (n + 1))),
        σ.sign • X.ιSingularChainComplex (toSSet.sd s σ) := by
  obtain ⟨f, rfl⟩ := toSSet.exists_map_app_univObj_eq s
  rw [ι_map_app_singularChainComplexSd_f,
    ι_univObj_singularChainComplexSd_f_assoc, Preadditive.sum_comp]
  congr 1
  ext σ
  simp only [Linear.units_smul_comp, ι_singularChainComplexMap, smul_left_cancel_iff]
  rfl

@[reassoc]
lemma ι_singularChainComplexSdIter_f {n : ℕ} (s : (toSSet.obj X) _⦋n⦌) (k : ℕ) :
    ιSingularChainComplex _ s ≫ (singularChainComplexSdIter X (R := R) k).f n =
      ∑ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
        (∏ (i : Fin k), (σ i).sign) •
          ιSingularChainComplex _ (toSSet.sdIter s σ) := by
  induction k with
  | zero => simp
  | succ k hk =>
    let α : (Fin (k + 1) → Equiv.Perm (Fin (n + 1))) ≃
        (Fin k → Equiv.Perm (Fin (n + 1))) × Equiv.Perm (Fin (n + 1)) :=
      { toFun σ := ⟨σ ∘ Fin.succ, σ 0⟩
        invFun := fun ⟨σ, σ'⟩ ↦ Fin.cases σ' σ
        left_inv σ := by
          ext l : 1
          obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ <;> rfl }
    simp only [singularChainComplexSdIter_succ, HomologicalComplex.comp_f, reassoc_of% hk,
      Preadditive.sum_comp, Linear.units_smul_comp, ι_singularChainComplexSd_f,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_bijective
      (g := fun ⟨σ, σ₀⟩ ↦ ((∏ i, Equiv.Perm.sign (σ i)) * Equiv.Perm.sign σ₀) •
        ιSingularChainComplex _ (toSSet.sd (toSSet.sdIter s σ) σ₀))
        (t := .univ) _ α.bijective (by simp) ?_,
      Finset.sum_finset_product .univ .univ (fun _ ↦ .univ) (by simp)]
    simp only [Finset.mem_univ, forall_const]
    intro σ
    congr
    rw [mul_comm]
    simp [α, Fin.prod_univ_succ]

@[simp]
lemma singularChainComplexSdIter_f_zero (k : ℕ) :
    (singularChainComplexSdIter X (R := R) k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k hk => simp [hk]

/-- The homotopy from the identity to the `k`th iteration
`X.singularChainComplexSdIter` of subdivision endomorphism of the singular
chain complex of a topological space `X` with coefficients in `R`. -/
noncomputable def singularChainComplexHomotopyIdSdIter (k : ℕ) :
    _root_.Homotopy (𝟙 (X.singularChainComplex R)) (X.singularChainComplexSdIter k) :=
  match k with
  | .zero => .ofEq (by simp)
  | .succ k => (singularChainComplexHomotopyIdSdIter k).trans
    ((Homotopy.ofEq (by simp)).trans
      (((Homotopy.refl (X.singularChainComplexSdIter k)).comp
        X.singularChainComplexHomotopyIdSd).trans (.ofEq (by simp))))

lemma singularChainComplexHomotopyIdSdIter_hom (k n m : ℕ) :
    (X.singularChainComplexHomotopyIdSdIter (R := R) k).hom n m =
      ∑ (i : Fin k), (X.singularChainComplexSdIter i.val).f n ≫
          X.singularChainComplexHomotopyIdSd.hom n m := by
  induction k with
  | zero => simp [singularChainComplexHomotopyIdSdIter]
  | succ k hk => simp [singularChainComplexHomotopyIdSdIter, hk, Fin.sum_univ_castSucc]

end TopCat
