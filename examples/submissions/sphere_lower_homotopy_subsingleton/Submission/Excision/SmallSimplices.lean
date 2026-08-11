/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Submission.Excision.Fin.Prod
public import Submission.Excision.ConvexSpace.Diameter
public import Submission.Excision.SimplicialSet.Homology
public import Submission.Excision.SimplicialSet.RelativeHomology
public import Submission.Excision.SingularHomology.Subdivision
public import Submission.Excision.Topology.LebesgueNumber

/-!
# Small simplices lemma

-/

universe w

@[expose] public section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Opposite

namespace TopCat

variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

namespace toSSet

/-- Let `V : Set X` be a subset of a topological space `X : TopCat`.
This is the subcomplex of the singular simplicial set `toSSet.obj X` of `X`
consisting of simplices that are contained in `V`. -/
noncomputable abbrev subcomplexOfSet (V : Set X) : (toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (toSSet.map (ofHom (X := V) ⟨Subtype.val, by fun_prop⟩))

lemma mem_subcomplexOfSet_iff (V : Set X) {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSet V).obj _ ↔
      Set.range (toSSetObjEquiv _ _ s) ⊆ V := by
  simp only [subcomplexOfSet, Subfunctor.range_obj, Set.mem_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
    change Set.range (Subtype.val ∘ f) ⊆ V
    rintro _ ⟨u, rfl⟩
    simp
  · obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
    exact ⟨(toSSetObjEquiv _ _).symm ⟨fun x ↦ ⟨f x, h (by simp)⟩, by fun_prop⟩, rfl⟩

lemma subcomplexOfSet_inter (V₁ V₂ : Set X) :
    subcomplexOfSet (V₁ ∩ V₂) = subcomplexOfSet V₁ ⊓ subcomplexOfSet V₂ := by
  ext ⟨⟨n⟩⟩
  simp only [mem_subcomplexOfSet_iff, Set.subset_inter_iff, Subfunctor.min_obj, Set.mem_inter_iff]

variable (U) in
/-- Let `U : ι → Set X` be a family of subsets of a topological space `X : TopCat`.
This is the subcomplex of the singular simplicial set `toSSet.obj X` of `X`
consisting of simplices that are contained in some `U i`. -/
noncomputable def subcomplexOfSets : (toSSet.obj X).Subcomplex :=
  ⨆ (i : ι), subcomplexOfSet (U i)

lemma subcomplexOfSets_bool (U : Bool → Set X) :
    subcomplexOfSets U = subcomplexOfSet (U false) ⊔ subcomplexOfSet (U true) := by
  dsimp [subcomplexOfSets]
  refine le_antisymm ?_ ?_
  · simp
  · simp only [sup_le_iff]
    exact ⟨le_iSup (fun i ↦ subcomplexOfSet (U i)) false,
      le_iSup (fun i ↦ subcomplexOfSet (U i)) true⟩

lemma mem_subcomplexOfSets_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSets U).obj _ ↔
      ∃ (i : ι), Set.range (toSSetObjEquiv _ _ s) ⊆ U i := by
  simp only [subcomplexOfSets, Subfunctor.iSup_obj, Set.mem_iUnion,
    mem_subcomplexOfSet_iff]

lemma mem_subcomplexOfSets_iff' {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    s ∈ (subcomplexOfSets U).obj _ ↔
      ∃ (i : ι) (t : toSSet.obj (of (U i)) _⦋n⦌),
        (toSSet.map (ofHom ⟨Subtype.val, by fun_prop⟩)).app _ t = s := by
  rw [mem_subcomplexOfSets_iff]
  refine exists_congr (fun i ↦ ⟨fun h ↦ ?_, ?_⟩)
  · obtain ⟨s, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
    exact ⟨(toSSetObjEquiv _ _).symm ⟨fun x ↦ ⟨s x, h (by simp)⟩, by fun_prop⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective t
    rintro _ ⟨x, rfl⟩
    exact (t x).prop

lemma sd_mem_subcomplexOfSets {n : ℕ} (s : toSSet.obj X _⦋n⦌)
    (hs : s ∈ (subcomplexOfSets U).obj _) (σ : Equiv.Perm (Fin (n + 1))) :
    sd s σ ∈ (subcomplexOfSets U).obj _ := by
  rw [mem_subcomplexOfSets_iff] at hs ⊢
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, le_trans (range_toSSetObjEquiv_sd_subset _ _) hi⟩

end toSSet

variable (U) in
/-- Given a family of subsets `U : ι → Set X` of a topological space `X`,
this is the pair of simplicial sets corresponding to the inclusion
of the subcomplex `toSSet.subcomplexOfSets U` of `toSSet.obj X` consisting
of simplices contained in some `U i`. -/
noncomputable abbrev sSetPairOfSets : SSetPair.{w} :=
  SSetPair.of (toSSet.subcomplexOfSets U).ι

variable (U) in
/-- Given a family `U : ι → Set X` of subsets of a topological spaces `X`,
this is the condition that the union of the interiors of the `U i` covers `X`. -/
structure SmallSimplicesCondition : Prop where
  iUnion_interior : ⋃ (i : ι), interior (U i) = Set.univ

namespace SmallSimplicesCondition

variable (hU : SmallSimplicesCondition U)

include hU in
protected lemma iUnion : ⋃ (i : ι), U i = Set.univ := by
  rw [← Set.univ_subset_iff, ← hU.iUnion_interior]
  exact Set.iUnion_subset (fun i ↦ interior_subset.trans (Set.subset_iUnion _ _))

include hU in
lemma subcomplexOfSets_obj_zero :
    (toSSet.subcomplexOfSets U).obj (op ⦋0⦌) = Set.univ := by
  ext x
  obtain ⟨x, rfl⟩ := X.toSSetObj₀Equiv.symm.surjective x
  have := Set.mem_univ x
  rw [← hU.iUnion, Set.mem_iUnion] at this
  obtain ⟨i, hi⟩ := this
  simp only [toSSet.mem_subcomplexOfSets_iff, Set.mem_univ, iff_true]
  refine ⟨i, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hi

variable (U) in
/-- Let `U : ι → Set X` be a family of subsets of a topological sapce `X`.
Let `s` be a singular `n`-simplex of `X`. For any `k : ℕ`, this is
the condition that after subdividing `k` times `s`, we obtain
simplices that are contained in some of the `U i`. -/
def SdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) (k : ℕ) : Prop :=
  ∀ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
    toSSet.sdIter s σ ∈ (toSSet.subcomplexOfSets U).obj _

lemma SdIterIsSmall.succ {n : ℕ} {s : toSSet.obj X _⦋n⦌} {k : ℕ}
    (hs : SdIterIsSmall U s k) :
    SdIterIsSmall U s (k + 1) :=
  fun σ ↦ by
    rw [toSSet.sdIter_succ]
    exact toSSet.sd_mem_subcomplexOfSets _ (hs _) _

lemma SdIterIsSmall.δ {n : ℕ} {s : toSSet.obj X _⦋n + 1⦌} {k : ℕ}
    (hs : SdIterIsSmall U s k) (i : Fin (n + 2)) :
    SdIterIsSmall U ((toSSet.obj X).δ i s) k := by
  intro σ
  obtain ⟨σ', i', h⟩ := toSSet.exists_sdIter_δ_eq s i σ
  rw [h]
  exact (toSSet.subcomplexOfSets U).map _ (hs _)

lemma SdIterIsSmall.of_le {n : ℕ} {s : toSSet.obj X _⦋n⦌} {k k' : ℕ}
    (hs : SdIterIsSmall U s k) (h : k ≤ k') :
    SdIterIsSmall U s k' := by
  obtain ⟨i, h⟩ := Nat.le.dest h
  induction i generalizing k k' with
  | zero =>
    obtain rfl : k = k' := by lia
    exact hs
  | succ i hi =>
    obtain rfl : k + i + 1 = k' := by lia
    exact (hi hs (by lia) rfl).succ

lemma sdIterIsSmall_zero_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    SdIterIsSmall U s 0 ↔ s ∈ (toSSet.subcomplexOfSets U).obj _ := by
  simp [SdIterIsSmall]

include hU in
attribute [local instance] Convexity.ConvexSpace.ofModule in
open Convexity in
lemma exists_sdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    ∃ (k : ℕ), SdIterIsSmall U s k := by
  obtain ⟨f, rfl⟩ := (toSSetObjEquiv _ _).symm.surjective s
  let V (i : ι) : Set (stdSimplex ℝ (Fin (n + 1))) := f ⁻¹' (interior (U i))
  obtain ⟨ε, hε₀, hε⟩ := CompactSpace.lebesgue_number_lemma V
    (fun i ↦ f.continuous.isOpen_preimage _ isOpen_interior)
    (by simp [V, ← Set.preimage_iUnion, hU.iUnion_interior])
  let s₀ := ConvexSpace.AffineMap.id (R := ℝ) (StdSimplex ℝ (Fin (n + 1)))
  suffices ∃ (k : ℕ), ∀ (σ : Fin k → Equiv.Perm (Fin (n + 1))),
    (StdSimplex.ι.comp (s₀.sdIter σ)).diam ≤ ε by
      obtain ⟨k, hk⟩ := this
      refine ⟨k, fun σ ↦ ?_⟩
      rw [toSSet.mem_subcomplexOfSets_iff]
      obtain ⟨i, hi⟩ := hε (Set.range (StdSimplex.equiv ∘ (s₀.sdIter σ)))
        (Set.range_nonempty _) (by simpa [Set.range_comp] using hk σ)
      refine ⟨i, ?_⟩
      rintro _ ⟨x, rfl⟩
      refine interior_subset ?_
      simpa only [Set.mem_preimage, V, toSSet.sdIter_toSSetObjEquiv_symm] using!
        hi (Set.mem_range_self (StdSimplex.equiv.symm x))
  let δ := (StdSimplex.ι.comp s₀).diam
  have hδ : 0 ≤ δ := (StdSimplex.ι.comp s₀).diam_nonneg
  obtain h | h := hδ.lt_or_eq'
  · have hε' : 0 < ε / δ := by positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε' (y := (n / (n + 1) : ℝ)) (by
      rw [div_lt_one (by positivity)]
      simp)
    refine ⟨k, fun σ ↦ ?_⟩
    rw [ConvexSpace.AffineMap.comp_sdIter]
    refine ((StdSimplex.ι.comp s₀).diam_sdIter_le σ).trans
      (le_of_le_of_eq (mul_le_mul_of_nonneg_right hk.le (ConvexSpace.AffineMap.diam_nonneg _))
      (div_mul_cancel₀ ε h.ne'))
  · exact ⟨0, by simp [δ, h, hε₀.le]⟩

include hU in
lemma nonempty_ofPred_sdIterIsSmall {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    (setOf (SdIterIsSmall U s)).Nonempty :=
  hU.exists_sdIterIsSmall s

/-- Given a family `U : ι → Set X` of subsets of a topological space `X` which
satisfy the condition `SmallSimplicesCondition U`, and `s` a singular
`n`-simplex of `X`, this is the smallest `k : ℕ` such that
the condition `SdIterIsSmall U s k` is satisfied, i.e. that the
`k`th iterated subdivisions of `s` all belong to some of the `U i`. -/
noncomputable def m {n : ℕ} (s : toSSet.obj X _⦋n⦌) : ℕ :=
  Nat.lt_wfRel.wf.min _ (hU.nonempty_ofPred_sdIterIsSmall s)

lemma sdIterIsSmall_m {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    SdIterIsSmall U s (hU.m s) :=
  Nat.lt_wfRel.wf.min_mem _ (hU.nonempty_ofPred_sdIterIsSmall s)

lemma sdIterIsSmall_iff_m_le {n : ℕ} (s : toSSet.obj X _⦋n⦌) (k : ℕ) :
    SdIterIsSmall U s k ↔ hU.m s ≤ k :=
  ⟨fun h ↦ Nat.lt_wfRel.wf.min_le h, fun h ↦ (hU.sdIterIsSmall_m s).of_le h⟩

lemma m_eq_zero_iff {n : ℕ} (s : toSSet.obj X _⦋n⦌) :
    hU.m s = 0 ↔ s ∈ (toSSet.subcomplexOfSets U).obj _ := by
  rw [← sdIterIsSmall_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm ?_ (by simp)⟩
  · simpa only [← h] using hU.sdIterIsSmall_m s
  · rwa [← sdIterIsSmall_iff_m_le]

lemma m_δ_le {n : ℕ} (s : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) :
    hU.m ((toSSet.obj X).δ i s) ≤ hU.m s := by
  rw [← sdIterIsSmall_iff_m_le]
  exact (hU.sdIterIsSmall_m s).δ i

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C] {R : C}

include hU

/-- Given a family `U : ι → Set X` of subsets of a topological space `X` which
satisfies the condition `SmallSimplicesCondition U`, this is the data
that is part of the homotopy involved in the definition of a retraction
`ρ' : X.singularChainComplex R ⟶ (toSSet.subcomplexOfSets U).toSSet.chainComplex R`
of the inclusion. -/
noncomputable def hρ (n : ℕ) :
    (X.singularChainComplex R).X n ⟶ (X.singularChainComplex R).X (n + 1) :=
  Limits.Sigma.desc (fun x ↦
    X.ιSingularChainComplex x ≫ (X.singularChainComplexHomotopyIdSdIter (hU.m x)).hom n (n + 1))

@[reassoc]
lemma ι_hρ {n : ℕ} (x : toSSet.obj X _⦋n⦌) :
    X.ιSingularChainComplex x ≫ hU.hρ (R := R) n =
      X.ιSingularChainComplex x ≫
        (X.singularChainComplexHomotopyIdSdIter (hU.m x)).hom n (n + 1) :=
  Sigma.ι_desc ..

@[inherit_doc hρ]
noncomputable def hρ' (n m : ℕ) :
    (X.singularChainComplex R).X n ⟶ (X.singularChainComplex R).X m :=
  if h : n + 1 = m then hU.hρ n ≫ eqToHom (by simp [h]) else 0

@[simp]
lemma hρ'_eq (n : ℕ) : hU.hρ' (R := R) n (n + 1) = hU.hρ n := by simp [hρ']

lemma hρ'_zero (n m : ℕ) (h : n + 1 ≠ m) : hU.hρ' (R := R) n m = 0 := by grind [hρ']

/-- Auxiliary definition for
`ρ : X.singularChainComplex R ⟶ (toSSet.subcomplexOfSets U).toSSet.chainComplex R`. -/
noncomputable def ρ' :
    X.singularChainComplex R ⟶ X.singularChainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap hU.hρ'

lemma ρ'_eq_sub :
    hU.ρ' = 𝟙 (X.singularChainComplex R) - Homotopy.nullHomotopicMap hU.hρ' := rfl

/-- The morphism `ρ'` is homotopic to the identity. -/
noncomputable def homotopyρ'Id :
    _root_.Homotopy hU.ρ' (𝟙 (X.singularChainComplex R)) :=
  (Homotopy.equivSubZero.symm
    (.trans (.ofEq (by simp [ρ'_eq_sub])) (.nullHomotopy hU.hρ' hU.hρ'_zero))).symm

@[reassoc]
lemma ι_ρ'_f {n : ℕ} (x : (toSSet.obj X) _⦋n⦌)
    (hx : x ∈ (toSSet.subcomplexOfSets U).obj _) :
    X.ιSingularChainComplex (R := R) x ≫ hU.ρ'.f n = X.ιSingularChainComplex x := by
  dsimp [ρ'_eq_sub]
  simp only [Preadditive.comp_sub, Category.comp_id, sub_eq_self]
  replace hx := (hU.m_eq_zero_iff x).2 hx
  obtain _ | n := n
  · simp [ChainComplex.nullHomotopicMap_f_zero, ι_hρ_assoc,
      hx, singularChainComplexHomotopyIdSdIter_hom]
  · rw [ChainComplex.nullHomotopicMap_f_succ]
    simp only [hρ'_eq, Preadditive.comp_add, ι_singularChainComplex_d_assoc, Int.reduceNeg,
      Preadditive.sum_comp, Linear.smul_comp, ι_hρ_assoc]
    rw [Finset.sum_eq_zero (fun i hi ↦ ?_), hx]
    · simp [singularChainComplexHomotopyIdSdIter_hom]
    · rw [ι_hρ, singularChainComplexHomotopyIdSdIter_hom,
        Finset.sum_eq_zero (fun ⟨j, hj⟩ _ ↦ by have := hU.m_δ_le x i; lia), comp_zero, smul_zero]

@[simp]
lemma ρ'_zero : hU.ρ'.f 0 = 𝟙 ((X.singularChainComplex R).X 0) :=
  singularChainComplexX_hom_ext (fun x ↦ by
    rw [Category.comp_id, ι_ρ'_f]
    simp [hU.subcomplexOfSets_obj_zero])

@[reassoc (attr := simp)]
lemma chainComplexMap_ι_ρ' :
    SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R ≫ hU.ρ' =
        SSet.chainComplexMap (toSSet.subcomplexOfSets U).ι R := by
  ext n ⟨x, hx⟩
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  erw [SSet.ι_chainComplexMap_f]
  exact hU.ι_ρ'_f (R := R) x hx

@[reassoc]
lemma ι_singularChainComplexSdIter_π_eq_zero
    {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) (k : ℕ) (hk : hU.m x ≤ k) :
    X.ιSingularChainComplex x ≫ (X.singularChainComplexSdIter k).f n ≫
      ((sSetPairOfSets U).chainComplexπ R).f n = 0 := by
  simp only [ι_singularChainComplexSdIter_f_assoc,
    Preadditive.sum_comp, Linear.units_smul_comp]
  rw [Finset.sum_eq_zero]
  intro σ _
  erw [SSetPair.ιChainComplex_π_f_eq_zero_of_subcomplex _ _ _
    ((hU.sdIterIsSmall_m x).of_le hk σ)]
  rw [smul_zero]

-- to be moved, as it does not depend on `hU`
variable (U) in
omit hU in
@[reassoc (attr := simp)]
lemma map_subtypeVal_chainComplexπ (i : ι) (n : ℕ) :
    (singularChainComplexMap (ofHom (X := U i) (Y := X)
      ⟨Subtype.val, by fun_prop⟩) R).f n ≫
    ((sSetPairOfSets U).chainComplexπ R).f n = 0 :=
  singularChainComplexX_hom_ext (fun x ↦ by
    simp only [ι_singularChainComplexMap_assoc, comp_zero]
    apply SSetPair.ιChainComplex_π_f_eq_zero_of_subcomplex
    rw [toSSet.mem_subcomplexOfSets_iff']
    exact ⟨i, _, rfl⟩)

-- to be moved, as it does not depend on `hU`
variable (U) in
omit hU in
@[reassoc]
lemma ι_singularChainComplexHomotopyIdSd_hom_π_eq_zero
    {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) (hx : x ∈ (toSSet.subcomplexOfSets U).obj _) :
    X.ιSingularChainComplex x ≫
      X.singularChainComplexHomotopyIdSd.hom n (n + 1) ≫
        ((sSetPairOfSets U).chainComplexπ R).f (n + 1) = 0 := by
  rw [toSSet.mem_subcomplexOfSets_iff'] at hx
  obtain ⟨i, f, rfl⟩ := hx
  simp [ι_map_app_singularChainComplexHomotopyIdSd_hom_assoc]

@[reassoc]
lemma ι_singularChainComplexSdIter_homotopyIdSd_hom_π_eq_zero
    {n : ℕ} (x : (toSSet.obj X) _⦋n⦌) (k : ℕ) (hk : hU.m x ≤ k) :
    X.ιSingularChainComplex x ≫ (X.singularChainComplexSdIter k).f n ≫
      X.singularChainComplexHomotopyIdSd.hom n (n + 1) ≫
      ((sSetPairOfSets U).chainComplexπ R).f (n + 1) = 0 := by
  simp only [ι_singularChainComplexSdIter_f_assoc,
    Preadditive.sum_comp, Linear.units_smul_comp]
  rw [Finset.sum_eq_zero]
  intro σ _
  rw [ι_singularChainComplexHomotopyIdSd_hom_π_eq_zero _ _
    ((hU.sdIterIsSmall_m x).of_le hk σ), smul_zero]

@[reassoc]
lemma ι_comp_sdIter_f_sub_ρ' {n : ℕ} (x : toSSet.obj X _⦋n + 1⦌) :
    X.ιSingularChainComplex (R := R) x ≫
        ((X.singularChainComplexSdIter (hU.m x)).f (n + 1) - hU.ρ'.f (n + 1)) =
    ∑ (i : Fin (n + 2)),
      ∑ (j : Fin (hU.m x)) with hU.m ((toSSet.obj X).δ i x) ≤ j.val,
        (-1) ^ (i.val + 1) • X.ιSingularChainComplex ((toSSet.obj X).δ i x) ≫
          (X.singularChainComplexSdIter j.val).f n ≫
            X.singularChainComplexHomotopyIdSd.hom _ _ := by
  calc
    _ = X.ιSingularChainComplex x ≫ (Homotopy.nullHomotopicMap (hU.hρ' -
        (X.singularChainComplexHomotopyIdSdIter (hU.m x)).hom)).f (n + 1) := by
      simp [ρ'_eq_sub,
        (X.singularChainComplexHomotopyIdSdIter (hU.m x)).eq_sub_nullHomotopicMap]
    _ = X.ιSingularChainComplex x ≫
          (X.singularChainComplex R).d (n + 1) n ≫
            (hU.hρ n - (X.singularChainComplexHomotopyIdSdIter (hU.m x)).hom n (n + 1)) := by
        simp only [ChainComplex.nullHomotopicMap_f_succ, Pi.sub_apply,
          Preadditive.comp_sub, Preadditive.sub_comp, Preadditive.comp_add, hρ'_eq]
        erw [hU.ι_hρ_assoc]
        abel
    _ = _ := by
      rw [ι_singularChainComplex_d_assoc, Preadditive.sum_comp]
      congr
      ext i
      rw [Linear.smul_comp, ← Finset.smul_sum, pow_succ, ← smul_smul, neg_smul, one_smul]
      congr 1
      generalize hy : (toSSet.obj X).δ i x = y
      have hy' : hU.m y ≤ hU.m x := by simpa [← hy] using hU.m_δ_le x i
      let t (j : Fin (hU.m x)) :=
        X.ιSingularChainComplex y ≫ (X.singularChainComplexSdIter (R := R) j.val).f n ≫
          X.singularChainComplexHomotopyIdSd.hom _ (n + 1)
      calc
        _ = ∑ (j : Fin (hU.m y)), t (j.castLE hy') - ∑ j, t j  := by
          rw [Preadditive.comp_sub, singularChainComplexHomotopyIdSdIter_hom,
            Preadditive.comp_sum, ι_hρ, singularChainComplexHomotopyIdSdIter_hom,
            Preadditive.comp_sum]
          dsimp [t]
        _ = - ∑ (j : Fin (hU.m x)) with hU.m y ≤ j.val, t j := by
          rw [Fin.sum_univ_eq_sum_of_le _ _ hy']
          abel

@[reassoc]
lemma ι_ρ'_f_π_f {n : ℕ} (x : toSSet.obj X _⦋n⦌) :
  X.ιSingularChainComplex x ≫ hU.ρ'.f n ≫ ((sSetPairOfSets U).chainComplexπ R).f n =
    X.ιSingularChainComplex x ≫
      (X.singularChainComplexSdIter (hU.m x)).f n ≫
        ((sSetPairOfSets U).chainComplexπ R).f n := by
  obtain _ | n := n
  · simp
  · symm
    rw [← sub_eq_zero, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
      hU.ι_comp_sdIter_f_sub_ρ'_assoc]
    simp only [Preadditive.sum_comp]
    refine Finset.sum_eq_zero (fun i _ ↦ Finset.sum_eq_zero (fun ⟨j, hj⟩ hj' ↦ ?_))
    rw [Linear.smul_comp, Category.assoc, Category.assoc,
      hU.ι_singularChainComplexSdIter_homotopyIdSd_hom_π_eq_zero, smul_zero]
    simpa using hj'

@[reassoc (attr := simp)]
lemma ρ'_f_chainComplexπ_f (n : ℕ) :
    hU.ρ'.f n ≫ ((sSetPairOfSets U).chainComplexπ R).f n = 0 := by
  refine singularChainComplexX_hom_ext (fun x ↦ ?_)
  rw [ι_ρ'_f_π_f, comp_zero,
    hU.ι_singularChainComplexSdIter_π_eq_zero _ _ (by simp)]

@[reassoc (attr := simp)]
lemma ρ'_chainComplexπ :
    hU.ρ' ≫ (sSetPairOfSets U).chainComplexπ R = 0 := by
  cat_disch

/-- Given a family `U : ι → Set X` of subsets of a topological space `X` which
satisfies the condition `SmallSimplicesCondition U`, this is the retraction
`X.singularChainComplex R ⟶ (toSSet.subcomplexOfSets U).toSSet.chainComplex R`
to the inclusion that is part of the definition of the homotopy equivalence
`homotopyEquiv` (see below) between `(toSSet.subcomplexOfSets U).toSSet.chainComplex R`
and the singular chain complex of `X`. -/
@[no_expose]
noncomputable def ρ :
    X.singularChainComplex R ⟶
      (toSSet.subcomplexOfSets U).toSSet.chainComplex R :=
  (KernelFork.IsLimit.lift'
    ((sSetPairOfSets U).isLimitKernelForkChainComplex R) _ hU.ρ'_chainComplexπ).1

@[reassoc (attr := simp)]
lemma ρ'_ι :
    hU.ρ ≫ SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R = hU.ρ' :=
  (KernelFork.IsLimit.lift'
    ((sSetPairOfSets U).isLimitKernelForkChainComplex R) _ hU.ρ'_chainComplexπ).2

@[reassoc (attr := simp)]
lemma ι_ρ :
    SSet.chainComplexMap
      (TopCat.toSSet.subcomplexOfSets U).ι R ≫ hU.ρ = 𝟙 _ := by
  rw [← cancel_mono (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R),
    Category.assoc]
  erw [hU.ρ'_ι, hU.chainComplexMap_ι_ρ', Category.id_comp]

variable (R) in
/-- Given a family `U : ι → Set X` of subsets of a topological space `X` which
satisfies the condition `SmallSimplicesCondition U`, the inclusion of
`(toSSet.subcomplexOfSets U).toSSet.chainComplex R` in the singular chain
complex of `X` is an homotopy equivalence. -/
@[simps]
noncomputable def homotopyEquiv :
    HomotopyEquiv
      ((toSSet.subcomplexOfSets U).toSSet.chainComplex R)
      (X.singularChainComplex R) where
  hom := SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R
  inv := hU.ρ
  homotopyHomInvId := .ofEq hU.ι_ρ
  homotopyInvHomId := .trans (.ofEq hU.ρ'_ι) hU.homotopyρ'Id

variable (R) in
@[inherit_doc homotopyEquiv]
lemma homotopyEquivalences :
    homotopyEquivalences _ _
      (SSet.chainComplexMap (TopCat.toSSet.subcomplexOfSets U).ι R) :=
  ⟨hU.homotopyEquiv R, rfl⟩

end SmallSimplicesCondition

end TopCat
