/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Singular
import Submission.Homology.UCT.Dual
import Submission.Homology.SimplicialSplitting

/-!
# The bridge between `Hcoh` and the dual of the chain complex

`Submission/Cohomology/Basic.lean` defines cohomology by hand, as the quotient
`ker δ ⧸ im δ` of the module of cochains `Cochain S R n = S _⦋n⦌ → R`.
`Submission/Homology/UCT/Dual.lean` instead forms the dual complex `homDual K G` of a complex of
abelian groups and takes its `HomologicalComplex.homology`.

Both describe the same thing: the degree `n` chain group `(CsingSSet S).X n` is the free abelian
group on `S _⦋n⦌`, so a homomorphism `(CsingSSet S).X n ⟶ R` *is* a function `S _⦋n⦌ → R`, and
under that identification the differential of `homDual` is exactly `coboundary`.

## Main definitions

* `Submission.gen σ` — the generator of `(CsingSSet S).X n` attached to an `n`-simplex `σ`.
* `Submission.dualXEquiv S R n` — `((CsingSSet S).X n ⟶ R) ≃+ Cochain S R n`.

## Main results

* `Submission.dualXEquiv_d` — the degreewise identification intertwines the differentials.
-/

open CategoryTheory Limits Simplicial

noncomputable section

namespace Submission

/-! ### Elementary lemmas about morphisms of abelian groups -/

/-- A finite sum of homomorphisms of abelian groups is computed pointwise. -/
theorem AddCommGrpCat.sum_apply {M N : AddCommGrpCat.{0}} {ι : Type*} (s : Finset ι)
    (g : ι → (M ⟶ N)) (x : M) : (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.AddCommGrpCat.hom_add_apply, ih]

/-- An integer multiple of a homomorphism of abelian groups is computed pointwise. -/
theorem AddCommGrpCat.zsmul_apply {M N : AddCommGrpCat.{0}} (k : ℤ) (g : M ⟶ N) (x : M) :
    (k • g) x = k • g x := rfl

/-! ### The generators of the chain groups -/

variable {S : SSet.{0}}

/-- The generator of the degree `n` chain group `(CsingSSet S).X n` attached to an
`n`-simplex `σ`, i.e. the image of `1 : ℤ` under the inclusion of the `σ`-summand. -/
def gen {n : ℕ} (σ : S _⦋n⦌) : (CsingSSet S).X n :=
  S.ιChainComplex (R := AddCommGrpCat.of ℤ) σ (1 : ℤ)

theorem gen_def {n : ℕ} (σ : S _⦋n⦌) :
    gen σ = S.ιChainComplex (R := AddCommGrpCat.of ℤ) σ (1 : ℤ) := rfl

theorem apply_gen {n : ℕ} {T : AddCommGrpCat.{0}} (φ : (CsingSSet S).X n ⟶ T) (σ : S _⦋n⦌) :
    φ (gen σ) = (S.ιChainComplex (R := AddCommGrpCat.of ℤ) σ ≫ φ) (1 : ℤ) := rfl

/-- The homomorphism `ℤ ⟶ G` sending `1` to a prescribed element. -/
def intHom {G : AddCommGrpCat.{0}} (g : G) : AddCommGrpCat.of ℤ ⟶ G :=
  AddCommGrpCat.ofHom (zmultiplesHom G g)

@[simp]
theorem intHom_one {G : AddCommGrpCat.{0}} (g : G) : intHom g (1 : ℤ) = g := by
  simp [intHom]

theorem intHom_ext {G : AddCommGrpCat.{0}} {u v : AddCommGrpCat.of ℤ ⟶ G}
    (h : u (1 : ℤ) = v (1 : ℤ)) : u = v :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext_int h)

/-- The map prescribed on generators by `ccDesc`, evaluated on a generator. -/
theorem ccDesc_gen {n : ℕ} {T : AddCommGrpCat.{0}} (v : S _⦋n⦌ → (AddCommGrpCat.of ℤ ⟶ T))
    (σ : S _⦋n⦌) : ccDesc v (gen σ) = v σ (1 : ℤ) := by
  rw [apply_gen, ι_ccDesc]

/-- Two maps out of a chain group agree as soon as they agree on the generators. -/
theorem chainComplexX_hom_ext {n : ℕ} {T : AddCommGrpCat.{0}}
    {u v : (CsingSSet S).X n ⟶ T} (h : ∀ σ : S _⦋n⦌, u (gen σ) = v (gen σ)) : u = v :=
  SSet.chainComplex_hom_ext fun σ ↦ intHom_ext (h σ)

/-! ### The degreewise identification -/

variable (S) (R : Type) [CommRing R]

/-- A homomorphism out of the degree `n` chain group of a simplicial set is the same thing as an
`n`-cochain: the chain group is free on the `n`-simplices. -/
def dualXEquiv (n : ℕ) :
    ((CsingSSet S).X n ⟶ AddCommGrpCat.of R) ≃+ Cochain S R n where
  toFun φ σ := φ (gen σ)
  invFun f := ccDesc fun σ ↦ intHom (f σ)
  left_inv φ := chainComplexX_hom_ext fun σ ↦ by
    rw [ccDesc_gen, intHom_one]
  right_inv f := by
    funext σ
    dsimp only
    rw [ccDesc_gen, intHom_one]
  map_add' φ ψ := by
    funext σ
    dsimp only
    exact _root_.AddCommGrpCat.hom_add_apply φ ψ (gen σ)

@[simp]
theorem dualXEquiv_apply (n : ℕ) (φ : (CsingSSet S).X n ⟶ AddCommGrpCat.of R) (σ : S _⦋n⦌) :
    dualXEquiv S R n φ σ = φ (gen σ) := rfl

@[simp]
theorem dualXEquiv_symm_apply (n : ℕ) (f : Cochain S R n) (σ : S _⦋n⦌) :
    (dualXEquiv S R n).symm f (gen σ) = f σ :=
  congrFun ((dualXEquiv S R n).apply_symm_apply f) σ

variable {S R}

/-- The differential of the chain complex, evaluated on a generator, is the alternating sum of the
generators attached to the faces. -/
theorem d_gen {n : ℕ} (σ : S _⦋n + 1⦌) :
    (CsingSSet S).d (n + 1) n (gen σ) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • gen (SSet.face S i σ) := by
  rw [apply_gen, SSet.ιChainComplex_d, AddCommGrpCat.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ AddCommGrpCat.zsmul_apply _ _ _

/-- The degreewise identification of `dualXEquiv` intertwines the differential of the dual
complex with the coboundary operator on cochains. -/
theorem dualXEquiv_d (n : ℕ) (φ : (CsingSSet S).X n ⟶ AddCommGrpCat.of R) :
    dualXEquiv S R (n + 1) ((homDual (CsingSSet S) (AddCommGrpCat.of R)).d n (n + 1) φ) =
      coboundary S R n (dualXEquiv S R n φ) := by
  ext σ
  rw [dualXEquiv_apply, homDual_d_apply, coboundary_apply, apply_gen, ← Category.assoc,
    SSet.ιChainComplex_d, Preadditive.sum_comp, AddCommGrpCat.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, AddCommGrpCat.zsmul_apply, dualXEquiv_apply, apply_gen,
    zsmul_eq_mul]
  push_cast
  rfl

/-! ### The shape of the dual complex -/

/-- The dual of a chain complex indexed by `ℕ` is a cochain complex: the successor of `n` is
`n + 1`. -/
theorem symmDown_next (n : ℕ) : ((ComplexShape.down ℕ).symm).next n = n + 1 :=
  ComplexShape.next_eq' _ rfl

/-- In the dual of a chain complex indexed by `ℕ`, the predecessor of `m + 1` is `m`. -/
theorem symmDown_prev_succ (m : ℕ) : ((ComplexShape.down ℕ).symm).prev (m + 1) = m :=
  ComplexShape.prev_eq' _ rfl

/-- Nothing precedes degree `0` in the dual of a chain complex indexed by `ℕ`. -/
theorem symmDown_not_rel_zero (i : ℕ) : ¬ ((ComplexShape.down ℕ).symm).Rel i 0 :=
  fun h ↦ Nat.succ_ne_zero i h

/-- The zero homomorphism of abelian groups, applied to an element. -/
theorem zero_hom_apply {M N : AddCommGrpCat.{0}} (x : M) : (0 : M ⟶ N) x = 0 := rfl

variable (S R)

/-- Abbreviation for the dual cochain complex of the chain complex of a simplicial set. -/
abbrev dualComplex : HomologicalComplex AddCommGrpCat.{0} ((ComplexShape.down ℕ).symm) :=
  homDual (CsingSSet S) (AddCommGrpCat.of R)

theorem dualComplex_d_zero (i : ℕ) : (dualComplex S R).d i 0 = 0 :=
  HomologicalComplex.shape _ _ _ (symmDown_not_rel_zero i)

variable {S R}

theorem mem_cyclesSub_iff {n : ℕ} (φ : (dualComplex S R).X n) :
    φ ∈ cyclesSub (dualComplex S R) n ↔ (dualComplex S R).d n (n + 1) φ = 0 := by
  rw [← symmDown_next n]
  exact Iff.rfl

/-- Under `dualXEquiv`, the cocycles of the cochain complex of `S` correspond to the cycles of the
dual complex. -/
theorem dualXEquiv_mem_cocycles_iff {n : ℕ} (φ : (dualComplex S R).X n) :
    dualXEquiv S R n φ ∈ cocycles S R n ↔ φ ∈ cyclesSub (dualComplex S R) n := by
  rw [mem_cocycles_iff, mem_cyclesSub_iff, ← dualXEquiv_d n φ]
  exact ⟨fun h ↦ (dualXEquiv S R (n + 1)).injective (h.trans (map_zero _).symm),
    fun h ↦ by rw [h]; exact map_zero _⟩

variable (S R)

/-- Under `dualXEquiv`, cocycles correspond to cycles of the dual complex. -/
def dualCocyclesEquiv (n : ℕ) :
    cocycles S R n ≃+ cyclesSub (dualComplex S R) n where
  toFun f := ⟨(dualXEquiv S R n).symm f.1,
    (dualXEquiv_mem_cocycles_iff _).1 (by rw [AddEquiv.apply_symm_apply]; exact f.2)⟩
  invFun p := ⟨dualXEquiv S R n p.1, (dualXEquiv_mem_cocycles_iff _).2 p.2⟩
  left_inv f := Subtype.ext ((dualXEquiv S R n).apply_symm_apply f.1)
  right_inv p := Subtype.ext ((dualXEquiv S R n).symm_apply_apply p.1)
  map_add' f g := Subtype.ext (map_add (dualXEquiv S R n).symm f.1 g.1)

@[simp]
theorem dualCocyclesEquiv_coe (n : ℕ) (f : cocycles S R n) :
    ((dualCocyclesEquiv S R n f : cyclesSub (dualComplex S R) n) : (dualComplex S R).X n) =
      (dualXEquiv S R n).symm f.1 := rfl

/-- The image of the coboundaries under `dualCocyclesEquiv` is the subgroup of boundaries of the
dual complex. -/
theorem map_coboundariesIn (n : ℕ) :
    AddSubgroup.map (dualCocyclesEquiv S R n) (coboundariesIn S R n).toAddSubgroup =
      (AddMonoidHom.range
          ((dualComplex S R).d (((ComplexShape.down ℕ).symm).prev n) n).hom).addSubgroupOf
        (cyclesSub (dualComplex S R) n) := by
  ext p
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range,
    Submodule.mem_toAddSubgroup]
  cases n with
  | zero =>
      rw [dualComplex_d_zero]
      constructor
      · rintro ⟨f, hf, rfl⟩
        refine ⟨0, ?_⟩
        rw [zero_hom_apply]
        have h0 : (f : Cochain S R 0) = 0 := by
          have h : (f : Cochain S R 0) ∈ coboundaries S R 0 := hf
          rwa [coboundaries_zero, Submodule.mem_bot] at h
        show (0 : (dualComplex S R).X 0) = (dualXEquiv S R 0).symm (f : Cochain S R 0)
        rw [h0]
        exact (map_zero _).symm
      · rintro ⟨y, hy⟩
        refine ⟨0, Submodule.zero_mem _, Subtype.ext ?_⟩
        show (dualXEquiv S R 0).symm ((0 : cocycles S R 0) : Cochain S R 0) = p.1
        rw [← hy, zero_hom_apply, ZeroMemClass.coe_zero, map_zero]
        rfl
  | succ m =>
      rw [symmDown_prev_succ]
      constructor
      · rintro ⟨f, hf, rfl⟩
        obtain ⟨g, hg⟩ : ∃ g, coboundary S R m g = (f : Cochain S R (m + 1)) := hf
        refine ⟨(dualXEquiv S R m).symm g, (dualXEquiv S R (m + 1)).injective ?_⟩
        show dualXEquiv S R (m + 1) ((dualComplex S R).d m (m + 1) ((dualXEquiv S R m).symm g)) =
          dualXEquiv S R (m + 1) ((dualXEquiv S R (m + 1)).symm (f : Cochain S R (m + 1)))
        rw [dualXEquiv_d, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hg]
      · rintro ⟨y, hy⟩
        refine ⟨⟨coboundary S R m (dualXEquiv S R m y),
          by rw [mem_cocycles_iff, coboundary_coboundary]⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
        show (dualXEquiv S R (m + 1)).symm (coboundary S R m (dualXEquiv S R m y)) = p.1
        rw [← dualXEquiv_d, hy, AddEquiv.symm_apply_apply]

/-- **The bridge.**  The hand-made cohomology `Hcoh n S R` of a simplicial set agrees with the
homology of the dual of its chain complex. -/
def HcohEquivDualHomology (n : ℕ) : Hcoh n S R ≃+ (dualComplex S R).homology n :=
  (QuotientAddGroup.congr _ _ (dualCocyclesEquiv S R n) (map_coboundariesIn S R n)).trans
    homologyQuotEquiv

@[simp]
theorem HcohEquivDualHomology_mk (n : ℕ) (f : cocycles S R n) :
    HcohEquivDualHomology S R n (Hcoh.mk f) =
      homologyMk ((dualCocyclesEquiv S R n f : cyclesSub (dualComplex S R) n) :
        (dualComplex S R).X n) (dualCocyclesEquiv S R n f).2 := rfl

/-- A cocycle represents a nonzero cohomology class if its associated homomorphism on chains
takes a nonzero value on some cycle. -/
theorem Hcoh.mk_ne_zero_of_eval_cycle {n : ℕ} (f : cocycles S R n)
    (z : (CsingSSet S).X n)
    (hz : (CsingSSet S).d n ((ComplexShape.down ℕ).next n) z = 0)
    (heval : (dualXEquiv S R n).symm (f : Cochain S R n) z ≠ 0) :
    Hcoh.mk f ≠ 0 := by
  intro hzero
  apply heval
  have hdual : HcohEquivDualHomology S R n (Hcoh.mk f) = 0 := by
    rw [hzero, map_zero]
  rw [HcohEquivDualHomology_mk] at hdual
  have hvalue := congrArg
    (fun x : (dualComplex S R).homology n ↦
      ev (CsingSSet S) (AddCommGrpCat.of R) n x (homologyMk z hz)) hdual
  rw [ev_homologyMk, evCocycle_homologyMk] at hvalue
  simpa using hvalue

/-! ### Naturality -/

variable {S R}

/-- The chain map induced by a morphism of simplicial sets sends generators to generators. -/
theorem chainComplexMap_gen {T : SSet.{0}} (φ : S ⟶ T) {n : ℕ} (σ : S _⦋n⦌) :
    (SSet.chainComplexMap φ (AddCommGrpCat.of ℤ)).f n (gen σ) = gen (φ.app _ σ) := by
  rw [apply_gen, SSet.ι_chainComplexMap_f]
  rfl

/-- Under `dualXEquiv`, the map of dual complexes induced by a morphism of simplicial sets is the
pullback of cochains. -/
theorem dualXEquiv_homDualMap {T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) (ψ : (dualComplex T R).X n) :
    dualXEquiv S R n ((homDualMap (SSet.chainComplexMap φ (AddCommGrpCat.of ℤ))
        (AddCommGrpCat.of R)).f n ψ) = Cochain.pullback φ n (dualXEquiv T R n ψ) := by
  ext σ
  rw [dualXEquiv_apply, homDualMap_f_apply, Cochain.pullback_apply, dualXEquiv_apply,
    ConcreteCategory.comp_apply, chainComplexMap_gen]

/-- **Naturality of the bridge.**  The identification of `Hcoh` with the homology of the dual
complex is compatible with the maps induced by a morphism of simplicial sets. -/
theorem HcohEquivDualHomology_naturality {T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) (x : Hcoh n T R) :
    HcohEquivDualHomology S R n (Hcoh.map R φ n x) =
      HomologicalComplex.homologyMap
        (homDualMap (SSet.chainComplexMap φ (AddCommGrpCat.of ℤ)) (AddCommGrpCat.of R)) n
        (HcohEquivDualHomology T R n x) := by
  refine Hcoh.induction_on x fun f ↦ ?_
  have key : (homDualMap (SSet.chainComplexMap φ (AddCommGrpCat.of ℤ)) (AddCommGrpCat.of R)).f n
      ((dualCocyclesEquiv T R n f : cyclesSub (dualComplex T R) n) : (dualComplex T R).X n) =
      ((dualCocyclesEquiv S R n (cocyclesMap R φ n f) : cyclesSub (dualComplex S R) n) :
        (dualComplex S R).X n) := by
    refine (dualXEquiv S R n).injective ?_
    rw [dualXEquiv_homDualMap]
    show Cochain.pullback φ n (dualXEquiv T R n ((dualXEquiv T R n).symm (f : Cochain T R n))) =
      dualXEquiv S R n ((dualXEquiv S R n).symm ((cocyclesMap R φ n f : Cochain S R n)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rfl
  have h2 : (dualComplex S R).d n (((ComplexShape.down ℕ).symm).next n)
      ((homDualMap (SSet.chainComplexMap φ (AddCommGrpCat.of ℤ)) (AddCommGrpCat.of R)).f n
        ((dualCocyclesEquiv T R n f : cyclesSub (dualComplex T R) n) :
          (dualComplex T R).X n)) = 0 := by
    rw [key]
    exact (dualCocyclesEquiv S R n (cocyclesMap R φ n f)).2
  rw [Hcoh.map_mk, HcohEquivDualHomology_mk, HcohEquivDualHomology_mk,
    homologyMap_homologyMk _ _ _ h2]
  exact congrArg (homologyMkHom (dualComplex S R) n) (Subtype.ext key.symm)

/-! ### The singular case -/

variable (R) in
/-- **The bridge for singular cohomology.**  The hand-made singular cohomology `Hsing n X R` of a
topological space agrees with the homology of the dual of its singular chain complex. -/
def HsingEquivDualHomology (X : TopCat.{0}) (n : ℕ) :
    Hsing n X R ≃+ (homDual (Csing X) (AddCommGrpCat.of R)).homology n :=
  HcohEquivDualHomology (TopCat.toSSet.obj X) R n

/-- **Naturality of the bridge in the space.** -/
theorem HsingEquivDualHomology_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : Hsing n Y R) :
    HsingEquivDualHomology R X n (Hsing.map f n x) =
      HomologicalComplex.homologyMap (homDualMap (CsingMap f) (AddCommGrpCat.of R)) n
      (HsingEquivDualHomology R Y n x) :=
  HcohEquivDualHomology_naturality (TopCat.toSSet.map f) n x

/-- Surjectivity of a concrete singular-cohomology pullback transfers across the bridge to the
corresponding homology map of dual singular-chain complexes. -/
theorem surjective_dualHomologyMap_of_surjective_Hsing_map {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (h : Function.Surjective (Hsing.map (R := R) f n)) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (homDualMap (CsingMap f) (AddCommGrpCat.of R)) n) := by
  intro z
  obtain ⟨x, hx⟩ := h ((HsingEquivDualHomology R X n).symm z)
  refine ⟨HsingEquivDualHomology R Y n x, ?_⟩
  rw [← HsingEquivDualHomology_naturality, hx, AddEquiv.apply_symm_apply]

end Submission
