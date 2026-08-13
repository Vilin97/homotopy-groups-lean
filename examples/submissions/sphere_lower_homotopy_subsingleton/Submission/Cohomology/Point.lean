/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.SingularSqTwo
import Submission.Cohomology.DualShortExact
import Submission.Homology.Contractible
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Singular cohomology of a point and of contractible spaces

The singular simplicial set of a point has exactly one simplex in every degree.  Its coboundaries
therefore alternate between zero and the identity, so its positive-degree cohomology vanishes.
Homotopy invariance then gives the same conclusion for every contractible space.

## Main results

* `Submission.subsingleton_Hsing_punit` -- positive cohomology of a point is trivial;
* `Submission.subsingleton_Hsing_of_contractible` -- positive cohomology of a contractible space
  is trivial;
* `Submission.isZero_dualHomology_of_subsingleton_Hsing` -- transfer of concrete vanishing to
  the categorical dual-complex model;
* `Submission.isZero_dualHomology_of_contractible` -- the corresponding categorical statement
  for the dual singular-chain complex.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial

noncomputable section

namespace Submission

abbrev cohomologyPoint : TopCat.{0} := TopCat.of PUnit.{1}

private instance pointSimplexSubsingleton (n : ℕ) :
    Subsingleton ((TopCat.toSSet.obj cohomologyPoint) _⦋n⦌) where
  allEq σ τ := by
    exact ((CategoryTheory.mono_iff_injective
      ((TopCat.toSSetIsoConst cohomologyPoint).hom.app _)).1 (by infer_instance))
        (PUnit.ext _ _)

/-- The unique singular `n`-simplex of a point. -/
def pointSimplex (n : ℕ) : (TopCat.toSSet.obj cohomologyPoint) _⦋n⦌ :=
  (TopCat.toSSetIsoConst cohomologyPoint).inv.app _ PUnit.unit

variable (R : Type) [CommRing R]

private theorem point_coboundary_apply (n : ℕ)
    (f : SingCochain cohomologyPoint R n)
    (σ : (TopCat.toSSet.obj cohomologyPoint) _⦋n + 1⦌) :
    coboundary (TopCat.toSSet.obj cohomologyPoint) R n f σ =
      (if Even (n + 2) then 0 else 1) * f (pointSimplex n) := by
  rw [coboundary_apply]
  simp_rw [Subsingleton.elim (SSet.face _ _ σ) (pointSimplex n)]
  rw [← Finset.sum_mul, Fin.sum_neg_one_pow]

private theorem point_cocycle_eq_zero_of_odd {n : ℕ} (hn : Odd n)
    (f : cocycles (TopCat.toSSet.obj cohomologyPoint) R n) : (f : SingCochain cohomologyPoint R n) = 0 := by
  apply Cochain.ext
  intro σ
  have hf := congrFun f.2 (pointSimplex (n + 1))
  rw [point_coboundary_apply R n, if_neg (by simpa using hn.add_even ⟨1, rfl⟩), one_mul,
    Cochain.zero_apply] at hf
  rw [Subsingleton.elim σ (pointSimplex n), hf]
  rfl

private theorem point_cochain_is_coboundary_of_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0)
    (f : SingCochain cohomologyPoint R n) :
    f ∈ coboundaries (TopCat.toSSet.obj cohomologyPoint) R n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨(fun _ ↦ f (pointSimplex (m + 1)) : SingCochain cohomologyPoint R m), ?_⟩
  apply Cochain.ext
  intro σ
  rw [point_coboundary_apply R m]
  have hm : ¬ Even (m + 2) := by
    simpa [Nat.even_add_one] using hn
  rw [if_neg hm, one_mul]
  exact congrArg f (Subsingleton.elim (pointSimplex (m + 1)) σ)

/-- The positive-degree singular cohomology of a point is trivial. -/
theorem subsingleton_Hsing_punit (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (Hsing n cohomologyPoint R) := by
  constructor
  intro x y
  suffices hz : ∀ z : Hsing n cohomologyPoint R, z = 0 by rw [hz x, hz y]
  intro z
  refine Hcoh.induction_on z fun f ↦ (Hcoh.mk_eq_zero_iff f).2 ?_
  rcases n.even_or_odd with he | ho
  · exact point_cochain_is_coboundary_of_even R he hn f
  · rw [point_cocycle_eq_zero_of_odd R ho f]
    exact Submodule.zero_mem _

/-- A constant map induces the zero pullback on positive-degree singular cohomology. -/
theorem Hsing.map_const_eq_zero {X Y : TopCat.{0}} (y : Y)
    (n : ℕ) (hn : n ≠ 0) :
    Hsing.map (R := R) (TopCat.const y : X ⟶ Y) n = 0 := by
  letI : Subsingleton (Hsing n cohomologyPoint R) :=
    subsingleton_Hsing_punit R n hn
  have hconst : (TopCat.const y : X ⟶ Y) = toPt X ≫ ptIncl y := by
    ext x
    rfl
  rw [hconst, Hsing.map_comp]
  ext a
  rw [LinearMap.comp_apply]
  have hpoint : Hsing.map (R := R) (ptIncl y) n a = 0 :=
    Subsingleton.elim _ _
  simp [hpoint]

/-- The positive-degree singular cohomology of a contractible space is trivial. -/
theorem subsingleton_Hsing_of_contractible {X : TopCat.{0}} [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (Hsing n X R) := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨H⟩ := nonempty_contractibleHomotopy x
  let e : Hsing n X R ≃ₗ[R] Hsing n cohomologyPoint R :=
    hsingLinearEquivOfHomotopyEquiv (ptIncl x) (toPt X)
      (ptIncl_comp_toPt x ▸ TopCat.Homotopy.refl (𝟙 cohomologyPoint)) H n
  letI : Subsingleton (Hsing n cohomologyPoint R) := subsingleton_Hsing_punit R n hn
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim (e a) (e b))⟩

/-- Concrete singular-cohomology vanishing transfers across the bridge to homology of the dual
singular-chain complex. -/
theorem isZero_dualHomology_of_subsingleton_Hsing {X : TopCat.{0}} (n : ℕ)
    [Subsingleton (Hsing n X R)] :
    IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) := by
  let e := HsingEquivDualHomology R X n
  letI : Subsingleton ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) :=
    ⟨fun a b ↦ e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance

/-- Vanishing in the categorical dual-complex model transfers across the bridge to concrete
singular cohomology. -/
theorem subsingleton_Hsing_of_isZero_dualHomology {X : TopCat.{0}} (n : ℕ)
    (h : IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology n)) :
    Subsingleton (Hsing n X R) := by
  let e := HsingEquivDualHomology R X n
  letI : Subsingleton ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp h
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim (e a) (e b))⟩

/-- The cohomology of the dual singular-chain complex of a contractible space vanishes in every
positive degree. -/
theorem isZero_dualHomology_of_contractible {X : TopCat.{0}} [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) :
    IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) := by
  letI : Subsingleton (Hsing n X R) := subsingleton_Hsing_of_contractible R n hn
  exact isZero_dualHomology_of_subsingleton_Hsing R n

/-! ### Totally disconnected spaces -/

/-- The singular chains of a totally disconnected space deformation-retract onto a complex
concentrated in degree zero. -/
def csingHomotopyEquivSingleOfTotallyDisconnected (X : TopCat.{0})
    [TotallyDisconnectedSpace X] :
    HomotopyEquiv (Csing X)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj
        (∐ fun _ : X ↦ AddCommGrpCat.of ℤ)) :=
  (HomotopyEquiv.ofIso
    (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      AddCommGrpCat.{0} (AddCommGrpCat.of ℤ) X)).trans
    (ChainComplex.alternatingConstHomotopyEquiv (∐ fun _ : X ↦ AddCommGrpCat.of ℤ))

/-- Positive-degree cohomology of the dual singular-chain complex vanishes for a totally
disconnected space. -/
theorem isZero_dualHomology_of_totallyDisconnected {X : TopCat.{0}}
    [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) := by
  let Q : AddCommGrpCat.{0} := ∐ fun _ : X ↦ AddCommGrpCat.of ℤ
  let K : ChainComplex AddCommGrpCat.{0} ℕ := (ChainComplex.single₀ AddCommGrpCat.{0}).obj Q
  have hzX : IsZero ((homDual K (AddCommGrpCat.of R)).X n) := by
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro f g
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 Q n hn).eq_of_src f g
  have hzH : IsZero ((homDual K (AddCommGrpCat.of R)).homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hzX
  exact IsZero.of_iso hzH
    ((homDualHomotopyEquiv (csingHomotopyEquivSingleOfTotallyDisconnected X)
      (AddCommGrpCat.of R)).toHomologyIso n).symm

/-- Positive-degree singular cohomology of a totally disconnected space is trivial. -/
theorem subsingleton_Hsing_of_totallyDisconnected {X : TopCat.{0}}
    [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (Hsing n X R) := by
  let e := HsingEquivDualHomology R X n
  have hz := isZero_dualHomology_of_totallyDisconnected R n hn (X := X)
  letI : Subsingleton ((homDual (Csing X) (AddCommGrpCat.of R)).homology n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hz
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim (e a) (e b))⟩

end Submission
