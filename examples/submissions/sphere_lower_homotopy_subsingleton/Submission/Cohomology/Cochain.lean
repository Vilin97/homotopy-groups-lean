/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring

/-!
# Simplicial cochains

For a simplicial set `S : SSet.{0}` and a commutative ring `R` we define the module of
`n`-cochains `Submission.Cochain S R n := S _⦋n⦌ → R`, the coboundary operator

`(coboundary f) σ = ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) * f (S.face i σ)`,

and we prove `coboundary ∘ coboundary = 0`.

Applied to `S = TopCat.toSSet.obj X` this is the complex of singular cochains of a topological
space `X`; see `Submission/Cohomology/Singular.lean`.

## Main definitions

* `Submission.SSet.restrict S h σ` : the restriction of a simplex `σ` along a morphism `h` of the
  simplex category.  This is the basic operation out of which faces, front faces and back faces
  are built.
* `Submission.SSet.face S i σ` : the `i`-th face of a simplex.
* `Submission.Cochain S R n` : the `R`-module of `n`-cochains.
* `Submission.coboundary S R n : Cochain S R n →ₗ[R] Cochain S R (n + 1)`.
* `Submission.Cochain.pullback φ n : Cochain T R n →ₗ[R] Cochain S R n`, the map induced by a
  morphism of simplicial sets `φ : S ⟶ T`.

## Main results

* `Submission.coboundary_coboundary` : `coboundary (coboundary f) = 0`.
* `Submission.pullback_coboundary` : the pullback is a map of cochain complexes.
-/

namespace Submission

open CategoryTheory Simplicial

namespace SSet

/-- Restriction of an `b`-simplex of `S` along a morphism `h : ⦋a⦌ ⟶ ⦋b⦌` of the simplex
category, giving an `a`-simplex. -/
def restrict (S : _root_.SSet.{0}) {a b : ℕ} (h : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌)
    (σ : S _⦋b⦌) : S _⦋a⦌ :=
  S.map h.op σ

variable {S : _root_.SSet.{0}}

@[simp]
theorem restrict_id {a : ℕ} (σ : S _⦋a⦌) : restrict S (𝟙 _) σ = σ := by
  simp [restrict]

theorem restrict_restrict {a b c : ℕ} (h₁ : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌)
    (h₂ : (⦋b⦌ : SimplexCategory) ⟶ ⦋c⦌) (σ : S _⦋c⦌) :
    restrict S h₁ (restrict S h₂ σ) = restrict S (h₁ ≫ h₂) σ := by
  simp only [restrict, op_comp, Functor.map_comp_apply]

theorem restrict_congr {a b : ℕ} {h₁ h₂ : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌} (e : h₁ = h₂)
    (σ : S _⦋b⦌) : restrict S h₁ σ = restrict S h₂ σ := by rw [e]

/-- The `i`-th face of an `(n+1)`-simplex of a simplicial set. -/
def face (S : _root_.SSet.{0}) {n : ℕ} (i : Fin (n + 2)) (σ : S _⦋n + 1⦌) : S _⦋n⦌ :=
  restrict S (SimplexCategory.δ i) σ

theorem face_eq_restrict {n : ℕ} (i : Fin (n + 2)) (σ : S _⦋n + 1⦌) :
    face S i σ = restrict S (SimplexCategory.δ i) σ := rfl

/-- The first simplicial identity, in the form of an identity between iterated faces. -/
theorem face_face {n : ℕ} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j)
    (σ : S _⦋n + 2⦌) :
    face S (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt))
        (face S j.succ σ) = face S j (face S i σ) := by
  simp only [face_eq_restrict, restrict_restrict]
  exact restrict_congr (SimplexCategory.δ_comp_δ'' H) σ

/-- A morphism of simplicial sets commutes with restriction. -/
theorem app_restrict {S T : _root_.SSet.{0}} (φ : S ⟶ T) {a b : ℕ}
    (h : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌) (σ : S _⦋b⦌) :
    φ.app _ (restrict S h σ) = restrict T h (φ.app _ σ) := by
  simp only [restrict]
  exact NatTrans.naturality_apply φ h.op σ

/-- A morphism of simplicial sets commutes with the face maps. -/
theorem app_face {S T : _root_.SSet.{0}} (φ : S ⟶ T) {n : ℕ} (i : Fin (n + 2))
    (σ : S _⦋n + 1⦌) : φ.app _ (face S i σ) = face T i (φ.app _ σ) :=
  app_restrict φ _ σ

end SSet

variable (S : SSet.{0}) (R : Type) [CommRing R]

/-- The `R`-module of simplicial `n`-cochains of a simplicial set `S`: functions from the
`n`-simplices of `S` to `R`. -/
def Cochain (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Type := S _⦋n⦌ → R

namespace Cochain

instance (n : ℕ) : AddCommGroup (Cochain S R n) := inferInstanceAs (AddCommGroup (S _⦋n⦌ → R))

instance (n : ℕ) : Module R (Cochain S R n) := inferInstanceAs (Module R (S _⦋n⦌ → R))

variable {S R}

@[ext]
theorem ext {n : ℕ} {f g : Cochain S R n} (h : ∀ σ, f σ = g σ) : f = g := funext h

@[simp]
theorem add_apply {n : ℕ} (f g : Cochain S R n) (σ : S _⦋n⦌) : (f + g) σ = f σ + g σ := rfl

@[simp]
theorem sub_apply {n : ℕ} (f g : Cochain S R n) (σ : S _⦋n⦌) : (f - g) σ = f σ - g σ := rfl

@[simp]
theorem neg_apply {n : ℕ} (f : Cochain S R n) (σ : S _⦋n⦌) : (-f) σ = -f σ := rfl

@[simp]
theorem zero_apply {n : ℕ} (σ : S _⦋n⦌) : (0 : Cochain S R n) σ = 0 := rfl

@[simp]
theorem smul_apply {n : ℕ} (r : R) (f : Cochain S R n) (σ : S _⦋n⦌) : (r • f) σ = r * f σ := rfl

end Cochain

/-- The coboundary operator on simplicial cochains, the alternating sum of the face maps. -/
def coboundary (n : ℕ) : Cochain S R n →ₗ[R] Cochain S R (n + 1) where
  toFun f := fun σ ↦ ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * f (SSet.face S i σ)
  map_add' f g := by
    ext σ
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' r f := by
    ext σ
    simp [Finset.mul_sum, mul_left_comm]

variable {S R}

theorem coboundary_apply {n : ℕ} (f : Cochain S R n) (σ : S _⦋n + 1⦌) :
    coboundary S R n f σ = ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) * f (SSet.face S i σ) := rfl

/-- The coboundary operator squares to zero. -/
theorem coboundary_coboundary {n : ℕ} (f : Cochain S R n) :
    coboundary S R (n + 1) (coboundary S R n f) = 0 := by
  ext σ
  rw [coboundary_apply, Cochain.zero_apply]
  have expand : ∀ j : Fin (n + 3),
      (-1 : R) ^ (j : ℕ) * coboundary S R n f (SSet.face S j σ) =
        ∑ i : Fin (n + 2),
          (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * f (SSet.face S i (SSet.face S j σ)) := by
    intro j
    rw [coboundary_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]; ring
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ expand j, ← Finset.sum_product',
    Finset.univ_product_univ]
  -- Split the index set into the "lower triangle" and its complement.  In a pair `p`, the first
  -- component is the outer index `j` and the second is the inner index `i`.
  set T : Finset (Fin (n + 3) × Fin (n + 2)) := {p | (p.1 : ℕ) ≤ (p.2 : ℕ)} with hT
  rw [← Finset.sum_add_sum_compl T, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun p hp ↦ (p.2.succ, p.1.castLT (lt_of_le_of_lt
    (Finset.mem_filter.mp hp).right p.2.is_lt))) ?_ ?_ ?_ ?_
  · intro p hp
    simp_rw [hT, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hp ⊢
    omega
  · rintro ⟨j, i⟩ hij ⟨j', i'⟩ hij' h
    rw [Prod.mk_inj]
    refine ⟨?_, by simpa using congr_arg Prod.fst h⟩
    simpa using congr_arg Fin.castSucc (congr_arg Prod.snd h)
  · rintro ⟨j', i'⟩ hij'
    simp_rw [hT, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(Fin.castSucc i', j'.pred ?_), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, Nat.not_lt_zero] at hij'
    · simp only [hT, Finset.mem_filter_univ]
      simpa using Nat.le_sub_one_of_lt hij'
    · simp
  · rintro ⟨j, i⟩ hij
    simp only [Fin.val_succ, Fin.val_castLT]
    rw [SSet.face_face (i := j) (j := i)
      (by simpa [hT, Fin.le_def] using (Finset.mem_filter.mp hij).right) σ]
    rw [show (j : ℕ) + ((i : ℕ) + 1) = ((i : ℕ) + (j : ℕ)) + 1 by omega, pow_succ]
    ring

/-- The cochain complex condition, stated as a composition of linear maps. -/
theorem coboundary_comp_coboundary (n : ℕ) :
    (coboundary S R (n + 1)).comp (coboundary S R n) = 0 :=
  LinearMap.ext fun f ↦ coboundary_coboundary f

namespace Cochain

/-- The map on cochains induced (contravariantly) by a morphism of simplicial sets. -/
def pullback {S T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) : Cochain T R n →ₗ[R] Cochain S R n where
  toFun f := fun σ ↦ f (φ.app _ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pullback_apply {S T : SSet.{0}} (φ : S ⟶ T) {n : ℕ} (f : Cochain T R n) (σ : S _⦋n⦌) :
    pullback (R := R) φ n f σ = f (φ.app _ σ) := rfl

@[simp]
theorem pullback_id (S : SSet.{0}) (n : ℕ) :
    pullback (R := R) (𝟙 S) n = LinearMap.id := rfl

theorem pullback_comp {S T U : SSet.{0}} (φ : S ⟶ T) (ψ : T ⟶ U) (n : ℕ) :
    pullback (R := R) (φ ≫ ψ) n = (pullback φ n).comp (pullback ψ n) := rfl

end Cochain

/-- Pullback along a morphism of simplicial sets is a map of cochain complexes. -/
theorem pullback_coboundary {S T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) :
    (Cochain.pullback (R := R) φ (n + 1)).comp (coboundary T R n) =
      (coboundary S R n).comp (Cochain.pullback φ n) := by
  ext f σ
  simp only [LinearMap.coe_comp, Function.comp_apply, Cochain.pullback_apply, coboundary_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [SSet.app_face]

end Submission
