/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.FrontBack
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Alexander–Whitney cup product on simplicial cochains

For cochains `f` of degree `p` and `g` of degree `q` on a simplicial set `S`, the
Alexander–Whitney cup product is

`(f ⌣ g) σ = f (front face of σ) * g (back face of σ)`.

Because `p + 1 + q` and `p + q + 1` are not definitionally equal in Lean, the total degree of the
product is carried as an explicit parameter: `cupOfEq (h : p + q = n) f g : Cochain S R n`.  The
notation `f ⌣ g` is `cupOfEq rfl f g`, of degree `p + q`.

## Main definitions

* `Submission.cupOfEq h f g` and `Submission.cup f g` (notation `f ⌣ g`).
* `Submission.cupₗ h : Cochain S R p →ₗ[R] Cochain S R q →ₗ[R] Cochain S R n`, the bilinear
  version.
* `Submission.Cochain.one : Cochain S R 0`, the unit.

## Main results

* `Submission.coboundary_cupOfEq` — the Leibniz rule
  `δ (f ⌣ g) = δ f ⌣ g + (-1) ^ p • (f ⌣ δ g)`.
* `Submission.cupOfEq_assoc` — associativity.
* `Submission.one_cup`, `Submission.cup_one` — unitality.
* `Submission.pullback_cupOfEq` — naturality.
-/

namespace Submission

open CategoryTheory Simplicial

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- The Alexander–Whitney cup product of a `p`-cochain and a `q`-cochain, landing in degree `n`
for any `n` with `p + q = n`. -/
def cupOfEq {p q n : ℕ} (h : p + q = n) (f : Cochain S R p) (g : Cochain S R q) :
    Cochain S R n :=
  fun σ ↦ f (SSet.front S (by omega) σ) * g (SSet.back S (by omega) σ)

theorem cupOfEq_apply {p q n : ℕ} (h : p + q = n) (f : Cochain S R p) (g : Cochain S R q)
    (σ : S _⦋n⦌) :
    cupOfEq h f g σ =
      f (SSet.front S (by omega) σ) * g (SSet.back S (by omega) σ) := rfl

/-- The Alexander–Whitney cup product, in the degree `p + q`. -/
def cup {p q : ℕ} (f : Cochain S R p) (g : Cochain S R q) : Cochain S R (p + q) :=
  cupOfEq rfl f g

@[inherit_doc] scoped infixl:70 " ⌣ " => Submission.cup

theorem cup_def {p q : ℕ} (f : Cochain S R p) (g : Cochain S R q) : f ⌣ g = cupOfEq rfl f g := rfl

/-- The cup product is `R`-bilinear. -/
def cupₗ {p q n : ℕ} (h : p + q = n) :
    Cochain S R p →ₗ[R] Cochain S R q →ₗ[R] Cochain S R n :=
  LinearMap.mk₂ R (cupOfEq h)
    (fun f₁ f₂ g ↦ by ext σ; simp only [cupOfEq_apply, Cochain.add_apply]; ring)
    (fun r f g ↦ by ext σ; simp only [cupOfEq_apply, Cochain.smul_apply]; ring)
    (fun f g₁ g₂ ↦ by ext σ; simp only [cupOfEq_apply, Cochain.add_apply]; ring)
    (fun r f g ↦ by ext σ; simp only [cupOfEq_apply, Cochain.smul_apply]; ring)

@[simp]
theorem cupₗ_apply {p q n : ℕ} (h : p + q = n) (f : Cochain S R p) (g : Cochain S R q) :
    cupₗ h f g = cupOfEq h f g :=
  LinearMap.mk₂_apply _ _ _ _

@[simp]
theorem zero_cupOfEq {p q n : ℕ} (h : p + q = n) (g : Cochain S R q) :
    cupOfEq h (0 : Cochain S R p) g = 0 := by
  ext σ
  rw [cupOfEq_apply, Cochain.zero_apply, Cochain.zero_apply, zero_mul]

@[simp]
theorem cupOfEq_zero {p q n : ℕ} (h : p + q = n) (f : Cochain S R p) :
    cupOfEq h f (0 : Cochain S R q) = 0 := by
  ext σ
  rw [cupOfEq_apply, Cochain.zero_apply, Cochain.zero_apply, mul_zero]

/-! ### The Leibniz rule -/

/-- **Leibniz rule** for the Alexander–Whitney cup product:
`δ (f ⌣ g) = (δ f) ⌣ g + (-1) ^ p • (f ⌣ δ g)`. -/
theorem coboundary_cupOfEq {p q n : ℕ} (h : p + q = n) (f : Cochain S R p)
    (g : Cochain S R q) :
    coboundary S R n (cupOfEq h f g) =
      cupOfEq (by omega : p + 1 + q = n + 1) (coboundary S R p f) g +
        (-1 : R) ^ p • cupOfEq (by omega : p + (q + 1) = n + 1) f (coboundary S R q g) := by
  subst h
  ext σ
  have hsplit : p + 1 + (q + 1) = p + q + 2 := by omega
  have hcastAdd : ∀ k : Fin (p + 1),
      ((Fin.cast hsplit (Fin.castAdd (q + 1) k) : Fin (p + q + 2)) : ℕ) = (k : ℕ) := fun _ ↦ rfl
  have hnatAdd : ∀ l : Fin (q + 1),
      ((Fin.cast hsplit (Fin.natAdd (p + 1) l) : Fin (p + q + 2)) : ℕ) = p + 1 + (l : ℕ) :=
    fun _ ↦ rfl
  -- Faces with a small index only affect the front face of `σ`.
  have hA : ∀ (i : Fin (p + q + 2)) (i' : Fin (p + 2)), (i : ℕ) ≤ p → (i' : ℕ) = (i : ℕ) →
      f (SSet.front S (show p ≤ p + q by omega) (SSet.face S i σ)) *
          g (SSet.back S (show q ≤ p + q by omega) (SSet.face S i σ)) =
        f (SSet.face S i' (SSet.front S (show p + 1 ≤ p + q + 1 by omega) σ)) *
          g (SSet.back S (show q ≤ p + q + 1 by omega) σ) := by
    intro i i' hi hi'
    rw [SSet.front_face_of_le (by omega) i i' hi', SSet.back_face_of_le (by omega) i (by omega)]
  -- Faces with a large index only affect the back face of `σ`.
  have hB : ∀ (i : Fin (p + q + 2)) (i'' : Fin (q + 2)), p < (i : ℕ) → (i'' : ℕ) = (i : ℕ) - p →
      f (SSet.front S (show p ≤ p + q by omega) (SSet.face S i σ)) *
          g (SSet.back S (show q ≤ p + q by omega) (SSet.face S i σ)) =
        f (SSet.front S (show p ≤ p + q + 1 by omega) σ) *
          g (SSet.face S i'' (SSet.back S (show q + 1 ≤ p + q + 1 by omega) σ)) := by
    intro i i'' hi hi''
    rw [SSet.front_face_of_lt (by omega) i (by omega),
      SSet.back_face_of_lt (by omega) i i'' (by omega) (by omega)]
  -- The two extra terms on the right-hand side cancel each other.
  have hlast : SSet.face S (Fin.last (p + 1))
      (SSet.front S (show p + 1 ≤ p + q + 1 by omega) σ) =
        SSet.front S (show p ≤ p + q + 1 by omega) σ := SSet.face_last_front _ σ
  have hzero : SSet.face S (0 : Fin (q + 2))
      (SSet.back S (show q + 1 ≤ p + q + 1 by omega) σ) =
        SSet.back S (show q ≤ p + q + 1 by omega) σ := SSet.face_zero_back _ σ
  have E1 : ∀ k : Fin (p + 1),
      (-1 : R) ^ ((Fin.cast hsplit (Fin.castAdd (q + 1) k) : Fin (p + q + 2)) : ℕ) *
          (f (SSet.front S (show p ≤ p + q by omega)
              (SSet.face S (Fin.cast hsplit (Fin.castAdd (q + 1) k)) σ)) *
            g (SSet.back S (show q ≤ p + q by omega)
              (SSet.face S (Fin.cast hsplit (Fin.castAdd (q + 1) k)) σ))) =
        ((-1 : R) ^ (k : ℕ) *
            f (SSet.face S k.castSucc (SSet.front S (show p + 1 ≤ p + q + 1 by omega) σ))) *
          g (SSet.back S (show q ≤ p + q + 1 by omega) σ) := by
    intro k
    rw [hA _ k.castSucc (by rw [hcastAdd]; have := k.isLt; omega) (by rw [hcastAdd]; rfl),
      hcastAdd, mul_assoc]
  have E2 : ∀ l : Fin (q + 1),
      (-1 : R) ^ ((Fin.cast hsplit (Fin.natAdd (p + 1) l) : Fin (p + q + 2)) : ℕ) *
          (f (SSet.front S (show p ≤ p + q by omega)
              (SSet.face S (Fin.cast hsplit (Fin.natAdd (p + 1) l)) σ)) *
            g (SSet.back S (show q ≤ p + q by omega)
              (SSet.face S (Fin.cast hsplit (Fin.natAdd (p + 1) l)) σ))) =
        (-1 : R) ^ p * (f (SSet.front S (show p ≤ p + q + 1 by omega) σ) *
          ((-1 : R) ^ ((l : ℕ) + 1) *
            g (SSet.face S l.succ (SSet.back S (show q + 1 ≤ p + q + 1 by omega) σ)))) := by
    intro l
    rw [hB _ l.succ (by rw [hnatAdd]; omega) (by rw [hnatAdd, Fin.val_succ]; omega), hnatAdd,
      show p + 1 + (l : ℕ) = p + ((l : ℕ) + 1) by omega, pow_add]
    ring
  simp only [Cochain.add_apply, Cochain.smul_apply, cupOfEq_apply, coboundary_apply]
  conv_rhs => lhs; lhs; rw [Fin.sum_univ_castSucc]
  conv_rhs => rhs; rhs; rhs; rw [Fin.sum_univ_succ]
  rw [hlast, hzero, ← Fin.sum_congr' _ hsplit, Fin.sum_univ_add,
    Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) ↦ E1 k),
    Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) ↦ E2 l),
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, pow_zero]
  ring

/-! ### Associativity -/

/-- **Associativity** of the Alexander–Whitney cup product, on the level of cochains. -/
theorem cupOfEq_assoc {p q r m n k : ℕ} (hm : p + q = m) (hn : q + r = n) (hk : p + q + r = k)
    (f : Cochain S R p) (g : Cochain S R q) (h : Cochain S R r) :
    cupOfEq (by omega : m + r = k) (cupOfEq hm f g) h =
      cupOfEq (by omega : p + n = k) f (cupOfEq hn g h) := by
  subst hm; subst hn; subst hk
  ext σ
  simp only [cupOfEq_apply]
  rw [SSet.front_front (by omega) (by omega), SSet.back_back (by omega) (by omega),
    SSet.back_front (p := p) (q := q) (r := r) σ, mul_assoc]

/-! ### The unit -/

namespace Cochain

/-- The unit cochain: the `0`-cochain with constant value `1`. -/
def one (S : SSet.{0}) (R : Type) [CommRing R] : Cochain S R 0 := fun _ ↦ (1 : R)

@[simp]
theorem one_apply (σ : S _⦋0⦌) : one S R σ = 1 := rfl

end Cochain

/-- The unit cochain is a cocycle. -/
theorem coboundary_one : coboundary S R 0 (Cochain.one S R) = 0 := by
  ext σ
  rw [coboundary_apply]
  simp [Fin.sum_univ_two]

/-- The unit cochain is a left unit for the cup product. -/
theorem one_cup {q : ℕ} (g : Cochain S R q) :
    cupOfEq (Nat.zero_add q) (Cochain.one S R) g = g := by
  ext σ
  rw [cupOfEq_apply, Cochain.one_apply, one_mul, SSet.back_self]

/-- The unit cochain is a right unit for the cup product. -/
theorem cup_one {p : ℕ} (f : Cochain S R p) :
    cupOfEq (Nat.add_zero p) f (Cochain.one S R) = f := by
  ext σ
  rw [cupOfEq_apply, Cochain.one_apply, mul_one, SSet.front_self]

/-! ### Naturality -/

/-- **Naturality**: pullback along a morphism of simplicial sets is multiplicative for the cup
product. -/
theorem pullback_cupOfEq {S T : SSet.{0}} (φ : S ⟶ T) {p q n : ℕ} (h : p + q = n)
    (f : Cochain T R p) (g : Cochain T R q) :
    Cochain.pullback φ n (cupOfEq h f g) =
      cupOfEq h (Cochain.pullback φ p f) (Cochain.pullback φ q g) := by
  ext σ
  rw [Cochain.pullback_apply, cupOfEq_apply, cupOfEq_apply, Cochain.pullback_apply,
    Cochain.pullback_apply, SSet.app_front, SSet.app_back]

/-- Pullback preserves the unit cochain. -/
@[simp]
theorem pullback_one {S T : SSet.{0}} (φ : S ⟶ T) :
    Cochain.pullback φ 0 (Cochain.one T R) = Cochain.one S R := rfl

end Submission
