/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Cochain

/-!
# Front and back faces of a simplex

The Alexander–Whitney cup product is built from the two "half" faces of a simplex: the *front*
face spanned by the first `a + 1` vertices and the *back* face spanned by the last `b + 1`
vertices.

This file defines the corresponding morphisms `frontHom` and `backHom` of `SimplexCategory` and
establishes all the identities relating them to each other and to the coface maps
`SimplexCategory.δ` that are needed for the Leibniz rule and for associativity of the cup product.

## Main definitions

* `Submission.frontHom a N h : ⦋a⦌ ⟶ ⦋N⦌` — `i ↦ i`.
* `Submission.backHom b N h : ⦋b⦌ ⟶ ⦋N⦌` — `i ↦ N - b + i`.
* `Submission.SSet.front S h σ`, `Submission.SSet.back S h σ` — the induced operations on
  simplices of a simplicial set.

## Main results

* `Submission.SSet.front_face_of_le`, `Submission.SSet.front_face_of_lt`,
  `Submission.SSet.back_face_of_le`, `Submission.SSet.back_face_of_lt` — how a front (resp. back)
  face interacts with a coface map.  These are the combinatorial heart of the Leibniz rule.
* `Submission.SSet.front_front`, `Submission.SSet.back_back`, `Submission.SSet.back_front` — the
  identities behind associativity.
-/

namespace Submission

open CategoryTheory Simplicial

/-- The underlying natural number of `Fin.succAbove`. -/
theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    ((p.succAbove k : Fin (n + 1)) : ℕ) = if (k : ℕ) < (p : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  split_ifs with hk
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hk), Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using Nat.not_lt.mp hk),
      Fin.val_succ]

/-- The underlying natural number of a coface map of `SimplexCategory`. -/
theorem val_δ_toOrderHom {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    (((SimplexCategory.δ i).toOrderHom k : Fin (n + 2)) : ℕ)
      = if (k : ℕ) < (i : ℕ) then (k : ℕ) else (k : ℕ) + 1 :=
  val_succAbove i k

/-- Two morphisms `⦋a⦌ ⟶ ⦋N⦌` agree as soon as they agree on underlying natural numbers. -/
theorem hom_ext_val {a N : ℕ} {f g : (⦋a⦌ : SimplexCategory) ⟶ ⦋N⦌}
    (H : ∀ k : Fin (a + 1),
      ((f.toOrderHom k : Fin (N + 1)) : ℕ) = ((g.toOrderHom k : Fin (N + 1)) : ℕ)) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k ↦ Fin.ext (H k)))

/-- The inclusion `⦋a⦌ ⟶ ⦋N⦌` of the first `a + 1` vertices. -/
def frontHom (a N : ℕ) (h : a ≤ N) : (⦋a⦌ : SimplexCategory) ⟶ ⦋N⦌ :=
  SimplexCategory.mkHom ⟨fun i ↦ i.castLE (by omega), fun _ _ hij ↦ hij⟩

/-- The inclusion `⦋b⦌ ⟶ ⦋N⦌` of the last `b + 1` vertices. -/
def backHom (b N : ℕ) (h : b ≤ N) : (⦋b⦌ : SimplexCategory) ⟶ ⦋N⦌ :=
  SimplexCategory.mkHom ⟨fun i ↦ ⟨N - b + (i : ℕ), by have := i.isLt; omega⟩,
    fun _ _ hij ↦ by simpa using hij⟩

@[simp]
theorem val_frontHom {a N : ℕ} (h : a ≤ N) (k : Fin (a + 1)) :
    (((frontHom a N h).toOrderHom k : Fin (N + 1)) : ℕ) = (k : ℕ) := rfl

@[simp]
theorem val_backHom {b N : ℕ} (h : b ≤ N) (k : Fin (b + 1)) :
    (((backHom b N h).toOrderHom k : Fin (N + 1)) : ℕ) = N - b + (k : ℕ) := rfl

theorem frontHom_self (a : ℕ) : frontHom a a le_rfl = 𝟙 _ :=
  hom_ext_val fun k ↦ by simp

theorem backHom_self (b : ℕ) : backHom b b le_rfl = 𝟙 _ :=
  hom_ext_val fun k ↦ by simp

theorem frontHom_comp_frontHom {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    frontHom a b h₁ ≫ frontHom b c h₂ = frontHom a c (h₁.trans h₂) :=
  hom_ext_val fun k ↦ by simp

theorem backHom_comp_backHom {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    backHom a b h₁ ≫ backHom b c h₂ = backHom a c (h₁.trans h₂) :=
  hom_ext_val fun k ↦ by simp; omega

/-- The "middle face" identity: the back face of a front face is the front face of a back face. -/
theorem backHom_comp_frontHom {p q r : ℕ} :
    backHom q (p + q) (by omega) ≫ frontHom (p + q) (p + q + r) (by omega) =
      frontHom q (q + r) (by omega) ≫ backHom (q + r) (p + q + r) (by omega) :=
  hom_ext_val fun k ↦ by simp; omega

theorem frontHom_comp_δ_of_lt {a N : ℕ} (h : a ≤ N) (i : Fin (N + 2)) (hi : a < (i : ℕ)) :
    frontHom a N h ≫ SimplexCategory.δ i = frontHom a (N + 1) (by omega) :=
  hom_ext_val fun k ↦ by
    have hk : (k : ℕ) ≤ a := by have := k.isLt; omega
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_δ_toOrderHom, val_frontHom, if_pos (by omega : (k : ℕ) < (i : ℕ))]

theorem frontHom_comp_δ_of_le {a N : ℕ} (h : a ≤ N) (i : Fin (N + 2)) (i' : Fin (a + 2))
    (hi' : (i' : ℕ) = (i : ℕ)) :
    frontHom a N h ≫ SimplexCategory.δ i =
      SimplexCategory.δ i' ≫ frontHom (a + 1) (N + 1) (by omega) :=
  hom_ext_val fun k ↦ by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_δ_toOrderHom, val_frontHom, hi']

theorem backHom_comp_δ_of_le {b N : ℕ} (h : b ≤ N) (i : Fin (N + 2)) (hi : (i : ℕ) ≤ N - b) :
    backHom b N h ≫ SimplexCategory.δ i = backHom b (N + 1) (by omega) :=
  hom_ext_val fun k ↦ by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_δ_toOrderHom, val_backHom, if_neg (by omega : ¬ N - b + (k : ℕ) < (i : ℕ))]
    omega

theorem backHom_comp_δ_of_lt {b N : ℕ} (h : b ≤ N) (i : Fin (N + 2)) (i' : Fin (b + 2))
    (hi : N - b < (i : ℕ)) (hi' : (i' : ℕ) = (i : ℕ) - (N - b)) :
    backHom b N h ≫ SimplexCategory.δ i =
      SimplexCategory.δ i' ≫ backHom (b + 1) (N + 1) (by omega) :=
  hom_ext_val fun k ↦ by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_δ_toOrderHom, val_backHom, hi']
    split_ifs <;> omega

theorem δ_last_comp_frontHom {a N : ℕ} (h : a + 1 ≤ N) :
    SimplexCategory.δ (Fin.last (a + 1)) ≫ frontHom (a + 1) N h = frontHom a N (by omega) :=
  hom_ext_val fun k ↦ by
    have hk : (k : ℕ) ≤ a := by have := k.isLt; omega
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_frontHom, val_δ_toOrderHom, Fin.val_last, if_pos (by omega : (k : ℕ) < a + 1)]

theorem δ_zero_comp_backHom {b N : ℕ} (h : b + 1 ≤ N) :
    SimplexCategory.δ (0 : Fin (b + 2)) ≫ backHom (b + 1) N h = backHom b N (by omega) :=
  hom_ext_val fun k ↦ by
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      val_backHom, val_δ_toOrderHom, Fin.val_zero, if_neg (Nat.not_lt_zero _)]
    omega

namespace SSet

variable {S : _root_.SSet.{0}}

/-- The front face of a simplex: the face spanned by its first `a + 1` vertices. -/
def front (S : _root_.SSet.{0}) {a N : ℕ} (h : a ≤ N) (σ : S _⦋N⦌) : S _⦋a⦌ :=
  restrict S (frontHom a N h) σ

/-- The back face of a simplex: the face spanned by its last `b + 1` vertices. -/
def back (S : _root_.SSet.{0}) {b N : ℕ} (h : b ≤ N) (σ : S _⦋N⦌) : S _⦋b⦌ :=
  restrict S (backHom b N h) σ

@[simp]
theorem front_self {a : ℕ} (σ : S _⦋a⦌) : front S le_rfl σ = σ := by
  rw [front, restrict_congr (frontHom_self a), restrict_id]

@[simp]
theorem back_self {b : ℕ} (σ : S _⦋b⦌) : back S le_rfl σ = σ := by
  rw [back, restrict_congr (backHom_self b), restrict_id]

theorem front_front {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (σ : S _⦋c⦌) :
    front S h₁ (front S h₂ σ) = front S (h₁.trans h₂) σ := by
  rw [front, front, front, restrict_restrict, frontHom_comp_frontHom]

theorem back_back {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (σ : S _⦋c⦌) :
    back S h₁ (back S h₂ σ) = back S (h₁.trans h₂) σ := by
  rw [back, back, back, restrict_restrict, backHom_comp_backHom]

/-- The "middle face" of a simplex can be computed in two ways. -/
theorem back_front {p q r : ℕ} (σ : S _⦋p + q + r⦌) :
    back S (by omega : q ≤ p + q) (front S (by omega : p + q ≤ p + q + r) σ) =
      front S (by omega : q ≤ q + r) (back S (by omega : q + r ≤ p + q + r) σ) := by
  rw [back, front, front, back, restrict_restrict, restrict_restrict,
    restrict_congr (backHom_comp_frontHom (p := p) (q := q) (r := r))]

theorem front_face_of_lt {a N : ℕ} (h : a ≤ N) (i : Fin (N + 2)) (hi : a < (i : ℕ))
    (σ : S _⦋N + 1⦌) : front S h (face S i σ) = front S (by omega : a ≤ N + 1) σ := by
  rw [front, face_eq_restrict, restrict_restrict, restrict_congr (frontHom_comp_δ_of_lt h i hi),
    front]

theorem front_face_of_le {a N : ℕ} (h : a ≤ N) (i : Fin (N + 2)) (i' : Fin (a + 2))
    (hi' : (i' : ℕ) = (i : ℕ)) (σ : S _⦋N + 1⦌) :
    front S h (face S i σ) = face S i' (front S (by omega : a + 1 ≤ N + 1) σ) := by
  rw [front, face_eq_restrict, restrict_restrict,
    restrict_congr (frontHom_comp_δ_of_le h i i' hi'), ← restrict_restrict, ← front,
    ← face_eq_restrict]

theorem back_face_of_le {b N : ℕ} (h : b ≤ N) (i : Fin (N + 2)) (hi : (i : ℕ) ≤ N - b)
    (σ : S _⦋N + 1⦌) : back S h (face S i σ) = back S (by omega : b ≤ N + 1) σ := by
  rw [back, face_eq_restrict, restrict_restrict, restrict_congr (backHom_comp_δ_of_le h i hi), back]

theorem back_face_of_lt {b N : ℕ} (h : b ≤ N) (i : Fin (N + 2)) (i' : Fin (b + 2))
    (hi : N - b < (i : ℕ)) (hi' : (i' : ℕ) = (i : ℕ) - (N - b)) (σ : S _⦋N + 1⦌) :
    back S h (face S i σ) = face S i' (back S (by omega : b + 1 ≤ N + 1) σ) := by
  rw [back, face_eq_restrict, restrict_restrict,
    restrict_congr (backHom_comp_δ_of_lt h i i' hi hi'), ← restrict_restrict, ← back,
    ← face_eq_restrict]

/-- Dropping the last vertex of a front face gives a smaller front face. -/
theorem face_last_front {a N : ℕ} (h : a + 1 ≤ N) (σ : S _⦋N⦌) :
    face S (Fin.last (a + 1)) (front S h σ) = front S (by omega : a ≤ N) σ := by
  rw [face_eq_restrict, front, restrict_restrict, restrict_congr (δ_last_comp_frontHom h), front]

/-- Dropping the first vertex of a back face gives a smaller back face. -/
theorem face_zero_back {b N : ℕ} (h : b + 1 ≤ N) (σ : S _⦋N⦌) :
    face S (0 : Fin (b + 2)) (back S h σ) = back S (by omega : b ≤ N) σ := by
  rw [face_eq_restrict, back, restrict_restrict, restrict_congr (δ_zero_comp_backHom h), back]

theorem app_front {S T : _root_.SSet.{0}} (φ : S ⟶ T) {a N : ℕ} (h : a ≤ N) (σ : S _⦋N⦌) :
    φ.app _ (front S h σ) = front T h (φ.app _ σ) :=
  app_restrict φ _ σ

theorem app_back {S T : _root_.SSet.{0}} (φ : S ⟶ T) {b N : ℕ} (h : b ≤ N) (σ : S _⦋N⦌) :
    φ.app _ (back S h σ) = back T h (φ.app _ σ) :=
  app_restrict φ _ σ

end SSet

end Submission
