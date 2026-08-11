/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.

The proof of `Submission.FaceHomotopy.toChainHomotopy` below is adapted from
`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy` in
`Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`
(Copyright (c) 2025 Fabian Odermatt, Apache 2.0).
-/
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.Homotopy

/-!
# Chain homotopies from face-only simplicial homotopy data

Mathlib's `CategoryTheory.SimplicialObject.Homotopy` is a homotopy between two *morphisms of
simplicial objects*, and its axioms involve both the faces and the degeneracies.  For the
vanishing theorem of `Submission/Hurewicz/Vanishing.lean` we must work with families of maps
which commute with the faces but *not* with the degeneracies: the compressing homotopies attached
to singular simplices are built by induction on the dimension and there is no reason for them to
be compatible with degenerate simplices.

Inspecting Mathlib's proof of `SimplicialObject.Homotopy.toChainHomotopy` shows that the two
degeneracy axioms are never used, and that the morphisms `f` and `g` enter only through their
components.  This file therefore isolates the face-only data as `Submission.FaceHomotopy` and
reproves the chain homotopy identity for it, following Mathlib's argument verbatim.

## Main definitions

* `Submission.FaceHomotopy F G` — face-only homotopy data between two morphisms of alternating
  face map complexes;
* `Submission.FaceHomotopy.toChainHomotopy` — the induced chain homotopy.
-/

open CategoryTheory CategoryTheory.SimplicialObject
open SimplexCategory Simplicial Opposite AlgebraicTopology CategoryTheory.Preadditive

attribute [local implicit_reducible] AlgebraicTopology.alternatingFaceMapComplex
  AlgebraicTopology.AlternatingFaceMapComplex.obj

noncomputable section

namespace Submission

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {K L : ChainComplex C ℕ}

/-- A presentation of the differential of a chain complex as an alternating sum of "face" maps.
The alternating face map complex of a simplicial object carries the obvious one. -/
structure FaceStructure (K : ChainComplex C ℕ) where
  /-- The face maps. -/
  δ (n : ℕ) (i : Fin (n + 2)) : K.X (n + 1) ⟶ K.X n
  /-- The differential is the alternating sum of the face maps. -/
  d_eq (n : ℕ) : K.d (n + 1) n = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • δ n i

/-- Face-only homotopy data between two maps `F G : K ⟶ L` of chain complexes equipped with face
structures: a family of morphisms `h i : K.X n ⟶ L.X (n + 1)`, `i : Fin (n + 1)`, satisfying the
five identities involving the face maps that appear in the definition of a simplicial homotopy.
Unlike `CategoryTheory.SimplicialObject.Homotopy`, no compatibility with degeneracies is
required — which is essential for the compressions of `Submission/Hurewicz/Vanishing.lean`. -/
structure FaceHomotopy (dK : FaceStructure K) (dL : FaceStructure L) (F G : K ⟶ L) where
  /-- Basic data: `h i : K.X n ⟶ L.X (n + 1)` for `i : Fin (n + 1)`. -/
  h {n : ℕ} (i : Fin (n + 1)) : K.X n ⟶ L.X (n + 1)
  /-- The zeroth operator followed by the zeroth face recovers `G`. -/
  h_zero_comp_δ_zero (n : ℕ) : h 0 ≫ dL.δ n 0 = G.f n
  /-- The last operator followed by the last face recovers `F`. -/
  h_last_comp_δ_last (n : ℕ) : h (Fin.last n) ≫ dL.δ n (Fin.last (n + 1)) = F.f n
  /-- Compatibility with the faces, first case. -/
  h_succ_comp_δ_castSucc_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    h j.succ ≫ dL.δ (n + 1) i.castSucc = dK.δ n i ≫ h j
  /-- Compatibility with the faces, second case. -/
  h_succ_comp_δ_castSucc_succ {n : ℕ} (j : Fin (n + 1)) :
    h j.succ ≫ dL.δ (n + 1) j.castSucc.succ = h j.castSucc ≫ dL.δ (n + 1) j.castSucc.succ
  /-- Compatibility with the faces, third case. -/
  h_castSucc_comp_δ_succ_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    h j.castSucc ≫ dL.δ (n + 1) i.succ = dK.δ n i ≫ h j

namespace FaceHomotopy

attribute [reassoc (attr := simp)]
  h_zero_comp_δ_zero h_last_comp_δ_last h_succ_comp_δ_castSucc_of_lt
  h_castSucc_comp_δ_succ_of_lt

attribute [reassoc] h_succ_comp_δ_castSucc_succ

variable {dK : FaceStructure K} {dL : FaceStructure L} {F G : K ⟶ L}
variable (H : FaceHomotopy dK dL F G)

/-- The family of components of the induced chain homotopy. -/
def hom (p q : ℕ) : K.X p ⟶ L.X q :=
  if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k ≫ eqToHom (by simp [h])
  else 0

@[simp]
theorem hom_eq (p : ℕ) : hom H p (p + 1) = -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k := by
  simp [hom]

@[simp]
theorem hom_eq_zero (p q : ℕ) (hpq : p + 1 ≠ q) : hom H p q = 0 := dif_neg hpq

private theorem comm_zero : F.f 0 = hom H 0 1 ≫ L.d 1 0 + G.f 0 := by
  rw [dL.d_eq 0]
  simp [← H.h_last_comp_δ_last 0, Fin.sum_univ_two]

private theorem comm_succ (n : ℕ) :
    letI a : K.X (n + 1) ⟶ L.X (n + 1) := K.d (n + 1) n ≫ hom H n (n + 1)
    letI b : K.X (n + 1) ⟶ L.X (n + 1) := hom H (n + 1) (n + 2) ≫ L.d (n + 2) (n + 1)
    F.f (n + 1) = a + b + G.f (n + 1) := by
  rw [← H.h_zero_comp_δ_zero, ← H.h_last_comp_δ_last, dK.d_eq n, dL.d_eq (n + 1)]
  simp only [hom_eq,
    Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    smul_neg, Finset.sum_neg_distrib, ← Finset.sum_zsmul, smul_smul, ← pow_add]
  let α (x : Fin (n + 1) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • dK.δ n x.2 ≫ H.h x.1
  let β (x : Fin (n + 3) × Fin (n + 2)) := (-1) ^ ((x.1 + x.2 : ℕ)) • H.h x.2 ≫ dL.δ (n + 1) x.1
  have h₂ (x : Fin (n + 1) × Fin (n + 2)) (hx : x.1.castSucc < x.2) :
      α x = -β ⟨x.2.succ, x.1.castSucc⟩ := by
    dsimp [α, β]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 hx,
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  rw [← Finset.sum_product .univ .univ α, ← Finset.sum_product .univ .univ β,
    Finset.univ_product_univ, Finset.univ_product_univ]
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := { x | x.1.castSucc < x.2 }
  let γ₁ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.castSucc, x.1.succ)
  let γ₂ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.succ, x.1.castSucc)
  let γ₃ (i : Fin (n + 1)) := (i.castSucc.succ, i.succ)
  let γ₄ (i : Fin (n + 1)) := (i.castSucc.succ, i.castSucc)
  have hγ₁ : Function.Injective γ₁ := fun _ _ ↦ by aesop
  have hγ₂ : Function.Injective γ₂ := fun _ _ ↦ by aesop
  have hγ₃ : Function.Injective γ₃ := fun _ _ ↦ by aesop
  have hγ₄ : Function.Injective γ₄ := fun _ _ ↦ by aesop
  have eq₁ : H.h 0 ≫ dL.δ (n + 1) 0 = β ⟨0, 0⟩ := by simp [β]
  have eq₂ : H.h (Fin.last _) ≫ dL.δ (n + 1) (Fin.last _) =
      - β ⟨Fin.last _, Fin.last _⟩ := by
    dsimp [β]
    simp only [pow_add, even_two, Even.neg_pow, one_pow, mul_one,
      pow_one, mul_neg, neg_smul, neg_neg]
    rw [← pow_add, (Even.add_self n).neg_one_pow, one_smul]
  have eq₃ : ∑ x ∈ Sᶜ, α x = - ∑ y ∈ Finset.image γ₁ Sᶜ, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₁.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₁]
    simp only [← H.h_succ_comp_δ_castSucc_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₄ : ∑ x ∈ S, α x = - ∑ y ∈ Finset.image γ₂ S, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₂.injOn]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    dsimp [α, β, γ₂]
    simp only [← H.h_castSucc_comp_δ_succ_of_lt x.2 x.1 (by simpa [S] using hx),
      pow_add, pow_one, mul_neg, mul_one, neg_mul, neg_smul, neg_neg]
    rw [mul_comm]
  have eq₅ : ∑ x, β (γ₄ x) = - ∑ x, β (γ₃ x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ by simp [h_succ_comp_δ_castSucc_succ, β, γ₃, γ₄])
  have h₁ : Disjoint (Finset.image γ₁ Sᶜ) (Finset.image γ₂ S) := by
    rw [Finset.disjoint_iff_ne]
    grind [Finset.mem_compl]
  have h₂ : Disjoint (Finset.image γ₃ .univ) (Finset.image γ₄ .univ) := by
    rw [Finset.disjoint_iff_ne]
    grind
  have h₃ : Disjoint (Finset.disjUnion _ _ h₂) {(0, 0), (Fin.last _, Fin.last _)} := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_insert, forall_eq_or_imp, Prod.forall]
    rintro ⟨a, _⟩ ⟨b, _⟩
    simp
    grind
  have h₄ : Disjoint (Finset.disjUnion _ _ h₁) (Finset.disjUnion _ _ h₃) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.disjUnion_eq_union, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, ne_eq,
      Finset.mem_insert, Finset.mem_singleton, Prod.forall, Prod.mk.injEq, not_and,
      S, γ₁, γ₂, γ₃, γ₄]
    rintro ⟨a, _⟩ ⟨b, _⟩ (⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩ | ⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩) _ _
      ((⟨⟨i, _⟩, h₄, h₅⟩ | ⟨⟨i, _⟩, h₄, h₅⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
        simp [Fin.ext_iff] at h₁ h₂ h₃ ⊢ <;> grind
  have Hc : (Finset.disjUnion _ _ h₁)ᶜ = Finset.disjUnion _ _ h₃ :=
    Finset.compl_eq_of_disjoint_of_card_add_eq h₄ (by
      rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion,
        Finset.card_image_of_injective _ hγ₁, Finset.card_image_of_injective _ hγ₂,
        Finset.card_image_of_injective _ hγ₃, Finset.card_image_of_injective _ hγ₄]
      simp
      lia)
  rw [eq₁, eq₂, ← S.sum_add_sum_compl, eq₃, eq₄,
    neg_add_rev, neg_neg, neg_neg, ← Finset.sum_disjUnion h₁,
    ← (Finset.disjUnion _ _ h₁).sum_add_sum_compl, neg_add,
    ← add_assoc, add_neg_cancel, zero_add, Hc,
    Finset.sum_disjUnion, Finset.sum_disjUnion,
    Finset.sum_image hγ₃.injOn, Finset.sum_image hγ₄.injOn,
    Finset.sum_insert (by simp), Finset.sum_singleton,
    neg_add_rev, neg_add_rev, neg_add_rev, eq₅]
  simp

/-- Face-only homotopy data induces a chain homotopy. -/
def toChainHomotopy : _root_.Homotopy F G where
  hom := hom H
  zero i j hij := hom_eq_zero _ _ _ hij
  comm n := by
    cases n with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add]
      simp [comm_zero H]
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)]
      simp [comm_succ H]

end FaceHomotopy

end Submission
