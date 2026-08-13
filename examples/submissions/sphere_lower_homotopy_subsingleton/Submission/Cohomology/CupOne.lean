/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# The first higher cup product over `ZMod 2`

This file defines the simplicial cup-one product on cochains with coefficients in `ZMod 2`.
For cochains of positive degrees `p` and `q`, its value on a `(p + q - 1)`-simplex is

`sum_j f([0, ..., j, j + q, ..., p + q - 1]) * g([j, ..., j + q])`,

where `j` ranges from `0` to `p - 1`.  The two faces in each summand are encoded by morphisms of
the simplex category, so naturality is immediate from functoriality of restriction.

The degree-three self-product is the cochain representative used to define `Sq^2` on a
degree-three mod-two cohomology class.  Its boundary formula is developed below in the concrete
degrees needed for the first stable stem.
-/

namespace Submission

open CategoryTheory Simplicial

/-- The left face in the `j`-th summand of the cup-one product.  It retains the first `j + 1`
vertices and the final `p - j` vertices. -/
def cupOneLeftHom (p q : ℕ) (hq : 1 ≤ q) (j : Fin p) :
    (⦋p⦌ : SimplexCategory) ⟶ ⦋p + q - 1⦌ :=
  SimplexCategory.mkHom
    ⟨fun k ↦
        ⟨if (k : ℕ) ≤ (j : ℕ) then (k : ℕ) else (k : ℕ) + q - 1, by
          have hk := k.isLt
          have hj := j.isLt
          split_ifs <;> omega⟩,
      fun a b hab ↦ by
        apply Fin.mk_le_mk.mpr
        split_ifs <;> omega⟩

/-- The right face in the `j`-th summand of the cup-one product: the consecutive vertices from
`j` through `j + q`. -/
def cupOneRightHom (p q : ℕ) (j : Fin p) :
    (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q - 1⦌ :=
  SimplexCategory.mkHom
    ⟨fun k ↦ ⟨(j : ℕ) + (k : ℕ), by
        have hj := j.isLt
        have hk := k.isLt
        omega⟩,
      fun _ _ hab ↦ by simpa using Nat.add_le_add_left hab (j : ℕ)⟩

@[simp]
theorem val_cupOneLeftHom {p q : ℕ} (hq : 1 ≤ q) (j : Fin p) (k : Fin (p + 1)) :
    (((cupOneLeftHom p q hq j).toOrderHom k : Fin (p + q - 1 + 1)) : ℕ) =
      if (k : ℕ) ≤ (j : ℕ) then (k : ℕ) else (k : ℕ) + q - 1 :=
  rfl

@[simp]
theorem val_cupOneRightHom {p q : ℕ} (j : Fin p) (k : Fin (q + 1)) :
    (((cupOneRightHom p q j).toOrderHom k : Fin (p + q - 1 + 1)) : ℕ) =
      (j : ℕ) + (k : ℕ) :=
  rfl

namespace SSet

variable {S : _root_.SSet.{0}}

/-- The left face of a simplex occurring in a cup-one summand. -/
def cupOneLeft (S : _root_.SSet.{0}) (p q : ℕ) (hq : 1 ≤ q) (j : Fin p)
    (σ : S _⦋p + q - 1⦌) : S _⦋p⦌ :=
  restrict S (cupOneLeftHom p q hq j) σ

/-- The right face of a simplex occurring in a cup-one summand. -/
def cupOneRight (S : _root_.SSet.{0}) (p q : ℕ) (j : Fin p)
    (σ : S _⦋p + q - 1⦌) : S _⦋q⦌ :=
  restrict S (cupOneRightHom p q j) σ

theorem app_cupOneLeft {S T : _root_.SSet.{0}} (φ : S ⟶ T) (p q : ℕ) (hq : 1 ≤ q)
    (j : Fin p) (σ : S _⦋p + q - 1⦌) :
    φ.app _ (cupOneLeft S p q hq j σ) = cupOneLeft T p q hq j (φ.app _ σ) :=
  app_restrict φ _ σ

theorem app_cupOneRight {S T : _root_.SSet.{0}} (φ : S ⟶ T) (p q : ℕ) (j : Fin p)
    (σ : S _⦋p + q - 1⦌) :
    φ.app _ (cupOneRight S p q j σ) = cupOneRight T p q j (φ.app _ σ) :=
  app_restrict φ _ σ

end SSet

variable {S : SSet.{0}}

/-- The cup-one product of positive-degree simplicial cochains with mod-two coefficients. -/
def cupOne {p q : ℕ} (hq : 1 ≤ q) (f : Cochain S (ZMod 2) p)
    (g : Cochain S (ZMod 2) q) : Cochain S (ZMod 2) (p + q - 1) :=
  fun σ ↦ ∑ j : Fin p, f (SSet.cupOneLeft S p q hq j σ) *
    g (SSet.cupOneRight S p q j σ)

@[simp]
theorem cupOne_apply {p q : ℕ} (hq : 1 ≤ q) (f : Cochain S (ZMod 2) p)
    (g : Cochain S (ZMod 2) q) (σ : S _⦋p + q - 1⦌) :
    cupOne hq f g σ = ∑ j : Fin p, f (SSet.cupOneLeft S p q hq j σ) *
      g (SSet.cupOneRight S p q j σ) :=
  rfl

/-- Cup-one is bilinear on cochains. -/
def cupOneₗ {p q : ℕ} (hq : 1 ≤ q) :
    Cochain S (ZMod 2) p →ₗ[ZMod 2]
      Cochain S (ZMod 2) q →ₗ[ZMod 2] Cochain S (ZMod 2) (p + q - 1) :=
  LinearMap.mk₂ (ZMod 2) (cupOne hq)
    (fun f₁ f₂ g ↦ by
      ext σ
      simp only [cupOne_apply, Cochain.add_apply, add_mul, Finset.sum_add_distrib])
    (fun r f g ↦ by
      ext σ
      simp only [cupOne_apply, Cochain.smul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring)
    (fun f g₁ g₂ ↦ by
      ext σ
      simp only [cupOne_apply, Cochain.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r f g ↦ by
      ext σ
      simp only [cupOne_apply, Cochain.smul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring)

@[simp]
theorem cupOneₗ_apply {p q : ℕ} (hq : 1 ≤ q) (f : Cochain S (ZMod 2) p)
    (g : Cochain S (ZMod 2) q) : cupOneₗ hq f g = cupOne hq f g :=
  rfl

@[simp]
theorem add_cupOne {p q : ℕ} (hq : 1 ≤ q) (f₁ f₂ : Cochain S (ZMod 2) p)
    (g : Cochain S (ZMod 2) q) :
    cupOne hq (f₁ + f₂) g = cupOne hq f₁ g + cupOne hq f₂ g :=
  LinearMap.map_add₂ (cupOneₗ hq) f₁ f₂ g

@[simp]
theorem cupOne_add {p q : ℕ} (hq : 1 ≤ q) (f : Cochain S (ZMod 2) p)
    (g₁ g₂ : Cochain S (ZMod 2) q) :
    cupOne hq f (g₁ + g₂) = cupOne hq f g₁ + cupOne hq f g₂ :=
  (cupOneₗ hq f).map_add g₁ g₂

@[simp]
theorem zero_cupOne {p q : ℕ} (hq : 1 ≤ q) (g : Cochain S (ZMod 2) q) :
    cupOne hq (0 : Cochain S (ZMod 2) p) g = 0 := by
  exact (cupOneₗ hq).map_zero₂ g

@[simp]
theorem cupOne_zero {p q : ℕ} (hq : 1 ≤ q) (f : Cochain S (ZMod 2) p) :
    cupOne hq f (0 : Cochain S (ZMod 2) q) = 0 := by
  exact (cupOneₗ hq f).map_zero

/-- Pullback along a simplicial map preserves the cup-one product. -/
theorem pullback_cupOne {S T : SSet.{0}} (φ : S ⟶ T) {p q : ℕ} (hq : 1 ≤ q)
    (f : Cochain T (ZMod 2) p) (g : Cochain T (ZMod 2) q) :
    Cochain.pullback φ (p + q - 1) (cupOne hq f g) =
      cupOne hq (Cochain.pullback φ p f) (Cochain.pullback φ q g) := by
  ext σ
  simp only [Cochain.pullback_apply, cupOne_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [SSet.app_cupOneLeft, SSet.app_cupOneRight]

/-! ### The degree-three boundary formula -/

/-- A canonical spelling of a morphism `⦋3⦌ ⟶ ⦋6⦌`, determined by its values on the four
vertices.  This proof helper makes extensionally equal composite face maps definitionally equal
after reduction. -/
private def normalizeThreeFace (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋6⦌) :
    (⦋3⦌ : SimplexCategory) ⟶ ⦋6⦌ :=
  SimplexCategory.mkHom
    ⟨![h.toOrderHom 0, h.toOrderHom 1, h.toOrderHom 2, h.toOrderHom 3], by
      intro a b hab
      have hh := h.toOrderHom.monotone hab
      fin_cases a <;> fin_cases b <;> simp_all⟩

private theorem normalizeThreeFace_eq (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋6⦌) :
    normalizeThreeFace h = h :=
  hom_ext_val fun k ↦ by fin_cases k <;> rfl

/-- Restriction along a `3`-face of a `6`-simplex, with the face morphism in canonical form. -/
private def SSet.canonicalThreeFace (S : _root_.SSet.{0})
    (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋6⦌) (σ : S _⦋6⦌) : S _⦋3⦌ :=
  SSet.restrict S (normalizeThreeFace h) σ

private theorem SSet.restrict_eq_canonicalThreeFace (S : _root_.SSet.{0})
    (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋6⦌) (σ : S _⦋6⦌) :
    SSet.restrict S h σ = SSet.canonicalThreeFace S h σ := by
  rw [SSet.canonicalThreeFace, normalizeThreeFace_eq]

/-- A canonical spelling of a morphism `⦋2⦌ ⟶ ⦋5⦌`. -/
private def normalizeTwoFaceFive (h : (⦋2⦌ : SimplexCategory) ⟶ ⦋5⦌) :
    (⦋2⦌ : SimplexCategory) ⟶ ⦋5⦌ :=
  SimplexCategory.mkHom
    ⟨![h.toOrderHom 0, h.toOrderHom 1, h.toOrderHom 2], by
      intro a b hab
      have hh := h.toOrderHom.monotone hab
      fin_cases a <;> fin_cases b <;> simp_all⟩

private theorem normalizeTwoFaceFive_eq (h : (⦋2⦌ : SimplexCategory) ⟶ ⦋5⦌) :
    normalizeTwoFaceFive h = h :=
  hom_ext_val fun k ↦ by fin_cases k <;> rfl

private def SSet.canonicalTwoFaceFive (S : _root_.SSet.{0})
    (h : (⦋2⦌ : SimplexCategory) ⟶ ⦋5⦌) (σ : S _⦋5⦌) : S _⦋2⦌ :=
  SSet.restrict S (normalizeTwoFaceFive h) σ

private theorem SSet.restrict_eq_canonicalTwoFaceFive (S : _root_.SSet.{0})
    (h : (⦋2⦌ : SimplexCategory) ⟶ ⦋5⦌) (σ : S _⦋5⦌) :
    SSet.restrict S h σ = SSet.canonicalTwoFaceFive S h σ := by
  rw [SSet.canonicalTwoFaceFive, normalizeTwoFaceFive_eq]

/-- A canonical spelling of a morphism `⦋3⦌ ⟶ ⦋5⦌`. -/
private def normalizeThreeFaceFive (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋5⦌) :
    (⦋3⦌ : SimplexCategory) ⟶ ⦋5⦌ :=
  SimplexCategory.mkHom
    ⟨![h.toOrderHom 0, h.toOrderHom 1, h.toOrderHom 2, h.toOrderHom 3], by
      intro a b hab
      have hh := h.toOrderHom.monotone hab
      fin_cases a <;> fin_cases b <;> simp_all⟩

private theorem normalizeThreeFaceFive_eq (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋5⦌) :
    normalizeThreeFaceFive h = h :=
  hom_ext_val fun k ↦ by fin_cases k <;> rfl

private def SSet.canonicalThreeFaceFive (S : _root_.SSet.{0})
    (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋5⦌) (σ : S _⦋5⦌) : S _⦋3⦌ :=
  SSet.restrict S (normalizeThreeFaceFive h) σ

private theorem SSet.restrict_eq_canonicalThreeFaceFive (S : _root_.SSet.{0})
    (h : (⦋3⦌ : SimplexCategory) ⟶ ⦋5⦌) (σ : S _⦋5⦌) :
    SSet.restrict S h σ = SSet.canonicalThreeFaceFive S h σ := by
  rw [SSet.canonicalThreeFaceFive, normalizeThreeFaceFive_eq]

/-- The cup-one boundary formula in bidegree `(2, 3)`. -/
theorem coboundary_cupOne_two_three (f : Cochain S (ZMod 2) 2)
    (g : Cochain S (ZMod 2) 3) :
    coboundary S (ZMod 2) 4 (cupOne (by omega : 1 ≤ 3) f g) =
      cupOne (by omega : 1 ≤ 3) (coboundary S (ZMod 2) 2 f) g +
        cupOne (by omega : 1 ≤ 4) f (coboundary S (ZMod 2) 3 g) +
          cupOfEq rfl f g + cupOfEq rfl g f := by
  ext σ
  simp only [coboundary_apply, cupOne_apply, cupOfEq_apply, Cochain.add_apply]
  have hneg : (-1 : ZMod 2) = 1 := by decide
  simp only [hneg, one_pow, one_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [SSet.cupOneLeft, SSet.cupOneRight, SSet.face_eq_restrict, SSet.front,
    SSet.back, SSet.restrict_restrict]
  simp only [SSet.restrict_eq_canonicalTwoFaceFive,
    SSet.restrict_eq_canonicalThreeFaceFive]
  simp only [SSet.canonicalTwoFaceFive, SSet.canonicalThreeFaceFive,
    normalizeTwoFaceFive, normalizeThreeFaceFive, cupOneLeftHom, cupOneRightHom,
    frontHom, backHom, SimplexCategory.δ, SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  simp [Fin.succAbove]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [htwo, mul_zero, add_zero]

/-- The cup-one boundary formula in bidegree `(3, 2)`. -/
theorem coboundary_cupOne_three_two (f : Cochain S (ZMod 2) 3)
    (g : Cochain S (ZMod 2) 2) :
    coboundary S (ZMod 2) 4 (cupOne (by omega : 1 ≤ 2) f g) =
      cupOne (by omega : 1 ≤ 2) (coboundary S (ZMod 2) 3 f) g +
        cupOne (by omega : 1 ≤ 3) f (coboundary S (ZMod 2) 2 g) +
          cupOfEq rfl f g + cupOfEq rfl g f := by
  ext σ
  simp only [coboundary_apply, cupOne_apply, cupOfEq_apply, Cochain.add_apply]
  have hneg : (-1 : ZMod 2) = 1 := by decide
  simp only [hneg, one_pow, one_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [SSet.cupOneLeft, SSet.cupOneRight, SSet.face_eq_restrict, SSet.front,
    SSet.back, SSet.restrict_restrict]
  simp only [SSet.restrict_eq_canonicalTwoFaceFive,
    SSet.restrict_eq_canonicalThreeFaceFive]
  simp only [SSet.canonicalTwoFaceFive, SSet.canonicalThreeFaceFive,
    normalizeTwoFaceFive, normalizeThreeFaceFive, cupOneLeftHom, cupOneRightHom,
    frontHom, backHom, SimplexCategory.δ, SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  simp [Fin.succAbove]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [htwo, mul_zero, add_zero]

/-- In degree three, cup-one is a chain homotopy over `ZMod 2` between the cup product and its
transpose.  This is the cochain identity underlying the operation `Sq^2` on degree-three
classes. -/
theorem coboundary_cupOne_three_three (f g : Cochain S (ZMod 2) 3) :
    coboundary S (ZMod 2) 5 (cupOne (by omega : 1 ≤ 3) f g) =
      cupOne (by omega : 1 ≤ 3) (coboundary S (ZMod 2) 3 f) g +
        cupOne (by omega : 1 ≤ 4) f (coboundary S (ZMod 2) 3 g) +
          cupOfEq rfl f g + cupOfEq rfl g f := by
  ext σ
  simp only [coboundary_apply, cupOne_apply, cupOfEq_apply, Cochain.add_apply]
  have hneg : (-1 : ZMod 2) = 1 := by decide
  simp only [hneg, one_pow, one_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [SSet.cupOneLeft, SSet.cupOneRight, SSet.face_eq_restrict, SSet.front,
    SSet.back, SSet.restrict_restrict]
  simp only [SSet.restrict_eq_canonicalThreeFace]
  simp only [SSet.canonicalThreeFace, normalizeThreeFace, cupOneLeftHom, cupOneRightHom,
    frontHom, backHom, SimplexCategory.δ, SimplexCategory.len_mk, SimplexCategory.mkHom,
    SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
    Fin.succAboveOrderEmb_apply]
  simp [Fin.succAbove]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [htwo, mul_zero, add_zero]

/-! ### Independence of the degree-three square from cocycle representatives -/

/-- An explicit degree-four cochain whose coboundary measures the change in the degree-three
cup-one square after adding the coboundary of `h`. -/
def cupOneThreeRepresentativeChangeWitness (f : Cochain S (ZMod 2) 3)
    (h : Cochain S (ZMod 2) 2) : Cochain S (ZMod 2) 4 :=
  cupOne (by omega : 1 ≤ 3) h f +
    cupOne (by omega : 1 ≤ 2) f h +
      cupOne (by omega : 1 ≤ 3) h (coboundary S (ZMod 2) 2 h) +
        cupOfEq rfl h h

/-- Adding a coboundary to a degree-three cocycle changes its cup-one square by the coboundary
of `cupOneThreeRepresentativeChangeWitness`. -/
theorem coboundary_cupOneThreeRepresentativeChangeWitness
    {f : Cochain S (ZMod 2) 3} (hf : f ∈ cocycles S (ZMod 2) 3)
    (h : Cochain S (ZMod 2) 2) :
    coboundary S (ZMod 2) 4 (cupOneThreeRepresentativeChangeWitness f h) =
      cupOne (by omega : 1 ≤ 3) (f + coboundary S (ZMod 2) 2 h)
          (f + coboundary S (ZMod 2) 2 h) +
        cupOne (by omega : 1 ≤ 3) f f := by
  have hf0 : coboundary S (ZMod 2) 3 f = 0 := (mem_cocycles_iff f).1 hf
  have hdd :
      coboundary S (ZMod 2) 3 (coboundary S (ZMod 2) 2 h) = 0 :=
    coboundary_coboundary h
  simp only [cupOneThreeRepresentativeChangeWitness, map_add,
    coboundary_cupOne_two_three, coboundary_cupOne_three_two,
    coboundary_cupOfEq, hf0, hdd, zero_cupOne, cupOne_zero,
    zero_add, add_zero, add_cupOne, cupOne_add]
  ext σ
  simp only [Cochain.add_apply, Cochain.smul_apply]
  have hneg : (-1 : ZMod 2) = 1 := by decide
  simp only [hneg, one_pow, one_mul]
  ring_nf
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [htwo, mul_zero, add_zero]

/-- The cup-one self-product of a degree-three mod-two cocycle is a degree-five cocycle. -/
theorem cupOne_three_self_mem_cocycles {f : Cochain S (ZMod 2) 3}
    (hf : f ∈ cocycles S (ZMod 2) 3) :
    cupOne (by omega : 1 ≤ 3) f f ∈ cocycles S (ZMod 2) 5 := by
  rw [mem_cocycles_iff, coboundary_cupOne_three_three,
    (mem_cocycles_iff f).1 hf, zero_cupOne, cupOne_zero, zero_add]
  simp only [zero_add]
  ext σ
  simp only [Cochain.add_apply, Cochain.zero_apply, cupOfEq_apply]
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    f (SSet.front S (by omega) σ) * f (SSet.back S (by omega) σ) +
          f (SSet.front S (by omega) σ) * f (SSet.back S (by omega) σ) =
        2 * (f (SSet.front S (by omega) σ) * f (SSet.back S (by omega) σ)) := by ring
    _ = 0 := by rw [htwo, zero_mul]

/-- The degree-five cocycle obtained as the cup-one square of a degree-three cocycle. -/
def cupOneThreeSelfCocycle (f : cocycles S (ZMod 2) 3) : cocycles S (ZMod 2) 5 :=
  ⟨cupOne (by omega : 1 ≤ 3) (f : Cochain S (ZMod 2) 3) f,
    cupOne_three_self_mem_cocycles f.2⟩

@[simp]
theorem cupOneThreeSelfCocycle_coe (f : cocycles S (ZMod 2) 3) :
    ((cupOneThreeSelfCocycle f : cocycles S (ZMod 2) 5) : Cochain S (ZMod 2) 5) =
      cupOne (by omega : 1 ≤ 3) (f : Cochain S (ZMod 2) 3) f :=
  rfl

/-- Add the coboundary of a degree-two cochain to a degree-three cocycle. -/
def degreeThreeCocycleAddCoboundary (f : cocycles S (ZMod 2) 3)
    (h : Cochain S (ZMod 2) 2) : cocycles S (ZMod 2) 3 :=
  f + ⟨coboundary S (ZMod 2) 2 h, coboundary_coboundary h⟩

@[simp]
theorem degreeThreeCocycleAddCoboundary_coe (f : cocycles S (ZMod 2) 3)
    (h : Cochain S (ZMod 2) 2) :
    ((degreeThreeCocycleAddCoboundary f h : cocycles S (ZMod 2) 3) :
        Cochain S (ZMod 2) 3) =
      (f : Cochain S (ZMod 2) 3) + coboundary S (ZMod 2) 2 h :=
  rfl

/-- The cohomology class of the degree-three cup-one square is unchanged after adding a
coboundary to its cocycle representative. -/
theorem cupOneThreeSelfClass_add_coboundary (f : cocycles S (ZMod 2) 3)
    (h : Cochain S (ZMod 2) 2) :
    Hcoh.mk (cupOneThreeSelfCocycle (degreeThreeCocycleAddCoboundary f h)) =
      Hcoh.mk (cupOneThreeSelfCocycle f) := by
  apply (Submodule.Quotient.eq (coboundariesIn S (ZMod 2) 5)).2
  change
    (cupOne (by omega : 1 ≤ 3)
          ((f : Cochain S (ZMod 2) 3) + coboundary S (ZMod 2) 2 h)
          ((f : Cochain S (ZMod 2) 3) + coboundary S (ZMod 2) 2 h) -
        cupOne (by omega : 1 ≤ 3) (f : Cochain S (ZMod 2) 3) f) ∈
      coboundaries S (ZMod 2) 5
  rw [coboundaries_succ]
  refine ⟨cupOneThreeRepresentativeChangeWitness (f : Cochain S (ZMod 2) 3) h, ?_⟩
  rw [coboundary_cupOneThreeRepresentativeChangeWitness f.2]
  ext σ
  simp only [Cochain.add_apply, Cochain.sub_apply, ZMod.neg_eq_self_mod_two, sub_eq_add_neg]

/-- The degree-three instance of the second Steenrod square,
`Sq^2 : H^3(S; F_2) → H^5(S; F_2)`, defined by the cup-one self-product of a cocycle
representative. -/
def sqTwoDegreeThree (x : Hcoh 3 S (ZMod 2)) : Hcoh 5 S (ZMod 2) :=
  Quotient.liftOn' x (fun f ↦ Hcoh.mk (cupOneThreeSelfCocycle f)) fun a b hab ↦ by
    have hab' :
        ((a - b : cocycles S (ZMod 2) 3) : Cochain S (ZMod 2) 3) ∈
          coboundaries S (ZMod 2) 3 := by
      exact (Submodule.quotientRel_def (p := coboundariesIn S (ZMod 2) 3)).mp hab
    rw [coboundaries_succ] at hab'
    obtain ⟨h, hh⟩ := hab'
    have ha : degreeThreeCocycleAddCoboundary b h = a := by
      apply Subtype.ext
      simp only [degreeThreeCocycleAddCoboundary_coe, hh]
      change (b : Cochain S (ZMod 2) 3) + ((a : Cochain S (ZMod 2) 3) - b) = a
      rw [add_comm]
      exact sub_add_cancel (a : Cochain S (ZMod 2) 3) b
    simpa only [ha] using cupOneThreeSelfClass_add_coboundary b h

@[simp]
theorem sqTwoDegreeThree_mk (f : cocycles S (ZMod 2) 3) :
    sqTwoDegreeThree (Hcoh.mk f) = Hcoh.mk (cupOneThreeSelfCocycle f) :=
  rfl

/-- The cup-one square cocycle is natural under maps of simplicial sets. -/
theorem cupOneThreeSelfCocycle_natural {S T : SSet.{0}} (φ : S ⟶ T)
    (f : cocycles T (ZMod 2) 3) :
    cupOneThreeSelfCocycle (cocyclesMap (ZMod 2) φ 3 f) =
      cocyclesMap (ZMod 2) φ 5 (cupOneThreeSelfCocycle f) := by
  apply Subtype.ext
  exact (pullback_cupOne φ (by omega : 1 ≤ 3)
    (f : Cochain T (ZMod 2) 3) f).symm

/-- `Sq^2 : H^3 → H^5` is natural under maps of simplicial sets. -/
theorem sqTwoDegreeThree_natural {S T : SSet.{0}} (φ : S ⟶ T)
    (x : Hcoh 3 T (ZMod 2)) :
    Hcoh.map (ZMod 2) φ 5 (sqTwoDegreeThree x) =
      sqTwoDegreeThree (Hcoh.map (ZMod 2) φ 3 x) := by
  refine Hcoh.induction_on x fun f ↦ ?_
  simp only [sqTwoDegreeThree_mk, Hcoh.map_mk]
  congr 1
  exact (cupOneThreeSelfCocycle_natural φ f).symm

end Submission
