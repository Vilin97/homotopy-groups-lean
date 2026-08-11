/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.MayerVietorisLES
import Submission.Homology.Contractible

/-!
# Collapsing the Mayer–Vietoris sequence

The standard use of Mayer–Vietoris is: if `A` and `B` have vanishing homology in two consecutive
degrees, the connecting homomorphism `∂ : Hₙ₊₁(X) ⟶ Hₙ(A ∩ B)` is an isomorphism.  This is what
turns the covering of a sphere by two contractible pieces into the inductive step
`H̃ₖ₊₁(Sⁿ⁺¹) ≅ H̃ₖ(Sⁿ)`.

## Main results

* `isZero_mvSum` — `Hₙ(A) ⊞ Hₙ(B)` vanishes when both summands do;
* `isIso_mvδ` — the connecting map is an isomorphism when four homology groups vanish;
* `mvδIso` — the resulting isomorphism `Hₙ₊₁(X) ≅ Hₙ(A ∩ B)`;
* `mvδIso_of_contractible` — the case where `A` and `B` are contractible.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X)

/-- A biproduct of two zero objects is zero. -/
lemma isZero_biprod {C : Type*} [Category* C] [Preadditive C] {Y Z : C} [HasBinaryBiproduct Y Z]
    (hY : IsZero Y) (hZ : IsZero Z) : IsZero (Y ⊞ Z) := by
  refine (IsZero.iff_id_eq_zero _).2 (biprod.hom_ext' _ _ ?_ ?_)
  · rw [Category.comp_id, comp_zero]
    exact hY.eq_zero_of_src _
  · rw [Category.comp_id, comp_zero]
    exact hZ.eq_zero_of_src _

/-- `Hₙ(A) ⊞ Hₙ(B)` vanishes when both summands do. -/
lemma isZero_mvSum (n : ℕ) (hA : IsZero (Hgrp n (TopCat.of A)))
    (hB : IsZero (Hgrp n (TopCat.of B))) : IsZero (mvSum A B n) :=
  isZero_biprod hA hB

/-- **Mayer–Vietoris collapse.**  If `Hₙ` and `Hₙ₊₁` of both `A` and `B` vanish, the connecting
homomorphism `∂ : Hₙ₊₁(X) ⟶ Hₙ(A ∩ B)` is an isomorphism. -/
theorem isIso_mvδ (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    (hA1 : IsZero (Hgrp (n + 1) (TopCat.of A))) (hB1 : IsZero (Hgrp (n + 1) (TopCat.of B)))
    (hA0 : IsZero (Hgrp n (TopCat.of A))) (hB0 : IsZero (Hgrp n (TopCat.of B))) :
    IsIso (mvδ A B h n) := by
  have hκ : mvKappa A B (n + 1) = 0 := (isZero_mvSum A B (n + 1) hA1 hB1).eq_zero_of_src _
  have hι : mvIota A B n = 0 := (isZero_mvSum A B n hA0 hB0).eq_zero_of_tgt _
  have : Mono (mvδ A B h n) := (mayerVietoris_exact_kappa_δ A B h n).mono_g hκ
  have : Epi (mvδ A B h n) := (mayerVietoris_exact_δ_iota A B h n).epi_f hι
  exact isIso_of_mono_of_epi _

/-- The Mayer–Vietoris isomorphism `Hₙ₊₁(X) ≅ Hₙ(A ∩ B)` when `A` and `B` have vanishing homology
in degrees `n` and `n + 1`. -/
def mvδIso (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    (hA1 : IsZero (Hgrp (n + 1) (TopCat.of A))) (hB1 : IsZero (Hgrp (n + 1) (TopCat.of B)))
    (hA0 : IsZero (Hgrp n (TopCat.of A))) (hB0 : IsZero (Hgrp n (TopCat.of B))) :
    Hgrp (n + 1) X ≅ Hgrp n (TopCat.of (A ∩ B : Set X)) :=
  have : IsIso (mvδ A B h n) := isIso_mvδ A B h n hA1 hB1 hA0 hB0
  asIso (mvδ A B h n)

/-- If `A` and `B` are contractible, `∂ : Hₙ₊₂(X) ≅ Hₙ₊₁(A ∩ B)` for every `n`. -/
def mvδIso_of_contractible (h : interior A ∪ interior B = Set.univ) (n : ℕ)
    [ContractibleSpace A] [ContractibleSpace B] :
    Hgrp (n + 2) X ≅ Hgrp (n + 1) (TopCat.of (A ∩ B : Set X)) :=
  mvδIso A B h (n + 1)
    (isZero_Hgrp_of_contractible (X := TopCat.of A) (n + 1))
    (isZero_Hgrp_of_contractible (X := TopCat.of B) (n + 1))
    (isZero_Hgrp_of_contractible (X := TopCat.of A) n)
    (isZero_Hgrp_of_contractible (X := TopCat.of B) n)

/-- **Mayer–Vietoris in degree one.**  If `H₁(A)` and `H₁(B)` vanish and
`H₀(A ∩ B) ⟶ H₀(A) ⊞ H₀(B)` is a monomorphism, then `H₁(X)` vanishes. -/
theorem isZero_Hgrp_one_of_mono_mvIota (h : interior A ∪ interior B = Set.univ)
    (hA : IsZero (Hgrp 1 (TopCat.of A))) (hB : IsZero (Hgrp 1 (TopCat.of B)))
    (hmono : Mono (mvIota A B 0)) : IsZero (Hgrp 1 X) := by
  have hK : mvKappa A B 1 = 0 := (isZero_mvSum A B 1 hA hB).eq_zero_of_src _
  have hmonoδ : Mono (mvδ A B h 0) := (mayerVietoris_exact_kappa_δ A B h 0).mono_g hK
  have hδ0 : mvδ A B h 0 = 0 := (mayerVietoris_exact_δ_iota A B h 0).mono_g_iff.1 hmono
  refine (IsZero.iff_id_eq_zero _).2 (hmonoδ.right_cancellation _ _ ?_)
  rw [hδ0, comp_zero, comp_zero]

/-- `H₀(A ∩ B) ⟶ H₀(A) ⊞ H₀(B)` is a monomorphism as soon as its first component is. -/
theorem mono_mvIota_of_mono_left (hm : Mono (HgrpMap 0 (mvInclLeft A B))) :
    Mono (mvIota A B 0) :=
  mono_of_mono_fac (biprod.lift_fst (HgrpMap 0 (mvInclLeft A B))
    (HgrpMap 0 (mvInclRight A B)))

end Submission
