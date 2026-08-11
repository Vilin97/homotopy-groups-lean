/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Submission.Homology.MayerVietorisIso

/-!
# The Wang exact sequence

Let `p : E → Sᵐ` be a fibration with fibre `F`, and write `D₊`, `D₋` for the two enlarged closed
hemispheres of `Sᵐ`, so that `D₊ ∩ D₋ ≃ S^{m-1}`. Put `A = p⁻¹(D₊)`, `B = p⁻¹(D₋)`. Both `D±` are
contractible, so `A ≃ F ≃ B`, and — because the trivialisation over `D₊` *restricts* to
`D₊ ∩ D₋` (`Submission/Homotopy/DiscTrivialisation.lean`; this is where Dold's theorem is
avoided) — the inclusion `A ∩ B → A` becomes, after the identifications
`A ∩ B ≃ F × S^{m-1}` and `A ≃ F`, the projection onto the first factor. Feeding
`H_*(F × S^{m-1}) ≅ H_*(F) ⊕ H_{*-(m-1)}(F)` into Mayer–Vietoris and cancelling the resulting
diagonal copy of `H_*(F)` gives the **Wang exact sequence**.

## The interface

All of the above is packaged into `Submission.WangDatum E d`, whose only fields are

* two subsets `A B : Set E` whose interiors cover `E`;
* a space `fibre`;
* for every `n`, an isomorphism `split n : H_{n+d}(A ∩ B) ≅ H_{n+d}(A) ⊞ Hₙ(fibre)`;
* `split_fst`: the first component of `split n` is the map induced by `A ∩ B → A`.

Nothing else is assumed — in particular no comparison between the two trivialisations, and no
hypothesis on `E`. Here `d = m - 1` is the dimension of `D₊ ∩ D₋`.

## Main results

* `Submission.WangDatum.theta` — the **Wang map** `θ : Hₙ(F) ⟶ H_{n+d}(B)`, which raises degree
  by `d`;
* `Submission.WangDatum.wang_exact_theta_alpha`, `..._alpha_beta`, `..._beta_theta` — exactness of
```
    ⋯ ⟶ H_{n+d+1}(E) --β--> Hₙ(F) --θ--> H_{n+d}(B) --α--> H_{n+d}(E) --β--> H_{n-1}(F) ⟶ ⋯
```
  at the three consecutive spots;
* `Submission.WangDatum.isIso_theta` — if `H_{n+d}(E)` and `H_{n+d+1}(E)` vanish then `θ` is an
  isomorphism. This is the form used to compute `H_*(Ω S^{m})`, whose total space (a path space)
  is contractible.

`H_{n+d}(B)` rather than `H_{n+d}(F)` appears in the sequence because the datum deliberately does
not include an identification of `H_*(B)` with `H_*(F)`; `Submission.WangDatum.thetaF` restates
the Wang map through such an identification when one is supplied.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-! ### Elementwise calculus in a biproduct of abelian groups -/

section Biprod

variable {X Y Z W : AddCommGrpCat.{0}}

/-- The first component of an element of a biproduct of abelian groups. -/
def bfst (z : ↥(X ⊞ Y)) : X := (biprod.fst : X ⊞ Y ⟶ X) z

/-- The second component of an element of a biproduct of abelian groups. -/
def bsnd (z : ↥(X ⊞ Y)) : Y := (biprod.snd : X ⊞ Y ⟶ Y) z

/-- The image of an element of `X` in `X ⊞ Y`. -/
def binl (x : X) : ↥(X ⊞ Y) := (biprod.inl : X ⟶ X ⊞ Y) x

/-- The image of an element of `Y` in `X ⊞ Y`. -/
def binr (y : Y) : ↥(X ⊞ Y) := (biprod.inr : Y ⟶ X ⊞ Y) y

@[simp] theorem bfst_binl (x : X) : bfst (binl x : ↥(X ⊞ Y)) = x := by
  rw [bfst, binl, ← ConcreteCategory.comp_apply, biprod.inl_fst, ConcreteCategory.id_apply]

@[simp] theorem bsnd_binl (x : X) : bsnd (binl x : ↥(X ⊞ Y)) = 0 := by
  rw [bsnd, binl, ← ConcreteCategory.comp_apply, biprod.inl_snd]
  rfl

@[simp] theorem bfst_binr (y : Y) : bfst (binr y : ↥(X ⊞ Y)) = 0 := by
  rw [bfst, binr, ← ConcreteCategory.comp_apply, biprod.inr_fst]
  rfl

@[simp] theorem bsnd_binr (y : Y) : bsnd (binr y : ↥(X ⊞ Y)) = y := by
  rw [bsnd, binr, ← ConcreteCategory.comp_apply, biprod.inr_snd, ConcreteCategory.id_apply]

@[simp] theorem bfst_zero : bfst (0 : ↥(X ⊞ Y)) = 0 := map_zero _

@[simp] theorem bsnd_zero : bsnd (0 : ↥(X ⊞ Y)) = 0 := map_zero _

theorem binl_add_binr (z : ↥(X ⊞ Y)) : binl (bfst z) + binr (bsnd z) = z := by
  conv_rhs => rw [← ConcreteCategory.id_apply (X := X ⊞ Y) z, ← biprod.total]
  rw [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rfl

theorem bext {z w : ↥(X ⊞ Y)} (h1 : bfst z = bfst w) (h2 : bsnd z = bsnd w) : z = w := by
  rw [← binl_add_binr z, ← binl_add_binr w, h1, h2]

theorem bext_zero {z : ↥(X ⊞ Y)} (h1 : bfst z = 0) (h2 : bsnd z = 0) : z = 0 :=
  bext (h1.trans bfst_zero.symm) (h2.trans bsnd_zero.symm)

theorem biprod_desc_apply (f : X ⟶ Z) (g : Y ⟶ Z) (z : ↥(X ⊞ Y)) :
    biprod.desc f g z = f (bfst z) + g (bsnd z) := by
  rw [biprod.desc_eq, AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  rfl

theorem bfst_lift_apply (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    bfst (biprod.lift f g w : ↥(X ⊞ Y)) = f w := by
  rw [bfst, ← ConcreteCategory.comp_apply, biprod.lift_fst]

theorem bsnd_lift_apply (f : W ⟶ X) (g : W ⟶ Y) (w : W) :
    bsnd (biprod.lift f g w : ↥(X ⊞ Y)) = g w := by
  rw [bsnd, ← ConcreteCategory.comp_apply, biprod.lift_snd]

end Biprod

/-! ### The Wang datum -/

variable {E : TopCat.{0}} {d : ℕ}

/-- The input to the Wang exact sequence: a space `E` covered by the interiors of two subspaces
`A` and `B`, together with a splitting `H_{n+d}(A ∩ B) ≅ H_{n+d}(A) ⊞ Hₙ(fibre)` whose first
component is the map induced by the inclusion `A ∩ B → A`.

For a fibration over `Sᵐ` this is realised with `A = p⁻¹(D₊)`, `B = p⁻¹(D₋)`, `d = m - 1`, and
the splitting coming from `A ∩ B ≃ F × S^{m-1}` together with the product formula for homology;
the compatibility `split_fst` is exactly the statement that the trivialisation over `D₊`
restricts to `D₊ ∩ D₋`. -/
structure WangDatum (E : TopCat.{0}) (d : ℕ) where
  /-- The first piece of the cover, `p⁻¹(D₊)`. -/
  A : Set E
  /-- The second piece of the cover, `p⁻¹(D₋)`. -/
  B : Set E
  /-- The interiors of the two pieces cover `E`. -/
  cover : interior A ∪ interior B = Set.univ
  /-- The fibre. -/
  fibre : TopCat.{0}
  /-- The splitting of the homology of the overlap. -/
  split (n : ℕ) :
    Hgrp (n + d) (TopCat.of (A ∩ B : Set E)) ≅ Hgrp (n + d) (TopCat.of A) ⊞ Hgrp n fibre
  /-- The first component of the splitting is the map induced by `A ∩ B → A`. -/
  split_fst (n : ℕ) : (split n).hom ≫ biprod.fst = HgrpMap (n + d) (mvInclLeft A B)

namespace WangDatum

variable (W : WangDatum E d)

/-! #### The maps of the sequence -/

/-- The **Wang map** `θ : Hₙ(F) ⟶ H_{n+d}(B)`; it raises degree by `d = m - 1`. -/
def theta (n : ℕ) : Hgrp n W.fibre ⟶ Hgrp (n + d) (TopCat.of W.B) :=
  biprod.inr ≫ (W.split n).inv ≫ HgrpMap (n + d) (mvInclRight W.A W.B)

/-- The leading term `H_{n+d}(A) ⟶ H_{n+d}(B)` of the clutching automorphism. It plays no role in
the exactness of the Wang sequence, only in its multiplicative refinement. -/
def lead (n : ℕ) : Hgrp (n + d) (TopCat.of W.A) ⟶ Hgrp (n + d) (TopCat.of W.B) :=
  biprod.inl ≫ (W.split n).inv ≫ HgrpMap (n + d) (mvInclRight W.A W.B)

/-- The map `H_k(B) ⟶ H_k(E)` induced by the inclusion. -/
def alpha (k : ℕ) : Hgrp k (TopCat.of W.B) ⟶ Hgrp k E := HgrpMap k (subIncl W.B)

/-- The map `H_{n+d+1}(E) ⟶ Hₙ(F)`: the Mayer–Vietoris connecting homomorphism followed by the
projection onto the second summand of the splitting. -/
def beta (n : ℕ) : Hgrp (n + d + 1) E ⟶ Hgrp n W.fibre :=
  mvδ W.A W.B W.cover (n + d) ≫ (W.split n).hom ≫ biprod.snd

/-! #### Reading off the two inclusions -/

theorem inclLeft_apply (n : ℕ) (z : Hgrp (n + d) (TopCat.of (W.A ∩ W.B : Set E))) :
    HgrpMap (n + d) (mvInclLeft W.A W.B) z = bfst ((W.split n).hom z) := by
  rw [← W.split_fst n, ConcreteCategory.comp_apply]
  rfl

theorem lead_apply (n : ℕ) (x : Hgrp (n + d) (TopCat.of W.A)) :
    W.lead n x = HgrpMap (n + d) (mvInclRight W.A W.B) ((W.split n).inv (binl x)) := by
  rw [lead, binl, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

theorem theta_apply (n : ℕ) (y : Hgrp n W.fibre) :
    W.theta n y = HgrpMap (n + d) (mvInclRight W.A W.B) ((W.split n).inv (binr y)) := by
  rw [theta, binr, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

theorem inclRight_apply (n : ℕ) (z : Hgrp (n + d) (TopCat.of (W.A ∩ W.B : Set E))) :
    HgrpMap (n + d) (mvInclRight W.A W.B) z
      = W.lead n (bfst ((W.split n).hom z)) + W.theta n (bsnd ((W.split n).hom z)) := by
  have hz : (W.split n).inv ((W.split n).hom z) = z := by
    rw [← ConcreteCategory.comp_apply, (W.split n).hom_inv_id, ConcreteCategory.id_apply]
  rw [W.lead_apply, W.theta_apply, ← map_add, ← map_add, binl_add_binr, hz]

/-- `A ∩ B → A` is surjective on homology in every degree of the form `n + d`. -/
theorem inclLeft_surjective {k n : ℕ} (hk : k = n + d) :
    Function.Surjective (HgrpMap k (mvInclLeft W.A W.B)) := by
  subst hk
  intro a
  refine ⟨(W.split n).inv (binl a), ?_⟩
  rw [inclLeft_apply, ← ConcreteCategory.comp_apply, (W.split n).inv_hom_id,
    ConcreteCategory.id_apply, bfst_binl]

/-! #### The Mayer–Vietoris maps in coordinates -/

theorem bfst_mvIota (n : ℕ) (z : Hgrp n (TopCat.of (W.A ∩ W.B : Set E))) :
    bfst (mvIota W.A W.B n z) = HgrpMap n (mvInclLeft W.A W.B) z :=
  bfst_lift_apply _ _ z

theorem bsnd_mvIota (n : ℕ) (z : Hgrp n (TopCat.of (W.A ∩ W.B : Set E))) :
    bsnd (mvIota W.A W.B n z) = HgrpMap n (mvInclRight W.A W.B) z :=
  bsnd_lift_apply _ _ z

theorem mvKappa_apply (n : ℕ) (w : ↥(mvSum W.A W.B n)) :
    mvKappa W.A W.B n w = HgrpMap n (subIncl W.A) (bfst w) - HgrpMap n (subIncl W.B) (bsnd w) := by
  rw [mvKappa, biprod_desc_apply, sub_eq_add_neg]
  rfl

/-- Both inclusions of the overlap into `E` agree. -/
theorem subIncl_inclLeft_apply (n : ℕ) (z : Hgrp n (TopCat.of (W.A ∩ W.B : Set E))) :
    HgrpMap n (subIncl W.A) (HgrpMap n (mvInclLeft W.A W.B) z)
      = HgrpMap n (subIncl W.B) (HgrpMap n (mvInclRight W.A W.B) z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HgrpMap_comp, ← HgrpMap_comp,
    mvInclLeft_comp, mvInclRight_comp]

/-! ### Exactness of the Wang sequence -/

theorem hom_inv_apply (n : ℕ) (u : ↥(Hgrp (n + d) (TopCat.of W.A) ⊞ Hgrp n W.fibre)) :
    (W.split n).hom ((W.split n).inv u) = u := by
  rw [← ConcreteCategory.comp_apply, (W.split n).inv_hom_id, ConcreteCategory.id_apply]

theorem inv_hom_apply (n : ℕ) (z : Hgrp (n + d) (TopCat.of (W.A ∩ W.B : Set E))) :
    (W.split n).inv ((W.split n).hom z) = z := by
  rw [← ConcreteCategory.comp_apply, (W.split n).hom_inv_id, ConcreteCategory.id_apply]

theorem theta_comp_alpha (n : ℕ) : W.theta n ≫ W.alpha (n + d) = 0 := by
  ext b
  have hA : HgrpMap (n + d) (mvInclLeft W.A W.B) ((W.split n).inv (binr b)) = 0 := by
    rw [inclLeft_apply, W.hom_inv_apply, bfst_binr]
  show W.alpha (n + d) (W.theta n b) = 0
  rw [W.theta_apply, alpha, ← subIncl_inclLeft_apply, hA, map_zero]

/-- **Wang, exactness at `H_{n+d}(B)`:** `Hₙ(F) --θ--> H_{n+d}(B) --α--> H_{n+d}(E)`. -/
theorem wang_exact_theta_alpha (n : ℕ) :
    (ShortComplex.mk (W.theta n) (W.alpha (n + d)) (W.theta_comp_alpha n)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hκ : mvKappa W.A W.B (n + d) (binr y) = 0 := by
    rw [mvKappa_apply, bfst_binr, bsnd_binr, map_zero, zero_sub, neg_eq_zero]
    exact hy
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_iota_kappa W.A W.B W.cover (n + d)) (binr y) hκ
  have hA : HgrpMap (n + d) (mvInclLeft W.A W.B) z = 0 := by
    rw [← bfst_mvIota, hz, bfst_binr]
  have hB : HgrpMap (n + d) (mvInclRight W.A W.B) z = y := by
    rw [← bsnd_mvIota, hz, bsnd_binr]
  refine ⟨bsnd ((W.split n).hom z), ?_⟩
  have hfst : bfst ((W.split n).hom z) = 0 := by rw [← inclLeft_apply, hA]
  have hz' : (W.split n).hom z = binr (bsnd ((W.split n).hom z)) :=
    bext (by rw [hfst, bfst_binr]) (by rw [bsnd_binr])
  show W.theta n (bsnd ((W.split n).hom z)) = y
  rw [W.theta_apply, ← hz', W.inv_hom_apply, hB]

theorem beta_apply (n : ℕ) (x : Hgrp (n + d + 1) E) :
    W.beta n x = bsnd ((W.split n).hom (mvδ W.A W.B W.cover (n + d) x)) := by
  rw [beta, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rfl

theorem alpha_comp_beta (n : ℕ) : W.alpha (n + d + 1) ≫ W.beta n = 0 := by
  ext y
  have hk : mvKappa W.A W.B (n + d + 1) (binr y) = -HgrpMap (n + d + 1) (subIncl W.B) y := by
    rw [mvKappa_apply, bfst_binr, bsnd_binr, map_zero, zero_sub]
  have h0 : mvδ W.A W.B W.cover (n + d) (mvKappa W.A W.B (n + d + 1) (binr y)) = 0 := by
    rw [← ConcreteCategory.comp_apply, mvKappa_comp_mvδ]
    rfl
  rw [hk, map_neg, neg_eq_zero] at h0
  show W.beta n (W.alpha (n + d + 1) y) = 0
  rw [W.beta_apply, alpha, h0, map_zero, bsnd_zero]

/-- **Wang, exactness at `H_{n+d+1}(E)`:**
`H_{n+d+1}(B) --α--> H_{n+d+1}(E) --β--> Hₙ(F)`. -/
theorem wang_exact_alpha_beta (n : ℕ) :
    (ShortComplex.mk (W.alpha (n + d + 1)) (W.beta n) (W.alpha_comp_beta n)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  have hsnd : bsnd ((W.split n).hom (mvδ W.A W.B W.cover (n + d) x)) = 0 := by
    rw [← W.beta_apply]; exact hx
  have hiota : mvIota W.A W.B (n + d) (mvδ W.A W.B W.cover (n + d) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, mvδ_comp_mvIota]
    rfl
  have hfst : bfst ((W.split n).hom (mvδ W.A W.B W.cover (n + d) x)) = 0 := by
    rw [← inclLeft_apply, ← bfst_mvIota, hiota, bfst_zero]
  have hz0 : mvδ W.A W.B W.cover (n + d) x = 0 := by
    rw [← W.inv_hom_apply n (mvδ W.A W.B W.cover (n + d) x), bext_zero hfst hsnd, map_zero]
  obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_kappa_δ W.A W.B W.cover (n + d)) x hz0
  obtain ⟨v, hv⟩ := W.inclLeft_surjective (Nat.add_right_comm n d 1) (bfst w)
  have hdiag := W.subIncl_inclLeft_apply (n + d + 1) v
  rw [hv] at hdiag
  refine ⟨HgrpMap (n + d + 1) (mvInclRight W.A W.B) v - bsnd w, ?_⟩
  show HgrpMap (n + d + 1) (subIncl W.B) _ = x
  rw [map_sub, ← hdiag, ← mvKappa_apply, hw]

theorem beta_comp_theta (n : ℕ) : W.beta n ≫ W.theta n = 0 := by
  ext x
  have hiota : mvIota W.A W.B (n + d) (mvδ W.A W.B W.cover (n + d) x) = 0 := by
    rw [← ConcreteCategory.comp_apply, mvδ_comp_mvIota]
    rfl
  have hA : HgrpMap (n + d) (mvInclLeft W.A W.B) (mvδ W.A W.B W.cover (n + d) x) = 0 := by
    rw [← bfst_mvIota, hiota, bfst_zero]
  have hB : HgrpMap (n + d) (mvInclRight W.A W.B) (mvδ W.A W.B W.cover (n + d) x) = 0 := by
    rw [← bsnd_mvIota, hiota, bsnd_zero]
  have hfst : bfst ((W.split n).hom (mvδ W.A W.B W.cover (n + d) x)) = 0 := by
    rw [← inclLeft_apply, hA]
  rw [inclRight_apply, hfst, map_zero, zero_add] at hB
  show W.theta n (W.beta n x) = 0
  rw [W.beta_apply]
  exact hB

/-- **Wang, exactness at `Hₙ(F)`:** `H_{n+d+1}(E) --β--> Hₙ(F) --θ--> H_{n+d}(B)`. -/
theorem wang_exact_beta_theta (n : ℕ) :
    (ShortComplex.mk (W.beta n) (W.theta n) (W.beta_comp_theta n)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro b hb
  have hhom : (W.split n).hom ((W.split n).inv (binr b)) = binr b := W.hom_inv_apply n _
  have hA : HgrpMap (n + d) (mvInclLeft W.A W.B) ((W.split n).inv (binr b)) = 0 := by
    rw [inclLeft_apply, hhom, bfst_binr]
  have hB : HgrpMap (n + d) (mvInclRight W.A W.B) ((W.split n).inv (binr b)) = 0 := by
    rw [inclRight_apply, hhom, bfst_binr, bsnd_binr, map_zero, zero_add]
    exact hb
  have hiota : mvIota W.A W.B (n + d) ((W.split n).inv (binr b)) = 0 :=
    bext_zero ((bfst_mvIota W (n + d) _).trans hA) ((bsnd_mvIota W (n + d) _).trans hB)
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1
    (mayerVietoris_exact_δ_iota W.A W.B W.cover (n + d)) _ hiota
  refine ⟨x, ?_⟩
  show W.beta n x = b
  rw [W.beta_apply, hx, hhom, bsnd_binr]

/-! ### The collapse used to compute `H_*(Ω Sᵐ)` -/

/-- If `H_{n+d}(E)` and `H_{n+d+1}(E)` vanish, the Wang map `θ : Hₙ(F) ⟶ H_{n+d}(B)` is an
isomorphism. This is what happens for the path fibration, whose total space is contractible. -/
theorem isIso_theta (n : ℕ) (h1 : IsZero (Hgrp (n + d + 1) E)) (h0 : IsZero (Hgrp (n + d) E)) :
    IsIso (W.theta n) := by
  have hβ : W.beta n = 0 := h1.eq_zero_of_src _
  have hα : W.alpha (n + d) = 0 := h0.eq_zero_of_tgt _
  have : Mono (W.theta n) := (W.wang_exact_beta_theta n).mono_g hβ
  have : Epi (W.theta n) := (W.wang_exact_theta_alpha n).epi_f hα
  exact isIso_of_mono_of_epi _

/-- The Wang isomorphism `Hₙ(F) ≅ H_{n+d}(B)` when the total space has vanishing homology in
degrees `n + d` and `n + d + 1`. -/
def thetaIso (n : ℕ) (h1 : IsZero (Hgrp (n + d + 1) E)) (h0 : IsZero (Hgrp (n + d) E)) :
    Hgrp n W.fibre ≅ Hgrp (n + d) (TopCat.of W.B) :=
  have := W.isIso_theta n h1 h0
  asIso (W.theta n)

/-! ### Low degrees -/

end WangDatum

/-- A Mayer–Vietoris collapse in the other direction: if the total space has vanishing homology in
degrees `k` and `k + 1`, and `A ∩ B → A` is an isomorphism on `H_k`, then `H_k(B)` vanishes. For a
fibration over `Sᵐ` this is what makes `H_k(F)` vanish for `0 < k < m - 1`. -/
theorem isZero_Hgrp_of_isIso_mvInclLeft {X : TopCat.{0}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) (k : ℕ) (h1 : IsZero (Hgrp (k + 1) X))
    (h0 : IsZero (Hgrp k X)) (hiso : IsIso (HgrpMap k (mvInclLeft A B))) :
    IsZero (Hgrp k (TopCat.of B)) := by
  have hδ : mvδ A B h k = 0 := h1.eq_zero_of_src _
  have hκ : mvKappa A B k = 0 := h0.eq_zero_of_tgt _
  have hm : Mono (mvIota A B k) := (mayerVietoris_exact_δ_iota A B h k).mono_g hδ
  have he : Epi (mvIota A B k) := (mayerVietoris_exact_iota_kappa A B h k).epi_f hκ
  have hsurj : Function.Surjective (mvIota A B k) :=
    (AddCommGrpCat.epi_iff_surjective _).1 he
  have hinj : Function.Injective (HgrpMap k (mvInclLeft A B)) :=
    (AddCommGrpCat.mono_iff_injective _).1 (isIso_iff_mono_and_epi _ |>.1 hiso).1
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext y
  obtain ⟨z, hz⟩ := hsurj (binr y)
  have hA : HgrpMap k (mvInclLeft A B) z = 0 := by
    rw [← bfst_lift_apply (HgrpMap k (mvInclLeft A B)) (HgrpMap k (mvInclRight A B)) z]
    show bfst (mvIota A B k z) = 0
    rw [hz, bfst_binr]
  have hz0 : z = 0 := hinj (by rw [hA, map_zero])
  have : (binr y : ↥(mvSum A B k)) = 0 := by rw [← hz, hz0, map_zero]
  have hy : y = 0 := by rw [← bsnd_binr (X := Hgrp k (TopCat.of A)) y, this, bsnd_zero]
  rw [hy]
  rfl

namespace WangDatum

variable (W : WangDatum E d)

/-! ### Restating the sequence through an identification of `H_*(B)` with `H_*(F)` -/

variable (isoB : ∀ n : ℕ, Hgrp n (TopCat.of W.B) ≅ Hgrp n W.fibre)

/-- The Wang map read as an endomorphism of `H_*(F)` raising degree by `d`. -/
def thetaF (n : ℕ) : Hgrp n W.fibre ⟶ Hgrp (n + d) W.fibre :=
  W.theta n ≫ (isoB (n + d)).hom

/-- The Wang map raises degree by `d` and is an isomorphism `Hₙ(F) ≅ H_{n+d}(F)` as soon as the
total space has vanishing homology in the two relevant degrees. -/
theorem isIso_thetaF (n : ℕ) (h1 : IsZero (Hgrp (n + d + 1) E)) (h0 : IsZero (Hgrp (n + d) E)) :
    IsIso (W.thetaF isoB n) :=
  have := W.isIso_theta n h1 h0
  IsIso.comp_isIso

/-- The Wang isomorphism `Hₙ(F) ≅ H_{n+d}(F)`. -/
def thetaFIso (n : ℕ) (h1 : IsZero (Hgrp (n + d + 1) E)) (h0 : IsZero (Hgrp (n + d) E)) :
    Hgrp n W.fibre ≅ Hgrp (n + d) W.fibre :=
  (W.thetaIso n h1 h0).trans (isoB (n + d))

end WangDatum

end Submission
