/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.DualShortExact
import Submission.Cohomology.DualBridge

/-!
# Evaluation and connecting homomorphisms

For a short exact sequence of chain complexes, the homological connecting map and the connecting
map of the reversed dual sequence are adjoint under evaluation.  At the chain level, both sides
are the same expression: extend the cocycle to the middle complex and evaluate it on a lift of the
cycle before taking its boundary.

## Main results

* `shortExact_delta_homologyMk` computes a connecting homomorphism on chosen representatives.
* `ev_delta_adjoint_chain` proves that the homological and dual connecting maps are adjoint.
-/

open CategoryTheory Limits Opposite ComposableArrows Abelian

noncomputable section

namespace Submission

variable {ι : Type*} {c : ComplexShape ι}

@[simp]
theorem intHom_comp {A B : AddCommGrpCat.{0}} (x : A) (f : A ⟶ B) :
    intHom x ≫ f = intHom (f x) := by
  apply intHom_ext
  rw [ConcreteCategory.comp_apply, intHom_one, intHom_one]

@[simp]
theorem intHom_zero (A : AddCommGrpCat.{0}) : intHom (0 : A) = 0 := by
  apply intHom_ext
  simpa using intHom_one (0 : A)

/-- Evaluating the morphism from `ℤ` that represents a cycle recovers its `homologyMk` class. -/
theorem liftCycles_intHom_homologyπ_one
    (K : HomologicalComplex AddCommGrpCat.{0} c) (i j : ι) (hij : c.next i = j)
    (x : K.X i) (hx : K.d i j x = 0) :
    (K.liftCycles (intHom x) j hij (by simpa using congrArg intHom hx) ≫
      K.homologyπ i) (1 : ℤ) = homologyMk x (by rw [hij]; exact hx) := by
  subst j
  rw [ConcreteCategory.comp_apply, homologyMk_eq_homologyπ]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles i)).1 inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i, intHom_one]
  exact (ShortComplex.abCyclesIso_inv_apply_iCycles (K.sc i) ⟨x, hx⟩).symm

/-- The connecting homomorphism sends the class of `x3` to the class of `x1` whenever `x2`
lifts `x3` and the differential of `x2` is the image of `x1`. -/
theorem shortExact_delta_homologyMk
    {S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (x3 : S.X₃.X i) (hx3 : S.X₃.d i j x3 = 0)
    (x2 : S.X₂.X i) (hx2 : S.g.f i x2 = x3)
    (x1 : S.X₁.X j) (hx1 : S.f.f j x1 = S.X₂.d i j x2) :
    hS.δ i j hij (homologyMk x3 (by rw [c.next_eq' hij]; exact hx3)) =
      homologyMk x1 (by
        apply (AddCommGrpCat.mono_iff_injective (S.f.f (c.next j))).1
          (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
            (c.next j)).mono_f)
        rw [← ConcreteCategory.comp_apply, ← S.f.comm, ConcreteCategory.comp_apply, hx1,
          ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
        simp) := by
  let hx1' : S.X₁.d j (c.next j) x1 = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (S.f.f (c.next j))).1
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
        (c.next j)).mono_f)
    rw [← ConcreteCategory.comp_apply, ← S.f.comm, ConcreteCategory.comp_apply, hx1,
      ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
    simp
  have h := hS.δ_eq i j hij (intHom x3)
    (by rw [intHom_comp, hx3, intHom_zero]) (intHom x2)
    (by rw [intHom_comp, hx2]) (intHom x1)
    (by rw [intHom_comp, intHom_comp, hx1]) (c.next j) rfl
  have h1 := ConcreteCategory.congr_hom h (1 : ℤ)
  simp only [ConcreteCategory.comp_apply] at h1
  have hl := liftCycles_intHom_homologyπ_one S.X₃ i j (c.next_eq' hij) x3 hx3
  have hr := liftCycles_intHom_homologyπ_one S.X₁ j (c.next j) rfl x1 hx1'
  rw [ConcreteCategory.comp_apply] at hl hr
  rw [hl, hr] at h1
  exact h1

set_option backward.isDefEq.respectTransparency false in
/-- For a short exact sequence of chain complexes and its reversed dual sequence, the two
connecting homomorphisms are adjoint under the evaluation pairing. -/
theorem ev_delta_adjoint_chain
    (S : ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ))
    (G : AddCommGrpCat.{0}) (hS : S.ShortExact)
    (hD : (homDualShortComplex S G).ShortExact) (n : ℕ)
    (Φ : (homDualShortComplex S G).X₃.homology n) (z : S.X₃.homology (n + 1)) :
    ev S.X₃ G (n + 1) (hD.δ n (n + 1) (by rfl) Φ) z =
      ev S.X₁ G n Φ (hS.δ (n + 1) n (by rfl) z) := by
  dsimp only [homDualShortComplex] at hD Φ ⊢
  let T := homDualShortComplex S G
  let hc : (ComplexShape.down ℕ).symm.Rel n (n + 1) := by rfl
  let hh : (ComplexShape.down ℕ).Rel (n + 1) n := by rfl
  change ev S.X₃ G (n + 1) (hD.δ n (n + 1) hc Φ) z =
    ev S.X₁ G n Φ (hS.δ (n + 1) n hh z)
  obtain ⟨φ, hφ, rfl⟩ := homologyMk_surjective Φ
  obtain ⟨x, hx, rfl⟩ := homologyMk_surjective z
  have hφ' : (homDual S.X₁ G).d n (n + 1) φ = 0 := by
    have hn : (ComplexShape.down ℕ).symm.next n = n + 1 := ComplexShape.next_eq' _ rfl
    rw [← hn]
    exact hφ
  have hx' : S.X₃.d (n + 1) n x = 0 := by
    have hn : (ComplexShape.down ℕ).next (n + 1) = n := ChainComplex.next_nat_succ n
    rw [hn] at hx
    exact hx
  have hTn := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hD n
  have hTnp := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hD (n + 1)
  obtain ⟨φ2, hφ2⟩ : ∃ φ2 : T.X₂.X n, T.g.f n φ2 = φ :=
    ((AddCommGrpCat.epi_iff_surjective (T.g.f n)).1 hTn.epi_g) φ
  have hφ2cycle : T.g.f (n + 1) (T.X₂.d n (n + 1) φ2) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← T.g.comm, ConcreteCategory.comp_apply, hφ2]
    exact hφ'
  obtain ⟨φ3, hφ3⟩ : ∃ φ3 : T.X₁.X (n + 1),
      T.f.f (n + 1) φ3 = T.X₂.d n (n + 1) φ2 :=
    (T.map (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ).symm
      (n + 1))).ab_exact_iff.mp hTnp.exact _ hφ2cycle
  have hSnp := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS (n + 1)
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  obtain ⟨x2, hx2⟩ : ∃ x2 : S.X₂.X (n + 1), S.g.f (n + 1) x2 = x :=
    ((AddCommGrpCat.epi_iff_surjective (S.g.f (n + 1))).1 hSnp.epi_g) x
  have hx2cycle : S.g.f n (S.X₂.d (n + 1) n x2) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← S.g.comm, ConcreteCategory.comp_apply, hx2]
    exact hx'
  obtain ⟨x1, hx1⟩ : ∃ x1 : S.X₁.X n,
      S.f.f n x1 = S.X₂.d (n + 1) n x2 :=
    (S.map (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n)).ab_exact_iff.mp
      hSn.exact _ hx2cycle
  have hcoh := shortExact_delta_homologyMk hD n (n + 1) hc
    φ hφ' φ2 hφ2 φ3 hφ3
  have hhom := shortExact_delta_homologyMk hS (n + 1) n hh
    x hx' x2 hx2 x1 hx1
  dsimp only [homDualShortComplex] at hcoh
  rw [hcoh, hhom, ev_homologyMk, ev_homologyMk,
    evCocycle_homologyMk, evCocycle_homologyMk]
  change (S.X₁.X n ⟶ G) at φ
  change (S.X₂.X n ⟶ G) at φ2
  change (S.X₃.X (n + 1) ⟶ G) at φ3
  change S.f.f n ≫ φ2 = φ at hφ2
  change S.g.f (n + 1) ≫ φ3 = S.X₂.d (n + 1) n ≫ φ2 at hφ3
  change φ3 x = φ x1
  calc
    φ3 x = φ3 (S.g.f (n + 1) x2) := congrArg φ3 hx2.symm
    _ = (S.g.f (n + 1) ≫ φ3) x2 := rfl
    _ = (S.X₂.d (n + 1) n ≫ φ2) x2 := congrArg (fun q => q x2) hφ3
    _ = φ2 (S.X₂.d (n + 1) n x2) := rfl
    _ = φ2 (S.f.f n x1) := congrArg φ2 hx1.symm
    _ = (S.f.f n ≫ φ2) x1 := rfl
    _ = φ x1 := congrArg (fun q => q x1) hφ2

end Submission
