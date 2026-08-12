/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.Vanishing

/-!
# Vanishing of relative homology in a range of degrees

`Submission/Hurewicz/Vanishing.lean` deduces `H_*(X, A) = 0` in *all* degrees from a
`Submission.SimplicialCompression`, a coherent deformation of *all* the singular simplices of `X`
into `A`.  Several applications only have a deformation in a range of dimensions, and only need
the vanishing in a range of degrees.  This file provides that.

The relevant data is `Submission.SimplicialDeformation X A M`.  It differs from a
`SimplicialCompression` in two ways: the retraction `ρ` is a *self-map* of the singular simplices
of `X` rather than a map into those of `A`, and it is only required to land in `A` in dimensions
`≤ M`.  Everything else — the face compatibility of `ρ`, the homotopy operators `h` and their
five face axioms — is unchanged.

The point of making `ρ` a self-map is that the resulting chain homotopy `𝟙 ≃ ρ` is *global*, so
Mathlib's `Homotopy.homologyMap_eq` applies verbatim; the bound enters only at the very end,
through the observation that the descended endomorphism of the relative complex vanishes in degree
`k` as soon as `ρ` lands in `A` in dimension `k`, and that a chain map which is zero in degree `k`
induces zero on `H_k`.

## Main definitions and results

* `Submission.homologyMap_eq_zero_of_f_eq_zero` — a chain map vanishing in degree `n` induces
  zero on `H_n`;
* `Submission.SimplicialDeformation X A M` — the bounded deformation data;
* `Submission.SimplicialDeformation.isZero_HrelSet` — `H_k(X, A) = 0` for `k ≤ M`;
* `Submission.SimplicialDeformation.isIso_relIota` — `H_k(A) → H_k(X)` is an isomorphism for
  `k + 1 ≤ M`, and an epimorphism for `k = M`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not, and without
-- it `rw`/`simp` fail on goals that are not type-correct at `instances` transparency.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

/-- A chain map which vanishes in degree `n` induces the zero map on homology in degree `n`. -/
theorem homologyMap_eq_zero_of_f_eq_zero {K L : ChainComplex AddCommGrpCat.{0} ℕ}
    (φ : K ⟶ L) (n : ℕ) (h : φ.f n = 0) : HomologicalComplex.homologyMap φ n = 0 := by
  have hc : HomologicalComplex.cyclesMap φ n = 0 := by
    have hi := HomologicalComplex.cyclesMap_i φ n
    rw [h, comp_zero] at hi
    exact (cancel_mono (L.iCycles n)).1 (by rw [hi, zero_comp])
  have hn := HomologicalComplex.homologyπ_naturality φ n
  rw [hc, zero_comp] at hn
  exact (cancel_epi (K.homologyπ n)).1 (by rw [hn, comp_zero])

variable {X : TopCat.{0}} {A : Set X}

/-! ### Bounded deformation data -/

/-- Coherent data deforming the singular simplices of `X` towards `A`, compressing those of
dimension at most `M` into `A`.

`ρ` is a face-compatible self-map of the singular simplices of `X` which fixes the simplices
already lying in `A` and, in dimensions `≤ M`, takes its values in `A`; `h` is face-only homotopy
data (in the sense of `Submission.FaceHomotopy`) exhibiting the identity as chain homotopic to
`ρ`, again preserving the simplices lying in `A`. -/
structure SimplicialDeformation (X : TopCat.{0}) (A : Set X) (M : ℕ) where
  /-- The deformation on `n`-simplices. -/
  ρ (n : ℕ) : Sng X _⦋n⦌ → Sng X _⦋n⦌
  /-- The deformation commutes with the face maps. -/
  ρ_δ {n : ℕ} (i : Fin (n + 2)) (σ : Sng X _⦋n + 1⦌) :
    ρ n ((Sng X).δ i σ) = (Sng X).δ i (ρ (n + 1) σ)
  /-- The deformation fixes the simplices which already lie in `A`. -/
  ρ_fix {n : ℕ} (τ : Sng (TopCat.of A) _⦋n⦌) :
    ρ n ((sngIncl A).app _ τ) = (sngIncl A).app _ τ
  /-- In dimensions at most `M`, the deformation takes its values in `A`. -/
  ρ_mem {n : ℕ} (hn : n ≤ M) (σ : Sng X _⦋n⦌) : ∃ τ, (sngIncl A).app _ τ = ρ n σ
  /-- The homotopy operators. -/
  h {n : ℕ} (i : Fin (n + 1)) : Sng X _⦋n⦌ → Sng X _⦋n + 1⦌
  /-- The homotopy operators preserve the simplices lying in `A`. -/
  h_incl {n : ℕ} (i : Fin (n + 1)) (τ : Sng (TopCat.of A) _⦋n⦌) :
    ∃ υ, (sngIncl A).app _ υ = h i ((sngIncl A).app _ τ)
  /-- The zeroth face of the zeroth operator is the identity. -/
  h_zero_δ_zero {n : ℕ} (σ : Sng X _⦋n⦌) : (Sng X).δ 0 (h 0 σ) = σ
  /-- The last face of the last operator is the deformation. -/
  h_last_δ_last {n : ℕ} (σ : Sng X _⦋n⦌) :
    (Sng X).δ (Fin.last (n + 1)) (h (Fin.last n) σ) = ρ n σ
  /-- Compatibility with the faces, first case. -/
  h_succ_δ_castSucc_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc)
    (σ : Sng X _⦋n + 1⦌) : (Sng X).δ i.castSucc (h j.succ σ) = h j ((Sng X).δ i σ)
  /-- Compatibility with the faces, second case. -/
  h_succ_δ_castSucc_succ {n : ℕ} (j : Fin (n + 1)) (σ : Sng X _⦋n + 1⦌) :
    (Sng X).δ j.castSucc.succ (h j.succ σ) = (Sng X).δ j.castSucc.succ (h j.castSucc σ)
  /-- Compatibility with the faces, third case. -/
  h_castSucc_δ_succ_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i)
    (σ : Sng X _⦋n + 1⦌) : (Sng X).δ i.succ (h j.castSucc σ) = h j ((Sng X).δ i σ)

namespace SimplicialDeformation

variable {M : ℕ} (c : SimplicialDeformation X A M)

/-- The chain endomorphism of `C_*(X)` determined by the deformation data. -/
def selfMap : Csing X ⟶ Csing X :=
  faceChainMap c.ρ (fun _ i σ => c.ρ_δ i σ)

/-- The deformation fixes the singular chains of the subspace. -/
theorem incl_comp_selfMap :
    CsingMap (subIncl A) ≫ c.selfMap = 𝟙 (Csing (TopCat.of A)) ≫ CsingMap (subIncl A) := by
  rw [Category.id_comp]
  ext n : 1
  rw [HomologicalComplex.comp_f, CsingMap_f_eq_simpMap, selfMap, faceChainMap_f, simpMap_comp]
  exact congrArg simpMap (funext fun τ => c.ρ_fix τ)

/-- The face-only homotopy data on singular chains determined by the deformation data. -/
def faceHomotopy : FaceHomotopy (sngFace (Sng X)) (sngFace (Sng X)) c.selfMap (𝟙 (Csing X)) where
  h i := simpMap (c.h i)
  h_zero_comp_δ_zero n := by
    rw [sngFace, simpMap_comp, HomologicalComplex.id_f]
    exact (congrArg simpMap (funext fun σ => c.h_zero_δ_zero σ)).trans simpMap_id
  h_last_comp_δ_last n := by
    rw [sngFace, simpMap_comp, selfMap, faceChainMap_f]
    exact congrArg simpMap (funext fun σ => c.h_last_δ_last σ)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    rw [sngFace, simpMap_comp, simpMap_comp]
    exact congrArg simpMap (funext fun σ => c.h_succ_δ_castSucc_of_lt i j hij σ)
  h_succ_comp_δ_castSucc_succ j := by
    rw [sngFace, simpMap_comp, simpMap_comp]
    exact congrArg simpMap (funext fun σ => c.h_succ_δ_castSucc_succ j σ)
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    rw [sngFace, simpMap_comp, simpMap_comp]
    exact congrArg simpMap (funext fun σ => c.h_castSucc_δ_succ_of_lt i j hji σ)

/-- The homotopy operators carry singular chains of `A` into singular chains of `A`, hence die in
the relative complex. -/
theorem incl_comp_hom (p q : ℕ) :
    (CsingMap (subIncl A)).f p ≫ (c.faceHomotopy.toChainHomotopy).hom p q ≫
      (relProj (subIncl A)).f q = 0 := by
  show (CsingMap (subIncl A)).f p ≫ FaceHomotopy.hom c.faceHomotopy p q ≫ _ = 0
  by_cases hpq : p + 1 = q
  · subst hpq
    have key : ∀ k : Fin (p + 1), (CsingMap (subIncl A)).f p ≫ simpMap (c.h k) ≫
        (relProj (subIncl A)).f (p + 1) = 0 := by
      intro k
      have hchoice : (fun τ : Sng (TopCat.of A) _⦋p⦌ => c.h k ((sngIncl A).app _ τ)) =
          fun τ => (sngIncl A).app _ (Classical.choose (c.h_incl k τ)) :=
        funext fun τ => (Classical.choose_spec (c.h_incl k τ)).symm
      rw [← Category.assoc, CsingMap_f_eq_simpMap, simpMap_comp, hchoice,
        ← simpMap_comp (fun τ => Classical.choose (c.h_incl k τ))
          (fun υ : Sng (TopCat.of A) _⦋p + 1⦌ => (sngIncl A).app _ υ),
        ← CsingMap_f_eq_simpMap, Category.assoc, CsingMap_comp_relProj_f, comp_zero]
    have gen : ∀ (a : (Csing (TopCat.of A)).X p ⟶ (Csing X).X p)
        (φ : Fin (p + 1) → ((Csing X).X p ⟶ (Csing X).X (p + 1)))
        (b : (Csing X).X (p + 1) ⟶ (relComplex (subIncl A)).X (p + 1)),
        (∀ k, a ≫ φ k ≫ b = 0) →
          a ≫ (-∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • φ k) ≫ b = 0 := by
      intro a φ b hk
      rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_eq_zero, Preadditive.sum_comp,
        Preadditive.comp_sum]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, hk k, smul_zero]
    rw [FaceHomotopy.hom_eq]
    exact gen _ _ _ key
  · rw [FaceHomotopy.hom_eq_zero _ _ _ hpq]
    simp

/-- In dimensions at most `M` the deformation lands in `A`, hence dies in the relative complex. -/
theorem selfMap_comp_relProj (n : ℕ) (hn : n ≤ M) :
    c.selfMap.f n ≫ (relProj (subIncl A)).f n = 0 := by
  have hchoice : c.ρ n = fun σ => (sngIncl A).app _ (Classical.choose (c.ρ_mem hn σ)) :=
    funext fun σ => (Classical.choose_spec (c.ρ_mem hn σ)).symm
  rw [selfMap, faceChainMap_f, hchoice,
    ← simpMap_comp (fun σ => Classical.choose (c.ρ_mem hn σ))
      (fun τ : Sng (TopCat.of A) _⦋n⦌ => (sngIncl A).app _ τ),
    ← CsingMap_f_eq_simpMap, Category.assoc, CsingMap_comp_relProj_f, comp_zero]

include c in
/-- **The relative singular homology of `(X, A)` vanishes in degrees at most `M`** when the
singular simplices of `X` of dimension at most `M` can be coherently deformed into `A`. -/
theorem isZero_HrelSet (k : ℕ) (hk : k ≤ M) : IsZero (HrelSet k A) := by
  have hw2 : CsingMap (subIncl A) ≫ 𝟙 (Csing X) =
      𝟙 (Csing (TopCat.of A)) ≫ CsingMap (subIncl A) := by
    rw [Category.comp_id, Category.id_comp]
  have hepi : Epi (cokernel.π (CsingMap (subIncl A))) := coequalizer.π_epi
  have ho : cokernel.map (CsingMap (subIncl A)) (CsingMap (subIncl A))
      (𝟙 (Csing (TopCat.of A))) (𝟙 (Csing X)) hw2 = 𝟙 _ := by
    apply hepi.left_cancellation
    rw [π_cokernel_map, Category.id_comp, Category.comp_id]
  have hz : HomologicalComplex.homologyMap (cokernel.map (CsingMap (subIncl A))
      (CsingMap (subIncl A)) (𝟙 (Csing (TopCat.of A))) c.selfMap c.incl_comp_selfMap) k = 0 := by
    refine homologyMap_eq_zero_of_f_eq_zero _ k ?_
    have hepi' : Epi ((cokernel.π (CsingMap (subIncl A))).f k) := inferInstance
    apply hepi'.left_cancellation
    rw [π_cokernel_map_f, comp_zero]
    exact c.selfMap_comp_relProj k hk
  have key := (descHomotopy (CsingMap (subIncl A)) (CsingMap (subIncl A)) c.incl_comp_selfMap hw2
    c.faceHomotopy.toChainHomotopy c.incl_comp_hom).homologyMap_eq k
  rw [hz, ho, HomologicalComplex.homologyMap_id] at key
  exact (IsZero.iff_id_eq_zero _).2 key.symm

include c in
/-- **The inclusion `A ↪ X` induces isomorphisms on singular homology in degrees `k` with
`k + 1 ≤ M`.** -/
theorem isIso_relIota (k : ℕ) (hk : k + 1 ≤ M) : IsIso (HgrpMap k (subIncl A)) :=
  have : Mono (relIota k (subIncl A)) :=
    (pair_exact_δ_iota k (subIncl A)).mono_g
      ((c.isZero_HrelSet (k + 1) hk).eq_zero_of_src _)
  have : Epi (relIota k (subIncl A)) :=
    (pair_exact_iota_j k (subIncl A)).epi_f
      ((c.isZero_HrelSet k (by omega)).eq_zero_of_tgt _)
  isIso_of_mono_of_epi _

include c in
/-- **The inclusion `A ↪ X` induces an epimorphism on singular homology in degree `M`.** -/
theorem epi_relIota (k : ℕ) (hk : k ≤ M) : Epi (HgrpMap k (subIncl A)) :=
  (pair_exact_iota_j k (subIncl A)).epi_f ((c.isZero_HrelSet k hk).eq_zero_of_tgt _)

end SimplicialDeformation

end Submission
