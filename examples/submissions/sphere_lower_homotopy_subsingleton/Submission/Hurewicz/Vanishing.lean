/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.PairHomotopy
import Submission.Homology.SimplicialSplitting
import Submission.Homology.LesTools
import Submission.Hurewicz.FaceHomotopy

/-!
# Vanishing of relative singular homology from a compression of singular simplices

Let `A` be a subspace of `X`.  Suppose that every singular simplex of `X` can be deformed into
`A`, coherently with the face maps.  Then the relative singular homology `H_*(X, A)` vanishes and
`H_*(A) → H_*(X)` is an isomorphism.

This file contains the *algebraic* half of that statement.  The relevant coherent family is
packaged as `Submission.SimplicialCompression`: a face-compatible retraction `ρ` of the singular
simplices of `X` onto those of `A`, together with face-only homotopy data `h` (in the sense of
`Submission.FaceHomotopy`) exhibiting `ρ` as chain homotopic to the identity, both preserving the
simplices which already lie in `A`.

The geometric half — producing a `SimplicialCompression` out of the vanishing of the relative
homotopy groups — is the content of `Submission/Hurewicz/VanishingSorries.lean`.

## Main definitions and results

* `Submission.simpMap` — the map of chain groups induced by an arbitrary map of simplices;
* `Submission.sngFace` — the face structure of a simplicial chain complex;
* `Submission.SimplicialCompression X A` — the coherent compression data;
* `Submission.SimplicialCompression.isZero_HrelSet` — `H_k(X, A) = 0` for all `k`;
* `Submission.SimplicialCompression.isIso_relIota` — `H_k(A) → H_k(X)` is an isomorphism.
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

/-! ### Maps of chain groups prescribed on simplices -/

variable {S T U : SSet.{0}}

/-- The map of chain groups induced by an arbitrary map of simplices (not required to be
compatible with any simplicial operator). -/
def simpMap {n m : ℕ} (φ : S _⦋n⦌ → T _⦋m⦌) : (CsingSSet S).X n ⟶ (CsingSSet T).X m :=
  ccDesc fun x => T.ιChainComplex (φ x)

@[reassoc (attr := simp)]
theorem ι_simpMap {n m : ℕ} (φ : S _⦋n⦌ → T _⦋m⦌) (x : S _⦋n⦌) :
    S.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫ simpMap φ = T.ιChainComplex (φ x) :=
  ι_ccDesc _ _

@[simp]
theorem simpMap_id {n : ℕ} : simpMap (fun x : S _⦋n⦌ => x) = 𝟙 _ :=
  SSet.chainComplex_hom_ext fun x => (ι_simpMap _ x).trans (Category.comp_id _).symm

theorem simpMap_comp {n m k : ℕ} (φ : S _⦋n⦌ → T _⦋m⦌) (ψ : T _⦋m⦌ → U _⦋k⦌) :
    simpMap φ ≫ simpMap ψ = simpMap (fun x => ψ (φ x)) :=
  SSet.chainComplex_hom_ext fun x => by
    rw [← Category.assoc, ι_simpMap, ι_simpMap, ι_simpMap]

/-- The face structure of the chain complex of a simplicial set. -/
def sngFace (S : SSet.{0}) : FaceStructure (CsingSSet S) where
  δ n i := simpMap (fun x : S _⦋n + 1⦌ => S.δ i x)
  d_eq n := SSet.chainComplex_hom_ext fun x => by
    rw [SSet.ιChainComplex_d, Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Preadditive.comp_zsmul, ι_simpMap]

/-- A face-compatible family of maps of simplices induces a map of chain complexes. -/
def faceChainMap (φ : ∀ n, S _⦋n⦌ → T _⦋n⦌)
    (hφ : ∀ (n : ℕ) (i : Fin (n + 2)) (x : S _⦋n + 1⦌), φ n (S.δ i x) = T.δ i (φ (n + 1) x)) :
    CsingSSet S ⟶ CsingSSet T where
  f n := simpMap (φ n)
  comm' i j hij := by
    obtain rfl : j + 1 = i := by simpa using hij
    refine SSet.chainComplex_hom_ext fun x => ?_
    rw [← Category.assoc, ι_simpMap, SSet.ιChainComplex_d, ← Category.assoc,
      SSet.ιChainComplex_d, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun k _ => by rw [Preadditive.zsmul_comp, ι_simpMap, hφ]

@[simp]
theorem faceChainMap_f (φ : ∀ n, S _⦋n⦌ → T _⦋n⦌) (hφ) (n : ℕ) :
    (faceChainMap φ hφ).f n = simpMap (φ n) := rfl

/-! ### Singular simplices of a space -/

/-- The singular simplicial set of a space. -/
abbrev Sng (X : TopCat.{0}) : SSet.{0} := TopCat.toSSet.obj X

/-- The inclusion of the singular simplicial set of a subspace. -/
abbrev sngIncl {X : TopCat.{0}} (A : Set X) : Sng (TopCat.of A) ⟶ Sng X :=
  TopCat.toSSet.map (subIncl A)

/-- The map of singular chains induced by a continuous map, described on simplices. -/
theorem CsingMap_f_eq_simpMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (CsingMap f).f n = simpMap (fun x : Sng X _⦋n⦌ => (TopCat.toSSet.map f).app _ x) :=
  SSet.chainComplex_hom_ext fun x => by
    rw [ι_simpMap]
    exact SSet.ι_chainComplexMap_f _ _ _ _ x

variable {X : TopCat.{0}} {A : Set X}

/-- Singular chains of the subspace die in the relative complex. -/
theorem CsingMap_comp_relProj_f (n : ℕ) :
    (CsingMap (subIncl A)).f n ≫ (relProj (subIncl A)).f n = 0 := by
  have h0 : CsingMap (subIncl A) ≫ relProj (subIncl A) = 0 := cokernel.condition _
  rw [← HomologicalComplex.comp_f, h0, HomologicalComplex.zero_f]

/-! ### Compression data -/

/-- Coherent data compressing the singular simplices of `X` into a subspace `A`.

`ρ` is a face-compatible retraction of the singular simplices of `X` onto those of `A`, and `h`
is face-only homotopy data (in the sense of `Submission.FaceHomotopy`) exhibiting the identity as
chain homotopic to `ρ`.  Both are required to leave the simplices lying in `A` where they are. -/
structure SimplicialCompression (X : TopCat.{0}) (A : Set X) where
  /-- The retraction on `n`-simplices. -/
  ρ (n : ℕ) : Sng X _⦋n⦌ → Sng (TopCat.of A) _⦋n⦌
  /-- The retraction commutes with the face maps. -/
  ρ_δ {n : ℕ} (i : Fin (n + 2)) (σ : Sng X _⦋n + 1⦌) :
    ρ n ((Sng X).δ i σ) = (Sng (TopCat.of A)).δ i (ρ (n + 1) σ)
  /-- The retraction fixes the simplices which already lie in `A`. -/
  ρ_incl {n : ℕ} (τ : Sng (TopCat.of A) _⦋n⦌) : ρ n ((sngIncl A).app _ τ) = τ
  /-- The homotopy operators. -/
  h {n : ℕ} (i : Fin (n + 1)) : Sng X _⦋n⦌ → Sng X _⦋n + 1⦌
  /-- The homotopy operators preserve the simplices lying in `A`. -/
  h_incl {n : ℕ} (i : Fin (n + 1)) (τ : Sng (TopCat.of A) _⦋n⦌) :
    ∃ υ, (sngIncl A).app _ υ = h i ((sngIncl A).app _ τ)
  /-- The zeroth face of the zeroth operator is the identity. -/
  h_zero_δ_zero {n : ℕ} (σ : Sng X _⦋n⦌) : (Sng X).δ 0 (h 0 σ) = σ
  /-- The last face of the last operator is the retraction. -/
  h_last_δ_last {n : ℕ} (σ : Sng X _⦋n⦌) :
    (Sng X).δ (Fin.last (n + 1)) (h (Fin.last n) σ) = (sngIncl A).app _ (ρ n σ)
  /-- Compatibility with the faces, first case. -/
  h_succ_δ_castSucc_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc)
    (σ : Sng X _⦋n + 1⦌) : (Sng X).δ i.castSucc (h j.succ σ) = h j ((Sng X).δ i σ)
  /-- Compatibility with the faces, second case. -/
  h_succ_δ_castSucc_succ {n : ℕ} (j : Fin (n + 1)) (σ : Sng X _⦋n + 1⦌) :
    (Sng X).δ j.castSucc.succ (h j.succ σ) = (Sng X).δ j.castSucc.succ (h j.castSucc σ)
  /-- Compatibility with the faces, third case. -/
  h_castSucc_δ_succ_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i)
    (σ : Sng X _⦋n + 1⦌) : (Sng X).δ i.succ (h j.castSucc σ) = h j ((Sng X).δ i σ)

namespace SimplicialCompression

variable (c : SimplicialCompression X A)

/-- The chain retraction `C_*(X) ⟶ C_*(A)` determined by the compression data. -/
def retraction : Csing X ⟶ Csing (TopCat.of A) :=
  faceChainMap c.ρ (fun _ i σ => c.ρ_δ i σ)

/-- The inclusion of singular chains of the subspace is a section of the retraction. -/
theorem incl_comp_retraction : CsingMap (subIncl A) ≫ c.retraction = 𝟙 (Csing (TopCat.of A)) := by
  ext n : 1
  rw [HomologicalComplex.comp_f, CsingMap_f_eq_simpMap, retraction, faceChainMap_f, simpMap_comp,
    HomologicalComplex.id_f]
  exact (congrArg simpMap (funext fun τ => c.ρ_incl τ)).trans simpMap_id

/-- The face-only homotopy data on singular chains determined by the compression data. -/
def faceHomotopy : FaceHomotopy (sngFace (Sng X)) (sngFace (Sng X))
    (c.retraction ≫ CsingMap (subIncl A)) (𝟙 (Csing X)) where
  h i := simpMap (c.h i)
  h_zero_comp_δ_zero n := by
    rw [sngFace, simpMap_comp, HomologicalComplex.id_f]
    exact (congrArg simpMap (funext fun σ => c.h_zero_δ_zero σ)).trans simpMap_id
  h_last_comp_δ_last n := by
    rw [sngFace, simpMap_comp, HomologicalComplex.comp_f, retraction, faceChainMap_f,
      CsingMap_f_eq_simpMap, simpMap_comp]
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

include c in
/-- **The relative singular homology of `(X, A)` vanishes** when the singular simplices of `X`
can be coherently compressed into `A`. -/
theorem isZero_HrelSet (k : ℕ) : IsZero (HrelSet k A) :=
  isZero_Hrel_of_chainDeformation (subIncl A) c.retraction c.incl_comp_retraction
    c.faceHomotopy.toChainHomotopy c.incl_comp_hom k

include c in
/-- **The inclusion `A ↪ X` induces isomorphisms on singular homology** when the singular
simplices of `X` can be coherently compressed into `A`. -/
theorem isIso_relIota (k : ℕ) : IsIso (HgrpMap k (subIncl A)) :=
  have : Mono (relIota k (subIncl A)) :=
    (pair_exact_δ_iota k (subIncl A)).mono_g ((c.isZero_HrelSet (k + 1)).eq_zero_of_src _)
  have : Epi (relIota k (subIncl A)) :=
    (pair_exact_iota_j k (subIncl A)).epi_f ((c.isZero_HrelSet k).eq_zero_of_tgt _)
  isIso_of_mono_of_epi _

end SimplicialCompression

end Submission
