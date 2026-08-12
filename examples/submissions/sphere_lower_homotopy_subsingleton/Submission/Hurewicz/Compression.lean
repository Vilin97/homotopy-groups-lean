/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.Tower
import Submission.Hurewicz.Deformation

/-!
# The coherent compression of singular simplices

A tower of `Submission.Step`s attaches to every continuous map `f : |Δ^j| → X` a homotopy
`H f : |Δ^j| × I → X` which starts at `f`, is compatible with the face inclusions and is constant
on the maps that already take their values in `A`; when the level is *compressing* the homotopy
also ends inside `A`.  This file turns such a tower into compression data: the retraction is the
endpoint of the homotopy and the homotopy operators are obtained by precomposing with the prism
maps of `Submission/Hurewicz/Prism.lean`.

Two packagings are produced.  If every level compresses one gets a
`Submission.SimplicialCompression`, hence the vanishing of `H_*(X, A)` in all degrees; if only the
levels up to `M` compress one gets a `Submission.SimplicialDeformation X A M`, hence the vanishing
of `H_k(X, A)` for `k ≤ M`.

## Main definitions and results

* `Submission.compHom` — the homotopy attached to a singular simplex;
* `Submission.defRho`, `Submission.compRho`, `Submission.compH` — the deformation, the retraction
  and the homotopy operators;
* `Submission.deformation` — the resulting `SimplicialDeformation X A M`;
* `Submission.compression` — the resulting `SimplicialCompression X A`.
-/

open CategoryTheory Simplicial Opposite
open scoped Topology unitInterval

noncomputable section

namespace Submission

variable {X : TopCat.{0}} {A : Set X}

/-! ### The dictionary between singular simplices and maps out of the standard simplex -/

/-- Two singular simplices agree as soon as the corresponding maps do. -/
theorem sng_ext {Y : TopCat.{0}} {m : ℕ} {s t : Sng Y _⦋m⦌}
    (h : ∀ y, sngEquiv Y m s y = sngEquiv Y m t y) : s = t :=
  (sngEquiv Y m).injective (ContinuousMap.ext h)

/-- Taking the `i`-th face of a singular simplex is restricting along the `i`-th face
inclusion. -/
theorem apply_δ {Y : TopCat.{0}} {m : ℕ} (i : Fin (m + 2)) (s : Sng Y _⦋m + 1⦌)
    (y : stdSimplex ℝ (Fin (m + 1))) :
    sngEquiv Y m ((Sng Y).δ i s) y = sngEquiv Y (m + 1) s (faceMap i y) := by
  rw [sngEquiv_δ]
  rfl

/-- A singular simplex of the subspace, viewed in the total space. -/
theorem sngEquiv_incl {m : ℕ} (τ : Sng (TopCat.of A) _⦋m⦌) (y : stdSimplex ℝ (Fin (m + 1))) :
    sngEquiv X m ((sngIncl A).app _ τ) y = ((sngEquiv (TopCat.of A) m τ) y : X) := rfl

/-! ### The compression data attached to a tower -/

variable (S : ∀ j, Step A j) (hS : ∀ j, IsNext (S j) (S (j + 1)))

/-- The compressing homotopy attached to a singular simplex. -/
def compHom (n : ℕ) (s : Sng X _⦋n⦌) : C(stdSimplex ℝ (Fin (n + 1)) × I, X) :=
  (S n).H (sngEquiv X n s)

theorem compHom_zero (n : ℕ) (s : Sng X _⦋n⦌) (y : stdSimplex ℝ (Fin (n + 1))) :
    compHom S n s (y, 0) = sngEquiv X n s y :=
  (S n).start _ y

theorem compHom_mem {n : ℕ} (hc : (S n).Compresses) (s : Sng X _⦋n⦌)
    (y : stdSimplex ℝ (Fin (n + 1))) : compHom S n s (y, 1) ∈ A :=
  hc _ y

include hS in
/-- The homotopies of the faces of a simplex are the restrictions of its own homotopy. -/
theorem compHom_δ (n : ℕ) (i : Fin (n + 2)) (s : Sng X _⦋n + 1⦌)
    (y : stdSimplex ℝ (Fin (n + 1))) (t : I) :
    compHom S (n + 1) s (faceMap i y, t) = compHom S n ((Sng X).δ i s) (y, t) := by
  rw [compHom, compHom, sngEquiv_δ]
  exact hS n (sngEquiv X (n + 1) s) i y t

/-- The homotopy attached to a simplex of the subspace is constant. -/
theorem compHom_incl (n : ℕ) (τ : Sng (TopCat.of A) _⦋n⦌) (y : stdSimplex ℝ (Fin (n + 1)))
    (t : I) :
    compHom S n ((sngIncl A).app _ τ) (y, t) = ((sngEquiv (TopCat.of A) n τ) y : X) :=
  (S n).fix (f := sngEquiv X n ((sngIncl A).app _ τ))
    (fun z => ((sngEquiv (TopCat.of A) n τ) z).2) y t

/-- The deformation of the singular simplices of `X`, as a self-map. -/
def defRho (n : ℕ) (s : Sng X _⦋n⦌) : Sng X _⦋n⦌ :=
  (sngEquiv X n).symm
    ⟨fun y => compHom S n s (y, 1),
      (compHom S n s).continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem sngEquiv_defRho (n : ℕ) (s : Sng X _⦋n⦌) (y : stdSimplex ℝ (Fin (n + 1))) :
    sngEquiv X n (defRho S n s) y = compHom S n s (y, 1) := by
  rw [defRho, Equiv.apply_symm_apply]
  rfl

/-- The retraction of the singular simplices of `X` onto those of `A`. -/
def compRho (hc : ∀ n, (S n).Compresses) (n : ℕ) (s : Sng X _⦋n⦌) : Sng (TopCat.of A) _⦋n⦌ :=
  (sngEquiv (TopCat.of A) n).symm
    ⟨fun y => ⟨compHom S n s (y, 1), compHom_mem S (hc n) s y⟩,
      Continuous.subtype_mk
        ((compHom S n s).continuous.comp (continuous_id.prodMk continuous_const)) _⟩

theorem sngEquiv_compRho (hc : ∀ n, (S n).Compresses) (n : ℕ) (s : Sng X _⦋n⦌)
    (y : stdSimplex ℝ (Fin (n + 1))) :
    ((sngEquiv (TopCat.of A) n (compRho S hc n s)) y : X) = compHom S n s (y, 1) := by
  rw [compRho, Equiv.apply_symm_apply]
  rfl

/-- The homotopy operators of the compression. -/
def compH {n : ℕ} (i : Fin (n + 1)) (s : Sng X _⦋n⦌) : Sng X _⦋n + 1⦌ :=
  (sngEquiv X (n + 1)).symm ((compHom S n s).comp (prism i))

theorem sngEquiv_compH {n : ℕ} (i : Fin (n + 1)) (s : Sng X _⦋n⦌)
    (z : stdSimplex ℝ (Fin (n + 2))) :
    sngEquiv X (n + 1) (compH S i s) z = compHom S n s (prism i z) := by
  rw [compH, Equiv.apply_symm_apply]
  rfl

include hS in
/-- **The coherent deformation of the singular simplices of `X` of dimension at most `M` into
`A`.** -/
def deformation (M : ℕ) (hc : ∀ n ≤ M, (S n).Compresses) : SimplicialDeformation X A M where
  ρ := defRho S
  ρ_δ {n} i s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_defRho, sngEquiv_defRho, compHom_δ S hS]
  ρ_fix {n} τ := sng_ext fun y => by
    rw [sngEquiv_defRho, compHom_incl, sngEquiv_incl]
  ρ_mem {n} hn s := by
    refine ⟨(sngEquiv (TopCat.of A) n).symm
      ⟨fun y => ⟨compHom S n s (y, 1), compHom_mem S (hc n hn) s y⟩,
        Continuous.subtype_mk
          ((compHom S n s).continuous.comp (continuous_id.prodMk continuous_const)) _⟩, ?_⟩
    refine sng_ext fun y => ?_
    rw [sngEquiv_incl, Equiv.apply_symm_apply, sngEquiv_defRho]
    rfl
  h := fun {n} i => compH S i
  h_incl {n} i τ := by
    refine ⟨(sngEquiv (TopCat.of A) (n + 1)).symm
      ((sngEquiv (TopCat.of A) n τ).comp ⟨prismSpace i, continuous_prismSpace i⟩), ?_⟩
    refine sng_ext fun z => ?_
    rw [sngEquiv_incl, Equiv.apply_symm_apply, sngEquiv_compH, prism_apply, compHom_incl]
    rfl
  h_zero_δ_zero {n} s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, prism_apply, prismSpace_faceMap_zero, prismTime_faceMap_zero,
      compHom_zero]
  h_last_δ_last {n} s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, prism_apply, prismSpace_faceMap_last, prismTime_faceMap_last,
      sngEquiv_defRho]
  h_succ_δ_castSucc_of_lt {n} i j hij s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, sngEquiv_compH, prism_apply, prism_apply,
      prismSpace_faceMap_castSucc hij, prismTime_faceMap_castSucc hij, compHom_δ S hS]
  h_succ_δ_castSucc_succ {n} j s := sng_ext fun y => by
    rw [apply_δ, apply_δ, sngEquiv_compH, sngEquiv_compH, prism_faceMap_mid]
  h_castSucc_δ_succ_of_lt {n} i j hji s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, sngEquiv_compH, prism_apply, prism_apply,
      prismSpace_faceMap_succ hji, prismTime_faceMap_succ hji, compHom_δ S hS]

include hS in
/-- **The coherent compression of the singular simplices of `X` into `A`.** -/
def compression (hc : ∀ n, (S n).Compresses) : SimplicialCompression X A where
  ρ := compRho S hc
  ρ_δ {n} i s := sng_ext fun y => Subtype.ext (by
    rw [apply_δ, sngEquiv_compRho, sngEquiv_compRho, compHom_δ S hS])
  ρ_incl {n} τ := sng_ext fun y => Subtype.ext (by
    rw [sngEquiv_compRho, compHom_incl])
  h := fun {n} i => compH S i
  h_incl {n} i τ := by
    refine ⟨(sngEquiv (TopCat.of A) (n + 1)).symm
      ((sngEquiv (TopCat.of A) n τ).comp ⟨prismSpace i, continuous_prismSpace i⟩), ?_⟩
    refine sng_ext fun z => ?_
    rw [sngEquiv_incl, Equiv.apply_symm_apply, sngEquiv_compH, prism_apply, compHom_incl]
    rfl
  h_zero_δ_zero {n} s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, prism_apply, prismSpace_faceMap_zero, prismTime_faceMap_zero,
      compHom_zero]
  h_last_δ_last {n} s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, prism_apply, prismSpace_faceMap_last, prismTime_faceMap_last,
      sngEquiv_incl, sngEquiv_compRho]
  h_succ_δ_castSucc_of_lt {n} i j hij s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, sngEquiv_compH, prism_apply, prism_apply,
      prismSpace_faceMap_castSucc hij, prismTime_faceMap_castSucc hij, compHom_δ S hS]
  h_succ_δ_castSucc_succ {n} j s := sng_ext fun y => by
    rw [apply_δ, apply_δ, sngEquiv_compH, sngEquiv_compH, prism_faceMap_mid]
  h_castSucc_δ_succ_of_lt {n} i j hji s := sng_ext fun y => by
    rw [apply_δ, sngEquiv_compH, sngEquiv_compH, prism_apply, prism_apply,
      prismSpace_faceMap_succ hji, prismTime_faceMap_succ hji, compHom_δ S hS]

end Submission
