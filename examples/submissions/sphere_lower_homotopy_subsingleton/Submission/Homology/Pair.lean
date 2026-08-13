/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Point
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Relative singular homology and the long exact sequence of a pair

For a monomorphism `i : A ⟶ X` in `TopCat` (equivalently, an injective continuous map) we define
the relative singular chain complex as the cokernel of `C_*(A) ⟶ C_*(X)` — Mathlib already knows
this map is a monomorphism of chain complexes — and the relative homology `Hrel n i` as its
homology.

Since `ChainComplex AddCommGrpCat ℕ` is abelian, `0 → C_*(A) → C_*(X) → C_*(X,A) → 0` is short
exact essentially by definition, and Mathlib's homology-sequence machinery then yields the long
exact sequence of the pair.

## Main definitions

* `Csing X` — the singular chain complex of `X`;
* `relComplex i` — the relative chain complex of a monomorphism `i : A ⟶ X`;
* `Hrel n i` — relative singular homology;
* `relδ n i : Hrel (n+1) i ⟶ Hgrp n A` — the connecting homomorphism;
* `pairLES n i` — the six-term exact sequence
  `H_{n+1}(A) → H_{n+1}(X) → H_{n+1}(X,A) → H_n(A) → H_n(X) → H_n(X,A)`,
  together with `pairLES_exact`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- The singular chain complex of a topological space, with `ℤ` coefficients. -/
abbrev Csing (X : TopCat.{0}) : ChainComplex AddCommGrpCat.{0} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj X

/-- The singular chain complex as a functor. -/
abbrev CsingFunctor : TopCat.{0} ⥤ ChainComplex AddCommGrpCat.{0} ℕ :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

/-- The map of singular chain complexes induced by a continuous map. -/
def CsingMap {X Y : TopCat.{0}} (f : X ⟶ Y) : Csing X ⟶ Csing Y := CsingFunctor.map f

@[simp]
theorem CsingMap_id (X : TopCat.{0}) : CsingMap (𝟙 X) = 𝟙 (Csing X) :=
  CsingFunctor.map_id X

@[simp]
theorem CsingMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CsingMap (f ≫ g) = CsingMap f ≫ CsingMap g :=
  CsingFunctor.map_comp f g

instance mono_CsingMap {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Mono (CsingMap i) :=
  Functor.map_mono CsingFunctor i

/-- The relative singular chain complex `C_*(X, A)` of a monomorphism `i : A ⟶ X`. -/
def relComplex {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : ChainComplex AddCommGrpCat.{0} ℕ :=
  cokernel (CsingMap i)

/-- Relative singular homology `H_n(X, A; ℤ)`. -/
def Hrel (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : AddCommGrpCat.{0} :=
  (relComplex i).homology n

/-- The projection `C_*(X) ⟶ C_*(X, A)`. -/
def relProj {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Csing X ⟶ relComplex i :=
  cokernel.π (CsingMap i)

/-- The short complex `C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)`. -/
def relShortComplex {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ) :=
  ShortComplex.mk (CsingMap i) (cokernel.π (CsingMap i)) (by simp)

/-- `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0` is short exact. -/
theorem relShortComplex_shortExact {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (relShortComplex i).ShortExact where
  exact := ShortComplex.exact_cokernel (CsingMap i)
  mono_f := mono_CsingMap i
  epi_g := coequalizer.π_epi

/-- The connecting homomorphism `∂ : H_{n+1}(X, A) ⟶ H_n(A)`. -/
def relδ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Hrel (n + 1) i ⟶ Hgrp n A :=
  (relShortComplex_shortExact i).δ (n + 1) n rfl

/-- The map `H_n(A) ⟶ H_n(X)`. -/
abbrev relIota (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Hgrp n A ⟶ Hgrp n X :=
  HgrpMap n i

/-- The map `H_n(X) ⟶ H_n(X, A)`. -/
def relJ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : Hgrp n X ⟶ Hrel n i :=
  HomologicalComplex.homologyMap (relProj i) n

/-- The six-term long exact sequence of the pair `(X, A)`, starting at `H_{n+1}(A)`. -/
def pairLES (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : ComposableArrows AddCommGrpCat.{0} 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (relShortComplex_shortExact i) (n + 1) n rfl

/-- The long exact sequence of a pair is exact. -/
theorem pairLES_exact (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : (pairLES n i).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact _ _ _ _

/-- Exactness at `H_n(A)`: `H_{n+1}(X,A) → H_n(A) → H_n(X)`. -/
theorem pair_exact_δ_iota (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (relδ n i) (relIota n i)
      ((relShortComplex_shortExact i).δ_comp _ _ _)).Exact :=
  (relShortComplex_shortExact i).homology_exact₁ (n + 1) n rfl

/-- Exactness at `H_n(X)`: `H_n(A) → H_n(X) → H_n(X,A)`. -/
theorem pair_exact_iota_j (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relShortComplex i).f n)
      (HomologicalComplex.homologyMap (relShortComplex i).g n)
      (by simp [← HomologicalComplex.homologyMap_comp])).Exact :=
  (relShortComplex_shortExact i).homology_exact₂ n

/-- Exactness at `H_{n+1}(X,A)`: `H_{n+1}(X) → H_{n+1}(X,A) → H_n(A)`. -/
theorem pair_exact_j_δ (n : ℕ) {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] :
    (ShortComplex.mk (relJ (n + 1) i) (relδ n i)
      ((relShortComplex_shortExact i).comp_δ _ _ _)).Exact :=
  (relShortComplex_shortExact i).homology_exact₃ (n + 1) n rfl

/-! ### The inclusion of a subspace -/

/-- The inclusion of a subset, as a morphism of `TopCat`. -/
def subIncl {Y : TopCat.{0}} (A : Set Y) : TopCat.of A ⟶ Y :=
  TopCat.ofHom ⟨(Subtype.val : A → Y), continuous_subtype_val⟩

instance mono_subIncl {Y : TopCat.{0}} (A : Set Y) : Mono (subIncl A) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

/-- Relative singular homology of a pair `(Y, A)` with `A` a subspace. -/
abbrev HrelSet (n : ℕ) {Y : TopCat.{0}} (A : Set Y) : AddCommGrpCat.{0} := Hrel n (subIncl A)

/-! ### Reduced homology -/

/-- The inclusion of a basepoint, as a morphism of `TopCat`. -/
def ptIncl {X : TopCat.{0}} (x : X) : TopCat.of PUnit.{1} ⟶ X :=
  TopCat.ofHom ⟨fun _ => x, continuous_const⟩

instance mono_ptIncl {X : TopCat.{0}} (x : X) : Mono (ptIncl x) := by
  rw [TopCat.mono_iff_injective]
  intro a b _
  exact Subsingleton.elim a b

/-- Reduced singular homology `H̃_n(X)`, defined as `H_n(X, pt)`. -/
abbrev Hred (n : ℕ) {X : TopCat.{0}} (x : X) : AddCommGrpCat.{0} := Hrel n (ptIncl x)

/-- The unique map to the one-point space. -/
def toPt (X : TopCat.{0}) : X ⟶ TopCat.of PUnit.{1} :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

@[simp]
theorem ptIncl_comp_toPt {X : TopCat.{0}} (x : X) : ptIncl x ≫ toPt X = 𝟙 _ := by ext

/-- `H_n(pt) ⟶ H_n(X)` is a split monomorphism, hence a monomorphism. -/
instance mono_relIota_ptIncl (n : ℕ) {X : TopCat.{0}} (x : X) : Mono (relIota n (ptIncl x)) := by
  have : IsSplitMono (HgrpMap n (ptIncl x)) :=
    IsSplitMono.mk' ⟨HgrpMap n (toPt X), by rw [← HgrpMap_comp, ptIncl_comp_toPt, HgrpMap_id]⟩
  infer_instance

/-- The connecting map of the pair `(X, pt)` vanishes. -/
theorem relδ_ptIncl_eq_zero (n : ℕ) {X : TopCat.{0}} (x : X) : relδ n (ptIncl x) = 0 :=
  (pair_exact_δ_iota n (ptIncl x)).mono_g_iff.1 (mono_relIota_ptIncl n x)

instance mono_relJ_ptIncl (n : ℕ) {X : TopCat.{0}} (x : X) : Mono (relJ (n + 1) (ptIncl x)) :=
  (pair_exact_iota_j (n + 1) (ptIncl x)).mono_g
    ((isZero_Hgrp_punit (n + 1) n.succ_ne_zero).eq_zero_of_src _)

instance epi_relJ_ptIncl (n : ℕ) {X : TopCat.{0}} (x : X) : Epi (relJ (n + 1) (ptIncl x)) :=
  (pair_exact_j_δ n (ptIncl x)).epi_f (relδ_ptIncl_eq_zero n x)

/-- For positive degrees, reduced homology agrees with homology. -/
def hgrpIsoHred (n : ℕ) {X : TopCat.{0}} (x : X) : Hgrp (n + 1) X ≅ Hred (n + 1) x :=
  have : IsIso (relJ (n + 1) (ptIncl x)) := isIso_of_mono_of_epi _
  asIso (relJ (n + 1) (ptIncl x))

end Submission
