/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Submission.Homology.PairHomotopy
import Submission.Homotopy.RelMap

/-!
# Naturality of relative singular homology

A commutative square of inclusions induces a morphism between the corresponding short exact
sequences of singular chain complexes.  This file packages that morphism and records naturality
of all three maps in the long exact sequence of a pair.  It also lets the `BasedPairMap` structure
used by relative homotopy induce the corresponding map on relative singular homology.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace Submission

variable {A X B Y : TopCat.{0}}

/-- The morphism between the relative short exact sequences induced by a map of pairs. -/
def relShortComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relShortComplex i ⟶ relShortComplex j where
  τ₁ := CsingMap fA
  τ₂ := CsingMap f
  τ₃ := relComplexMap i j w
  comm₁₂ := by
    change CsingMap fA ≫ CsingMap j = CsingMap i ≫ CsingMap f
    simp only [CsingMap]
    rw [← CsingFunctor.map_comp, ← CsingFunctor.map_comp, w]
  comm₂₃ := (relProj_comp_relComplexMap i j w).symm

@[simp]
theorem relShortComplexMap_τ₁ (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    (relShortComplexMap i j w).τ₁ = CsingMap fA :=
  rfl

@[simp]
theorem relShortComplexMap_τ₂ (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    (relShortComplexMap i j w).τ₂ = CsingMap f :=
  rfl

@[simp]
theorem relShortComplexMap_τ₃ (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    (relShortComplexMap i j w).τ₃ = relComplexMap i j w :=
  rfl

/-- Naturality at the subspace-to-ambient map in the long exact sequence of a pair. -/
theorem relIota_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relIota n i ≫ HgrpMap n f = HgrpMap n fA ≫ relIota n j := by
  rw [← HgrpMap_comp, ← HgrpMap_comp, w]

/-- Naturality at the absolute-to-relative map in the long exact sequence of a pair. -/
theorem relJ_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relJ n i ≫ HrelMap n i j w = HgrpMap n f ≫ relJ n j := by
  change HomologicalComplex.homologyMap (relProj i) n ≫
      HomologicalComplex.homologyMap (relComplexMap i j w) n =
    HomologicalComplex.homologyMap (CsingMap f) n ≫
      HomologicalComplex.homologyMap (relProj j) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relProj_comp_relComplexMap]

/-- Naturality of the connecting homomorphism in the long exact sequence of a pair. -/
theorem relδ_naturality (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relδ n i ≫ HgrpMap n fA = HrelMap (n + 1) i j w ≫ relδ n j := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (relShortComplexMap i j w) (relShortComplex_shortExact i)
      (relShortComplex_shortExact j) (n + 1) n rfl

/-- A map of pairs whose subspace and ambient maps are isomorphisms induces an isomorphism on
relative singular homology. -/
theorem isIso_HrelMap_of_isIso (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} [IsIso fA] [IsIso f] (w : i ≫ f = fA ≫ j) :
    IsIso (HrelMap n i j w) := by
  letI : IsIso (CsingMap fA) := by unfold CsingMap; infer_instance
  letI : IsIso (CsingMap f) := by unfold CsingMap; infer_instance
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (relShortComplexMap i j w) (relShortComplex_shortExact i)
      (relShortComplex_shortExact j)
  · change Epi (HomologicalComplex.homologyMap (CsingMap fA) n)
    infer_instance
  · change IsIso (HomologicalComplex.homologyMap (CsingMap f) n)
    infer_instance
  · intro k _
    change IsIso (HomologicalComplex.homologyMap (CsingMap fA) k)
    infer_instance
  · intro k _
    change Mono (HomologicalComplex.homologyMap (CsingMap f) k)
    infer_instance

namespace BasedPairMap

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {A : Set X} {B : Set Y} {C : Set Z} {a : A} {b : B} {c : C}

/-- The ambient `TopCat` morphism underlying a based map of pairs. -/
def ambientHom (f : BasedPairMap A B a b) : TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom f.toContinuousMap

/-- The `TopCat` morphism induced between the distinguished subspaces. -/
def subspaceHom (f : BasedPairMap A B a b) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom f.subspaceMap

/-- The square of subspace inclusions associated to a based map of pairs commutes. -/
theorem subIncl_naturality (f : BasedPairMap A B a b) :
    subIncl (Y := TopCat.of X) A ≫ f.ambientHom =
      f.subspaceHom ≫ subIncl (Y := TopCat.of Y) B := by
  ext x
  rfl

/-- The map on relative singular homology induced by a based map of pairs. -/
def hrelMap (n : ℕ) (f : BasedPairMap A B a b) :
    HrelSet (Y := TopCat.of X) n A ⟶ HrelSet (Y := TopCat.of Y) n B :=
  HrelMap n (subIncl (Y := TopCat.of X) A) (subIncl (Y := TopCat.of Y) B)
    f.subIncl_naturality

/-- The relative homology map induced by the identity based pair map is the identity. -/
@[simp]
theorem hrelMap_id (n : ℕ) : hrelMap n (BasedPairMap.id : BasedPairMap A A a a) = 𝟙 _ := by
  exact HrelMap_id n (subIncl (Y := TopCat.of X) A)

/-- Relative homology maps induced by based pair maps respect composition. -/
@[simp]
theorem hrelMap_comp (n : ℕ) (g : BasedPairMap B C b c) (f : BasedPairMap A B a b) :
    hrelMap n f ≫ hrelMap n g = hrelMap n (g.comp f) := by
  exact HrelMap_comp n (subIncl (Y := TopCat.of X) A) (subIncl (Y := TopCat.of Y) B)
    (subIncl (Y := TopCat.of Z) C)
    f.subIncl_naturality g.subIncl_naturality

end BasedPairMap

end Submission
