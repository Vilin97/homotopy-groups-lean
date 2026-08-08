/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# General position: regular values of piecewise-affine maps

This file contains the measure-theoretic half of the piecewise-affine general position argument.
It is the replacement, in the PL world, for Sard's theorem.

The only input from Mathlib is `MeasureTheory.Measure.addHaar_affineSubspace`: a proper affine
subspace of a finite-dimensional real normed space is Haar-null.  Everything here is a
consequence.

Two situations are covered, and they are the two the project needs:

* a piece on which an affine map `L` is *degenerate* (not surjective): its image is contained in
  the proper affine subspace `range L`, hence is null
  (`Submission.addHaar_image_of_not_surjective`);
* a piece which is spanned by *too few points* — a face of a simplex, or a whole simplex of a
  triangulation of a cube of dimension `k < finrank ℝ F`: its image is contained in the affine
  span of at most `finrank ℝ F` points, hence again is null
  (`Submission.addHaar_image_of_card_le`).

Since a finite union of null sets is null and a nonempty open set has positive Haar measure,
some point of any nonempty open set is missed by all these images
(`Submission.exists_regular_value`, `Submission.exists_regular_value_of_card_le`).

## Main results

* `Submission.addHaar_of_affineSpan_ne_top`
* `Submission.addHaar_image_of_not_surjective`
* `Submission.addHaar_of_card_le`, `Submission.addHaar_image_of_card_le`
* `Submission.exists_notMem_of_measure_zero`
* `Submission.exists_regular_value`, `Submission.exists_regular_value_of_card_le`
-/

open MeasureTheory Module Set

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-! ### Null sets coming from proper affine subspaces -/

/-- A set whose affine span is not everything is Haar-null. -/
theorem addHaar_of_affineSpan_ne_top {s : Set F} (hs : affineSpan ℝ s ≠ ⊤) : μ s = 0 :=
  measure_mono_null (subset_affineSpan ℝ s) (Measure.addHaar_affineSubspace μ _ hs)

/-- A set contained in a proper affine subspace is Haar-null. -/
theorem addHaar_of_subset_affineSubspace {s : Set F} {W : AffineSubspace ℝ F} (hW : W ≠ ⊤)
    (hs : s ⊆ W) : μ s = 0 :=
  measure_mono_null hs (Measure.addHaar_affineSubspace μ _ hW)

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The affine span of at most `finrank ℝ F` points of `F` is a proper affine subspace. -/
theorem affineSpan_range_ne_top {ι : Type*} [Fintype ι] (p : ι → F)
    (hcard : Fintype.card ι ≤ finrank ℝ F) : affineSpan ℝ (Set.range p) ≠ ⊤ := by
  intro htop
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    ⟨Fintype.card ι - 1, (Nat.succ_pred_eq_of_pos
      (AffineSubspace.card_pos_of_affineSpan_eq_top ℝ F F htop)).symm⟩
  have h₁ : finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ m := finrank_vectorSpan_range_le ℝ p hm
  have h₂ : vectorSpan ℝ (Set.range p) = ⊤ :=
    AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ F F htop
  rw [h₂, finrank_top] at h₁
  omega

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The affine span of a finite set of at most `finrank ℝ F` points is a proper affine
subspace. -/
theorem affineSpan_coe_ne_top {T : Finset F} (hcard : T.card ≤ finrank ℝ F) :
    affineSpan ℝ (T : Set F) ≠ ⊤ := by
  have h := affineSpan_range_ne_top (fun x : {x // x ∈ T} => (x : F))
    (by rwa [Fintype.card_coe])
  rwa [Subtype.range_coe_subtype, Finset.setOf_mem] at h

/-- A set contained in the affine span of a finite set of at most `finrank ℝ F` points is
Haar-null. -/
theorem addHaar_of_finset_card_le {s : Set F} {T : Finset F}
    (hs : s ⊆ affineSpan ℝ (T : Set F)) (hcard : T.card ≤ finrank ℝ F) : μ s = 0 :=
  addHaar_of_subset_affineSubspace μ (affineSpan_coe_ne_top hcard) hs

/-- A set contained in the affine span of at most `finrank ℝ F` points is Haar-null.

This is the statement that covers a simplex of dimension `< finrank ℝ F` and, in particular, the
image of a `k`-simplex under an affine map into an `n`-dimensional space when `k < n`. -/
theorem addHaar_of_card_le {ι : Type*} [Fintype ι] {s : Set F} {p : ι → F}
    (hs : s ⊆ affineSpan ℝ (Set.range p)) (hcard : Fintype.card ι ≤ finrank ℝ F) : μ s = 0 :=
  addHaar_of_subset_affineSubspace μ (affineSpan_range_ne_top p hcard) hs

section AffineMap

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- **The image of a degenerate affine map is Haar-null.**  If an affine map `L : P →ᵃ[ℝ] F` is
not surjective, then its range is a proper affine subspace of `F` and the image of any set under
`L` has Haar measure zero. -/
theorem addHaar_image_of_not_surjective (L : P →ᵃ[ℝ] F) (hL : ¬Function.Surjective L)
    (s : Set P) : μ (L '' s) = 0 := by
  refine addHaar_of_subset_affineSubspace μ (W := (⊤ : AffineSubspace ℝ P).map L) ?_ ?_
  · intro htop
    refine hL (Set.range_eq_univ.mp ?_)
    have := congrArg (fun W : AffineSubspace ℝ F => (W : Set F)) htop
    simpa [AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ] using this
  · rw [AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ]
    exact Set.image_subset_range _ _

/-- The image under an affine map of a set contained in the affine span of at most
`finrank ℝ F` points is Haar-null.

Together with `Submission.exists_regular_value_of_card_le` this is exactly the general position
input needed to show that a piecewise-affine map from a `k`-dimensional complex into an
`n`-dimensional space with `k < n` is not surjective. -/
theorem addHaar_image_of_card_le {ι : Type*} [Fintype ι] (L : P →ᵃ[ℝ] F) {s : Set P} {p : ι → P}
    (hs : s ⊆ affineSpan ℝ (Set.range p)) (hcard : Fintype.card ι ≤ finrank ℝ F) :
    μ (L '' s) = 0 := by
  have himg : (L : P → F) '' (affineSpan ℝ (Set.range p) : Set P)
      = (affineSpan ℝ (Set.range fun i => L (p i)) : Set F) := by
    rw [← AffineSubspace.coe_map, AffineSubspace.map_span, ← Set.range_comp]
    rfl
  refine addHaar_of_card_le μ (p := fun i => L (p i)) ?_ hcard
  rw [← himg]
  exact Set.image_mono hs

end AffineMap

/-! ### Existence of a regular value -/

omit [NormedSpace ℝ F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- A nonempty open set is not covered by finitely many null sets. -/
theorem exists_notMem_of_measure_zero {ι : Type*} (D : Finset ι) (T : ι → Set F)
    (hT : ∀ i ∈ D, μ (T i) = 0) {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ i ∈ D, q ∉ T i := by
  have hsum : ∑ i ∈ D, μ (T i) = 0 := Finset.sum_eq_zero hT
  have hnull : μ (⋃ i ∈ D, T i) = 0 :=
    nonpos_iff_eq_zero.mp (hsum ▸ measure_biUnion_finset_le D T)
  have hpos := hU.measure_pos μ hUne
  have hsub : ¬U ⊆ ⋃ i ∈ D, T i := fun h => hpos.ne' (measure_mono_null h hnull)
  obtain ⟨q, hqU, hq⟩ := Set.not_subset.mp hsub
  exact ⟨q, hqU, fun i hi hqi => hq (Set.mem_iUnion₂.mpr ⟨i, hi, hqi⟩)⟩

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

include μ in
/-- **Existence of a regular value.**  Let `L i` be finitely many affine maps `P →ᵃ[ℝ] F`, let
`S i ⊆ P` be arbitrary pieces, and suppose that for every `i` in the index set `D` the map `L i`
fails to be surjective.  Then every nonempty open set `U ⊆ F` contains a point that is missed by
all the images `L i '' S i`, `i ∈ D`. -/
theorem exists_regular_value {ι : Type*} (D : Finset ι) (L : ι → P →ᵃ[ℝ] F) (S : ι → Set P)
    (hL : ∀ i ∈ D, ¬Function.Surjective (L i)) {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ i ∈ D, q ∉ L i '' S i :=
  exists_notMem_of_measure_zero μ D _
    (fun i hi => addHaar_image_of_not_surjective μ (L i) (hL i hi) (S i)) hU hUne

include μ in
/-- **Existence of a regular value, low-dimensional version.**  If each piece `S i` lies in the
affine span of at most `finrank ℝ F` points, then every nonempty open set `U ⊆ F` contains a
point missed by all the images `L i '' S i`, `i ∈ D`.

Taking `U = Set.univ` this says that such a piecewise-affine map is not surjective, which is the
statement needed to show `π_k (Sⁿ) = 0` for `k < n`. -/
theorem exists_regular_value_of_card_le {ι κ : Type*} [Fintype κ] (D : Finset ι)
    (L : ι → P →ᵃ[ℝ] F) (S : ι → Set P) (p : ι → κ → P)
    (hS : ∀ i ∈ D, S i ⊆ affineSpan ℝ (Set.range (p i)))
    (hcard : Fintype.card κ ≤ finrank ℝ F) {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ i ∈ D, q ∉ L i '' S i :=
  exists_notMem_of_measure_zero μ D _
    (fun i hi => addHaar_image_of_card_le μ (L i) (hS i hi) hcard) hU hUne

include μ in
/-- A finite union of images of low-dimensional pieces is not all of `F`: a piecewise-affine map
whose pieces are spanned by at most `finrank ℝ F` points each is never surjective. -/
theorem not_surjective_of_card_le {ι κ : Type*} [Fintype κ] (D : Finset ι) (L : ι → P →ᵃ[ℝ] F)
    (S : ι → Set P) (p : ι → κ → P) (hS : ∀ i ∈ D, S i ⊆ affineSpan ℝ (Set.range (p i)))
    (hcard : Fintype.card κ ≤ finrank ℝ F) : ⋃ i ∈ D, L i '' S i ≠ Set.univ := by
  intro hcov
  obtain ⟨q, -, hq⟩ := exists_regular_value_of_card_le μ D L S p hS hcard isOpen_univ
    Set.univ_nonempty
  have hmem : q ∈ ⋃ i ∈ D, L i '' S i := hcov ▸ Set.mem_univ q
  obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp hmem
  exact hq i hi hqi

end Submission
