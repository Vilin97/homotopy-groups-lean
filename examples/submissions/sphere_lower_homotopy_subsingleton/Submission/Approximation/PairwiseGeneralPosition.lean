/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.Simplex

/-!
# Pairwise general position for piecewise-affine cube maps

This file supplies the two-family general-position input needed by stable-range excision.  For
pieces spanned by `r + 1` and `s + 1` points in a finite-dimensional real normed space `F`, the
translations which make the pieces meet lie in an affine subspace of dimension at most `r + s`.
They are therefore Haar-null when `r + s < finrank ℝ F`.

Applying this simultaneously to the finite Kuhn-simplex covers of two grid approximations gives
arbitrarily small translations which separate their entire images.  Combining that separation
with uniform grid approximation produces arbitrarily close PL approximations of two continuous
cube maps with disjoint images.

## Main results

* `Submission.addHaar_collisionTranslations_of_card_le`
* `Submission.exists_translation_separating_finite_families`
* `Submission.exists_translation_disjoint_cubeGridAffineApprox_ranges`
* `Submission.exists_disjoint_cubeGridAffineApproximations`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology

namespace Submission

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [FiniteDimensional ℝ F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-! ### Haar-null collision sets -/

/-- Translations which move some point of `A` onto some point of `B`. -/
def collisionTranslations (A B : Set F) : Set F :=
  {t | ∃ a ∈ A, ∃ b ∈ B, a + t = b}

/-- If `A` and `B` lie in affine spans of respectively `r + 1` and `s + 1` points and
`r + s < finrank ℝ F`, then the translations which make them collide are Haar-null. -/
theorem addHaar_collisionTranslations_of_card_le
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (p : ι → F) (q : κ → F) {A B : Set F}
    (hA : A ⊆ affineSpan ℝ (Set.range p))
    (hB : B ⊆ affineSpan ℝ (Set.range q))
    (hcard : Fintype.card ι + Fintype.card κ ≤ finrank ℝ F + 1) :
    μ (collisionTranslations A B) = 0 := by
  let i₀ : ι := Classical.choice inferInstance
  let j₀ : κ := Classical.choice inferInstance
  let P := affineSpan ℝ (Set.range p)
  let Q := affineSpan ℝ (Set.range q)
  let W : AffineSubspace ℝ F :=
    AffineSubspace.mk' (q j₀ - p i₀) (P.direction ⊔ Q.direction)
  have hp₀ : p i₀ ∈ P := by
    exact mem_affineSpan ℝ (Set.mem_range_self i₀)
  have hq₀ : q j₀ ∈ Q := by
    exact mem_affineSpan ℝ (Set.mem_range_self j₀)
  have hsub : collisionTranslations A B ⊆ W := by
    rintro t ⟨a, ha, b, hb, hab⟩
    change t ∈ AffineSubspace.mk' (q j₀ - p i₀) (P.direction ⊔ Q.direction)
    rw [AffineSubspace.mem_mk']
    have haP : a ∈ P := hA ha
    have hbQ : b ∈ Q := hB hb
    have hpa : a - p i₀ ∈ P.direction := P.vsub_mem_direction haP hp₀
    have hqb : b - q j₀ ∈ Q.direction := Q.vsub_mem_direction hbQ hq₀
    have ht : t = b - a := eq_sub_of_add_eq (by simpa [add_comm] using hab)
    rw [ht]
    change (b - a) - (q j₀ - p i₀) ∈ P.direction ⊔ Q.direction
    have heq : (b - a) - (q j₀ - p i₀) = (b - q j₀) - (a - p i₀) := by abel
    rw [heq]
    exact (P.direction ⊔ Q.direction).sub_mem
      ((show Q.direction ≤ P.direction ⊔ Q.direction from le_sup_right) hqb)
      ((show P.direction ≤ P.direction ⊔ Q.direction from le_sup_left) hpa)
  apply addHaar_of_subset_affineSubspace μ (W := W) ?_ hsub
  intro hW
  have hP : finrank ℝ P.direction + 1 ≤ Fintype.card ι := by
    rw [show P = affineSpan ℝ (Set.range p) from rfl, direction_affineSpan]
    exact finrank_vectorSpan_range_add_one_le ℝ p
  have hQ : finrank ℝ Q.direction + 1 ≤ Fintype.card κ := by
    rw [show Q = affineSpan ℝ (Set.range q) from rfl, direction_affineSpan]
    exact finrank_vectorSpan_range_add_one_le ℝ q
  have hsup : finrank ℝ (P.direction ⊔ Q.direction : Submodule ℝ F) ≤
      finrank ℝ P.direction + finrank ℝ Q.direction :=
    Submodule.finrank_add_le_finrank_add_finrank P.direction Q.direction
  have hlt : finrank ℝ (P.direction ⊔ Q.direction : Submodule ℝ F) < finrank ℝ F := by omega
  have hEq : P.direction ⊔ Q.direction = (⊤ : Submodule ℝ F) := by
    have := congrArg AffineSubspace.direction hW
    simpa [W] using this
  rw [hEq, finrank_top] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Finset form of `addHaar_collisionTranslations_of_card_le`. -/
theorem addHaar_collisionTranslations_of_finset_card_le
    {P Q : Finset F} (hP : P.Nonempty) (hQ : Q.Nonempty) {A B : Set F}
    (hA : A ⊆ affineSpan ℝ (P : Set F))
    (hB : B ⊆ affineSpan ℝ (Q : Set F))
    (hcard : P.card + Q.card ≤ finrank ℝ F + 1) :
    μ (collisionTranslations A B) = 0 := by
  letI : Nonempty P := hP.to_subtype
  letI : Nonempty Q := hQ.to_subtype
  apply addHaar_collisionTranslations_of_card_le μ
      (p := fun x : P => (x : F)) (q := fun x : Q => (x : F))
  · simpa [Subtype.range_coe_subtype, Finset.setOf_mem] using hA
  · simpa [Subtype.range_coe_subtype, Finset.setOf_mem] using hB
  · simpa [Fintype.card_coe] using hcard

omit [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Avoiding the collision set is exactly disjointness after translation. -/
theorem not_mem_collisionTranslations_iff_disjoint {A B : Set F} {t : F} :
    t ∉ collisionTranslations A B ↔ Disjoint ((fun a => a + t) '' A) B := by
  rw [Set.disjoint_left]
  constructor
  · intro ht x hxA hxB
    obtain ⟨a, ha, rfl⟩ := hxA
    exact ht ⟨a, ha, a + t, hxB, rfl⟩
  · intro hdisj ⟨a, ha, b, hb, hab⟩
    have hat : a + t ∈ B := by simpa [hab] using hb
    exact hdisj ⟨a, ha, rfl⟩ hat

include μ in
/-- Every nonempty open set contains a translation which simultaneously separates two finite
families of low-dimensional affine pieces. -/
theorem exists_translation_separating_finite_families
    {α β : Type*} (D : Finset α) (E : Finset β)
    (A : α → Set F) (B : β → Set F) (P : α → Finset F) (Q : β → Finset F)
    (hP : ∀ i ∈ D, (P i).Nonempty) (hQ : ∀ j ∈ E, (Q j).Nonempty)
    (hA : ∀ i ∈ D, A i ⊆ affineSpan ℝ (P i : Set F))
    (hB : ∀ j ∈ E, B j ⊆ affineSpan ℝ (Q j : Set F))
    (hcard : ∀ i ∈ D, ∀ j ∈ E, (P i).card + (Q j).card ≤ finrank ℝ F + 1)
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U, ∀ i ∈ D, ∀ j ∈ E, Disjoint ((fun a => a + t) '' A i) (B j) := by
  obtain ⟨t, htU, ht⟩ := exists_notMem_of_measure_zero μ (D.product E)
    (fun ij => collisionTranslations (A ij.1) (B ij.2)) (by
      rintro ⟨i, j⟩ hij
      have hij' := Finset.mem_product.mp hij
      exact addHaar_collisionTranslations_of_finset_card_le μ
        (hP i hij'.1) (hQ j hij'.2) (hA i hij'.1) (hB j hij'.2)
        (hcard i hij'.1 j hij'.2)) hU hUne
  refine ⟨t, htU, fun i hi j hj => ?_⟩
  rw [← not_mem_collisionTranslations_iff_disjoint]
  exact ht (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)

/-! ### Pairwise general position for the grid approximation -/

variable {n m N M : ℕ}

/-- The finite set of target vertices spanning the image of one grid simplex. -/
noncomputable def gridSimplexValues (N : ℕ) (g : C(I^ Fin n, F))
    (S : Finset (Fin n → ℕ)) : Finset F := by
  classical
  exact S.image fun v => g (gridVertex N v)

/-- The convex target piece attached to one grid simplex. -/
def gridSimplexHull (N : ℕ) (g : C(I^ Fin n, F)) (S : Finset (Fin n → ℕ)) : Set F :=
  convexHull ℝ ((fun v => g (gridVertex N v)) '' (S : Set (Fin n → ℕ)))

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- A grid-simplex hull lies in the affine span of its finite set of target vertices. -/
theorem gridSimplexHull_subset_affineSpan_values (g : C(I^ Fin n, F))
    (S : Finset (Fin n → ℕ)) :
    gridSimplexHull N g S ⊆ affineSpan ℝ (gridSimplexValues N g S : Set F) := by
  classical
  rw [gridSimplexHull, gridSimplexValues, Finset.coe_image]
  exact convexHull_subset_affineSpan _

omit [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- A nonempty grid simplex has a nonempty set of target vertices. -/
theorem gridSimplexValues_nonempty (g : C(I^ Fin n, F)) {S : Finset (Fin n → ℕ)}
    (hS : S.Nonempty) : (gridSimplexValues N g S).Nonempty := by
  classical
  simpa [gridSimplexValues] using hS.image (fun v => g (gridVertex N v))

omit [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- Taking target values cannot increase the number of vertices. -/
theorem card_gridSimplexValues_le (g : C(I^ Fin n, F)) (S : Finset (Fin n → ℕ)) :
    (gridSimplexValues N g S).card ≤ S.card := by
  classical
  simpa [gridSimplexValues] using
    (Finset.card_image_le (s := S) (f := fun v => g (gridVertex N v)))

omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- The range cover from `range_cubeGridAffineApprox_subset`, with empty simplices removed. -/
theorem range_cubeGridAffineApprox_subset_nonempty_hulls (hN : 1 ≤ N)
    (g : C(I^ Fin n, F)) :
    Set.range (cubeGridAffineApprox n N g) ⊆
      ⋃ S ∈ (gridSimplices n N).filter Finset.Nonempty, gridSimplexHull N g S := by
  rintro _ ⟨y, rfl⟩
  exact Set.mem_iUnion₂.mpr
    ⟨activeVerts N y,
      Finset.mem_filter.mpr
        ⟨activeVerts_mem_gridSimplices hN y, activeVerts_nonempty hN y⟩,
      cubeGridAffineApprox_mem_convexHull hN g y⟩

include μ in
/-- **Pairwise PL general position.**  If the dimensions of two cubes add up to strictly less
than the dimension of `F`, then an arbitrarily small translation makes their piecewise-affine
grid approximations disjoint. -/
theorem exists_translation_disjoint_cubeGridAffineApprox_ranges
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F))
    {U : Set F} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ t ∈ U,
      Disjoint ((fun x => x + t) '' Set.range (cubeGridAffineApprox n N g))
        (Set.range (cubeGridAffineApprox m M h)) := by
  classical
  let D := (gridSimplices n N).filter Finset.Nonempty
  let E := (gridSimplices m M).filter Finset.Nonempty
  obtain ⟨t, htU, ht⟩ := exists_translation_separating_finite_families μ D E
    (gridSimplexHull N g) (gridSimplexHull M h)
    (gridSimplexValues N g) (gridSimplexValues M h)
    (by
      intro S hS
      exact gridSimplexValues_nonempty g (Finset.mem_filter.mp hS).2)
    (by
      intro T hT
      exact gridSimplexValues_nonempty h (Finset.mem_filter.mp hT).2)
    (fun S _ => gridSimplexHull_subset_affineSpan_values g S)
    (fun T _ => gridSimplexHull_subset_affineSpan_values h T)
    (by
      intro S hS T hT
      have hScard := card_le_of_mem_gridSimplices (Finset.mem_filter.mp hS).1
      have hTcard := card_le_of_mem_gridSimplices (Finset.mem_filter.mp hT).1
      have hSvalues := card_gridSimplexValues_le (N := N) g S
      have hTvalues := card_gridSimplexValues_le (N := M) h T
      omega)
    hU hUne
  refine ⟨t, htU, Set.disjoint_left.mpr ?_⟩
  intro x hxg hxh
  obtain ⟨a, ha, rfl⟩ := hxg
  have ha' := range_cubeGridAffineApprox_subset_nonempty_hulls hN g ha
  obtain ⟨S, hS, haS⟩ := Set.mem_iUnion₂.mp ha'
  have hh' := range_cubeGridAffineApprox_subset_nonempty_hulls hM h hxh
  obtain ⟨T, hT, hhT⟩ := Set.mem_iUnion₂.mp hh'
  exact Set.disjoint_left.mp (ht S hS T hT) ⟨a, haS, rfl⟩ hhT

include μ in
/-- **Two-map PL approximation in general position.**  Two continuous cube maps whose source
dimensions add up to less than the target dimension admit arbitrarily close piecewise-affine
approximations with disjoint images.  The first approximation is moved by one arbitrarily small
translation; the second is left fixed. -/
theorem exists_disjoint_cubeGridAffineApproximations
    (hdim : n + m + 1 ≤ finrank ℝ F)
    (g : C(I^ Fin n, F)) (h : C(I^ Fin m, F)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N M : ℕ) (t : F), 1 ≤ N ∧ 1 ≤ M ∧
      (∀ y, dist (cubeGridAffineApprox n N g y + t) (g y) < δ) ∧
      (∀ z, dist (cubeGridAffineApprox m M h z) (h z) < δ) ∧
      Disjoint ((fun x => x + t) '' Set.range (cubeGridAffineApprox n N g))
        (Set.range (cubeGridAffineApprox m M h)) := by
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨N, hN, hg⟩ := exists_cubeGridAffineApprox_dist_le n g hhalf
  obtain ⟨M, hM, hh⟩ := exists_cubeGridAffineApprox_dist_le m h hhalf
  obtain ⟨t, htball, hdisj⟩ :=
    exists_translation_disjoint_cubeGridAffineApprox_ranges μ hN hM hdim g h
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hhalf⟩
  have ht : ‖t‖ < δ / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using htball
  refine ⟨N, M, t, hN, hM, ?_, ?_, hdisj⟩
  · intro y
    calc
      dist (cubeGridAffineApprox n N g y + t) (g y)
          ≤ dist (cubeGridAffineApprox n N g y + t) (cubeGridAffineApprox n N g y) +
              dist (cubeGridAffineApprox n N g y) (g y) := dist_triangle _ _ _
      _ = ‖t‖ + dist (cubeGridAffineApprox n N g y) (g y) := by
        rw [dist_eq_norm]
        simp
      _ < δ := by linarith [hg y]
  · intro z
    exact lt_of_le_of_lt (hh z) (by linarith)

end Submission
