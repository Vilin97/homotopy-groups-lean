/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# The standard simplex is a disk, and its boundary is the sphere

The compression lemma and the homotopy extension property of the vendored `WhiteheadTheorem`
library are stated for the pair `(𝔻 j, ∂𝔻 j)`.  In order to run the compression recursion over
singular simplices we must identify the pair `(|Δ^j|, |∂Δ^j|)` with it.

The route is the one used in `Submission/Model/CubeSphere.lean` for the cube: drop the `0`-th
barycentric coordinate to realise `|Δ^j|` as the *corner simplex*
`{y ∈ ℝ^j | 0 ≤ y i, ∑ y i ≤ 1}`, a compact convex set with nonempty interior, and then apply
Mathlib's `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`.  The point of the corner
model is that the topological boundary of the corner simplex corresponds exactly to the set of
points of `|Δ^j|` with some barycentric coordinate equal to zero, which is `|∂Δ^j|`.

## Main definitions and results

* `Submission.simplexSet j` — the corner simplex in `ℝ^j`;
* `Submission.simplexEmb` — the embedding of `|Δ^j|` onto it;
* `Submission.simplexEmb_mem_frontier_iff` — the boundary correspondence;
* `Submission.simplexHomeoBall j : |Δ^j| ≃ₜ closedBall 0 1`, together with
  `Submission.norm_simplexHomeoBall_eq_one_iff` identifying `|∂Δ^j|` with the unit sphere;
* `Submission.simplexHomeoDisk j : SimplexCategory.toTop.obj ⦋j⦌ ≃ₜ TopCat.disk j`.
-/

open Metric Set Simplicial

noncomputable section

namespace Submission

variable {j : ℕ}

/-! ### The corner simplex in `ℝ^j` -/

/-- The corner simplex `{y ∈ ℝ^j | 0 ≤ y i for all i, ∑ y i ≤ 1}`. -/
def simplexSet (j : ℕ) : Set (EuclideanSpace ℝ (Fin j)) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

theorem mem_simplexSet {y : EuclideanSpace ℝ (Fin j)} :
    y ∈ simplexSet j ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 := Iff.rfl

theorem convex_simplexSet : Convex ℝ (simplexSet j) := by
  rintro y ⟨hy₀, hy₁⟩ z ⟨hz₀, hz₁⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · have h : (a • y + b • z) i = a * y i + b * z i := rfl
    rw [h]
    exact add_nonneg (mul_nonneg ha (hy₀ i)) (mul_nonneg hb (hz₀ i))
  · have h : ∑ i, (a • y + b • z) i = a * ∑ i, y i + b * ∑ i, z i := by
      simp [Finset.mul_sum, Finset.sum_add_distrib]
    rw [h]
    nlinarith

theorem isClosed_simplexSet : IsClosed (simplexSet j) := by
  have h₁ : IsClosed (⋂ i : Fin j, {y : EuclideanSpace ℝ (Fin j) | 0 ≤ y i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have h₂ : IsClosed {y : EuclideanSpace ℝ (Fin j) | ∑ i, y i ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  have : simplexSet j = (⋂ i : Fin j, {y : EuclideanSpace ℝ (Fin j) | 0 ≤ y i}) ∩
      {y : EuclideanSpace ℝ (Fin j) | ∑ i, y i ≤ 1} := by
    ext y; simp [simplexSet, mem_iInter]
  rw [this]
  exact h₁.inter h₂

theorem simplexSet_subset_closedBall : simplexSet j ⊆ closedBall 0 ((j : ℝ) + 1) := by
  rintro y ⟨hy₀, hy₁⟩
  have hle : ∀ i, y i ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (f := fun i => y i) (fun i _ => hy₀ i) (Finset.mem_univ i)) hy₁
  refine mem_closedBall_zero_iff.2 ?_
  rw [EuclideanSpace.norm_eq]
  have hb : ∑ i, ‖y i‖ ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin j)), ‖y i‖ ^ 2 ≤ 1 := by
      intro i _
      have h0 := hy₀ i
      have h2 := hle i
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin j, (1 : ℝ) := Finset.sum_le_sum h1
      _ = (j : ℝ) := by simp
      _ ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  calc Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt (((j : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (j : ℝ) + 1 := Real.sqrt_sq (by positivity)

theorem isBounded_simplexSet : Bornology.IsBounded (simplexSet j) :=
  (isBounded_closedBall).subset simplexSet_subset_closedBall

/-! ### The interior of the corner simplex -/

/-- The open corner simplex. -/
def openSimplexSet (j : ℕ) : Set (EuclideanSpace ℝ (Fin j)) :=
  {y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}

theorem isOpen_openSimplexSet : IsOpen (openSimplexSet j) := by
  have h₁ : IsOpen (⋂ i : Fin j, {y : EuclideanSpace ℝ (Fin j) | 0 < y i}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have h₂ : IsOpen {y : EuclideanSpace ℝ (Fin j) | ∑ i, y i < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have : openSimplexSet j = (⋂ i : Fin j, {y : EuclideanSpace ℝ (Fin j) | 0 < y i}) ∩
      {y : EuclideanSpace ℝ (Fin j) | ∑ i, y i < 1} := by
    ext y; simp [openSimplexSet, mem_iInter]
  rw [this]
  exact h₁.inter h₂

theorem openSimplexSet_subset : openSimplexSet j ⊆ simplexSet j :=
  fun _ hy => ⟨fun i => (hy.1 i).le, hy.2.le⟩

theorem openSimplexSet_subset_interior : openSimplexSet j ⊆ interior (simplexSet j) :=
  interior_maximal openSimplexSet_subset isOpen_openSimplexSet

theorem interior_simplexSet_nonempty : (interior (simplexSet j)).Nonempty := by
  have hpos : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
  refine ⟨WithLp.toLp 2 fun _ => (1 : ℝ) / (2 * ((j : ℝ) + 1)),
    openSimplexSet_subset_interior ⟨fun _ => by positivity, ?_⟩⟩
  show ∑ _i : Fin j, (1 : ℝ) / (2 * ((j : ℝ) + 1)) < 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
    div_lt_one hpos]
  linarith [Nat.cast_nonneg (α := ℝ) j]

/-- A point of the corner simplex with a vanishing coordinate is not interior. -/
theorem notMem_interior_of_coord_eq_zero {y : EuclideanSpace ℝ (Fin j)} (k : Fin j)
    (hk : y k = 0) : y ∉ interior (simplexSet j) := by
  intro hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
  set z : EuclideanSpace ℝ (Fin j) := y - EuclideanSpace.single k (ε / 2) with hz
  have hdist : dist z y < ε := by
    rw [hz, dist_eq_norm, sub_sub_cancel_left, norm_neg, PiLp.norm_single,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hmem : z ∈ simplexSet j := interior_subset (hball (Metric.mem_ball.2 hdist))
  have hzk : z k = -(ε / 2) := by simp [hz, hk]
  have h0 := hmem.1 k
  rw [hzk] at h0
  linarith

/-- A point of the corner simplex whose coordinates sum to `1` is not interior. -/
theorem notMem_interior_of_sum_eq_one {y : EuclideanSpace ℝ (Fin j)}
    (hs : ∑ i, y i = 1) : y ∉ interior (simplexSet j) := by
  intro hy
  have hj : 0 < j := by
    by_contra hj
    have : j = 0 := by lia
    subst this
    simp at hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
  set k : Fin j := ⟨0, hj⟩
  set z : EuclideanSpace ℝ (Fin j) := y + EuclideanSpace.single k (ε / 2) with hz
  have hdist : dist z y < ε := by
    rw [hz, dist_eq_norm, add_sub_cancel_left, PiLp.norm_single,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hmem : z ∈ simplexSet j := interior_subset (hball (Metric.mem_ball.2 hdist))
  have hsum : ∑ i, z i = 1 + ε / 2 := by
    have hz' : ∀ i, z i = y i + (if i = k then ε / 2 else 0) := fun i => by
      simp [hz, PiLp.single_apply]
    rw [Finset.sum_congr rfl fun i _ => hz' i, Finset.sum_add_distrib, hs]
    simp
  have := hmem.2
  rw [hsum] at this
  linarith

theorem interior_simplexSet_eq : interior (simplexSet j) = openSimplexSet j := by
  refine Subset.antisymm (fun y hy => ⟨fun i => ?_, ?_⟩) openSimplexSet_subset_interior
  · rcases lt_or_eq_of_le ((interior_subset hy).1 i) with h | h
    · exact h
    · exact absurd hy (notMem_interior_of_coord_eq_zero i h.symm)
  · rcases lt_or_eq_of_le (interior_subset hy).2 with h | h
    · exact h
    · exact absurd hy (notMem_interior_of_sum_eq_one h)

/-! ### The simplex as the corner simplex -/

/-- The embedding of the standard `j`-simplex into `ℝ^j`, dropping the `0`-th coordinate. -/
def simplexEmb (x : stdSimplex ℝ (Fin (j + 1))) : EuclideanSpace ℝ (Fin j) :=
  WithLp.toLp 2 fun i : Fin j => x.1 i.succ

@[simp]
theorem simplexEmb_apply (x : stdSimplex ℝ (Fin (j + 1))) (i : Fin j) :
    simplexEmb x i = x.1 i.succ := rfl

theorem continuous_simplexEmb : Continuous (simplexEmb (j := j)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin j => ℝ)).comp
    (continuous_pi fun i => (continuous_apply i.succ).comp continuous_subtype_val)

theorem sum_simplexEmb (x : stdSimplex ℝ (Fin (j + 1))) :
    ∑ i, simplexEmb x i = ∑ i : Fin j, x.1 i.succ := rfl

theorem simplexEmb_zero_coord (x : stdSimplex ℝ (Fin (j + 1))) :
    x.1 0 = 1 - ∑ i, simplexEmb x i := by
  have h := x.2.2
  rw [Fin.sum_univ_succ] at h
  rw [sum_simplexEmb]
  linarith

theorem simplexEmb_injective : Function.Injective (simplexEmb (j := j)) := by
  intro x y h
  refine Subtype.ext (funext fun i => ?_)
  induction i using Fin.cases with
  | zero => rw [simplexEmb_zero_coord, simplexEmb_zero_coord, h]
  | succ i => exact congrArg (fun z : EuclideanSpace ℝ (Fin j) => z i) h

theorem simplexEmb_mem (x : stdSimplex ℝ (Fin (j + 1))) : simplexEmb x ∈ simplexSet j := by
  refine ⟨fun i => x.2.1 _, ?_⟩
  have h := simplexEmb_zero_coord x
  have h0 := x.2.1 0
  linarith

/-- The inverse of `simplexEmb`, restoring the `0`-th coordinate. -/
def simplexEmbInv (y : EuclideanSpace ℝ (Fin j)) : Fin (j + 1) → ℝ :=
  Fin.cons (1 - ∑ i, y i) fun i => y i

theorem simplexEmbInv_mem {y : EuclideanSpace ℝ (Fin j)} (hy : y ∈ simplexSet j) :
    simplexEmbInv y ∈ stdSimplex ℝ (Fin (j + 1)) := by
  refine ⟨fun i => ?_, ?_⟩
  · induction i using Fin.cases with
    | zero => simpa [simplexEmbInv] using hy.2
    | succ i => simpa [simplexEmbInv] using hy.1 i
  · rw [Fin.sum_univ_succ]
    simp [simplexEmbInv]

theorem simplexEmb_simplexEmbInv {y : EuclideanSpace ℝ (Fin j)} (hy : y ∈ simplexSet j) :
    simplexEmb ⟨simplexEmbInv y, simplexEmbInv_mem hy⟩ = y := by
  ext i
  simp [simplexEmb, simplexEmbInv]

theorem simplexSet_subset_range : simplexSet j ⊆ Set.range (simplexEmb (j := j)) :=
  fun _ hy => ⟨⟨_, simplexEmbInv_mem hy⟩, simplexEmb_simplexEmbInv hy⟩

/-- The standard `j`-simplex is homeomorphic to the corner simplex. -/
def simplexHomeoSet (j : ℕ) : stdSimplex ℝ (Fin (j + 1)) ≃ₜ simplexSet j :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun x => (⟨simplexEmb x, simplexEmb_mem x⟩ : simplexSet j))
      ⟨fun _ _ h => simplexEmb_injective (Subtype.ext_iff.1 h),
        fun y => by
          obtain ⟨x, hx⟩ := simplexSet_subset_range y.2
          exact ⟨x, Subtype.ext hx⟩⟩)
    (by exact continuous_induced_rng.2 continuous_simplexEmb)

@[simp]
theorem simplexHomeoSet_apply (x : stdSimplex ℝ (Fin (j + 1))) :
    (simplexHomeoSet j x : EuclideanSpace ℝ (Fin j)) = simplexEmb x := rfl

/-- A point of the standard simplex lies on the boundary — i.e. some barycentric coordinate
vanishes — exactly when its image lies on the frontier of the corner simplex. -/
theorem simplexEmb_mem_frontier_iff (x : stdSimplex ℝ (Fin (j + 1))) :
    simplexEmb x ∈ frontier (simplexSet j) ↔ ∃ i, x.1 i = 0 := by
  rw [isClosed_simplexSet.frontier_eq, mem_sdiff, interior_simplexSet_eq]
  constructor
  · rintro ⟨-, h⟩
    simp only [openSimplexSet, mem_setOf_eq, not_and_or, not_forall, not_lt] at h
    rcases h with ⟨i, hi⟩ | hi
    · exact ⟨i.succ, le_antisymm (by simpa using hi) (x.2.1 _)⟩
    · refine ⟨0, ?_⟩
      rw [simplexEmb_zero_coord]
      have := simplexEmb_mem x
      linarith [this.2]
  · rintro ⟨i, hi⟩
    refine ⟨simplexEmb_mem x, fun hmem => ?_⟩
    induction i using Fin.cases with
    | zero =>
      rw [simplexEmb_zero_coord] at hi
      have := hmem.2
      linarith
    | succ i =>
      have := hmem.1 i
      rw [simplexEmb_apply] at this
      linarith

/-! ### The simplex as the disk -/

private theorem exists_simplexToBall (j : ℕ) :
    ∃ h : EuclideanSpace ℝ (Fin j) ≃ₜ EuclideanSpace ℝ (Fin j),
      h '' simplexSet j = closedBall 0 1 ∧ h '' frontier (simplexSet j) = sphere 0 1 := by
  obtain ⟨h, -, h₂, h₃⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_simplexSet (j := j)) interior_simplexSet_nonempty isBounded_simplexSet
  exact ⟨h, by rwa [isClosed_simplexSet.closure_eq] at h₂, h₃⟩

/-- A self-homeomorphism of `ℝ^j` taking the corner simplex onto the closed unit ball and its
frontier onto the unit sphere. -/
def simplexToBall (j : ℕ) : EuclideanSpace ℝ (Fin j) ≃ₜ EuclideanSpace ℝ (Fin j) :=
  (exists_simplexToBall j).choose

theorem simplexToBall_image : simplexToBall j '' simplexSet j = closedBall 0 1 :=
  (exists_simplexToBall j).choose_spec.1

theorem simplexToBall_image_frontier :
    simplexToBall j '' frontier (simplexSet j) = sphere 0 1 :=
  (exists_simplexToBall j).choose_spec.2

/-- **The standard `j`-simplex is homeomorphic to the closed unit `j`-ball.** -/
def simplexHomeoBall (j : ℕ) :
    stdSimplex ℝ (Fin (j + 1)) ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin j)) 1 :=
  (simplexHomeoSet j).trans
    (((simplexToBall j).image (simplexSet j)).trans (Homeomorph.setCongr simplexToBall_image))

@[simp]
theorem simplexHomeoBall_apply (x : stdSimplex ℝ (Fin (j + 1))) :
    (simplexHomeoBall j x : EuclideanSpace ℝ (Fin j)) = simplexToBall j (simplexEmb x) := rfl

/-- **Under the identification of the simplex with the disk, the boundary of the simplex
corresponds to the unit sphere.** -/
theorem norm_simplexHomeoBall_eq_one_iff (x : stdSimplex ℝ (Fin (j + 1))) :
    ‖(simplexHomeoBall j x : EuclideanSpace ℝ (Fin j))‖ = 1 ↔ ∃ i, x.1 i = 0 := by
  rw [simplexHomeoBall_apply, ← simplexEmb_mem_frontier_iff]
  constructor
  · intro h
    have hmem : simplexToBall j (simplexEmb x) ∈ sphere (0 : EuclideanSpace ℝ (Fin j)) 1 :=
      mem_sphere_zero_iff_norm.mpr h
    rw [← simplexToBall_image_frontier] at hmem
    obtain ⟨z, hz, hz'⟩ := hmem
    rwa [(simplexToBall j).injective hz'] at hz
  · intro h
    have : simplexToBall j (simplexEmb x) ∈ sphere (0 : EuclideanSpace ℝ (Fin j)) 1 := by
      rw [← simplexToBall_image_frontier]; exact ⟨_, h, rfl⟩
    exact mem_sphere_zero_iff_norm.mp this

/-- **The topological `j`-simplex is homeomorphic to the `j`-disk `𝔻 j`.** -/
def simplexHomeoDisk (j : ℕ) :
    (SimplexCategory.toTop.{0}.obj ⦋j⦌ : TopCat.{0}) ≃ₜ (TopCat.disk.{0} j : TopCat.{0}) :=
  (Homeomorph.ulift).trans ((simplexHomeoBall j).trans Homeomorph.ulift.symm)

@[simp]
theorem simplexHomeoDisk_apply (x : SimplexCategory.toTop.{0}.obj ⦋j⦌) :
    ((simplexHomeoDisk j x).down : EuclideanSpace ℝ (Fin j)) =
      simplexToBall j (simplexEmb x.down) := rfl

/-- The boundary correspondence at the level of `TopCat`. -/
theorem norm_simplexHomeoDisk_eq_one_iff (x : SimplexCategory.toTop.{0}.obj ⦋j⦌) :
    ‖((simplexHomeoDisk j x).down : EuclideanSpace ℝ (Fin j))‖ = 1 ↔
      ∃ i, x.down.1 i = 0 :=
  norm_simplexHomeoBall_eq_one_iff x.down

end Submission
