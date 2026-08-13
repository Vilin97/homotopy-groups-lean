/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Topology.UrysohnsLemma
import Submission.WhiteheadTheorem.Shapes.Cube

/-!
# Last-coordinate compression between two projected fibers

The cubical proof of homotopy excision separates the projections of two point fibers in an
`(n+1)`-cube and then compresses its last coordinate.  If `v : I^n -> I` is zero on the first
projected fiber and one on the second, the deformation is

`(s, r) |-> (s * (1 - t * v r), r)`.

At its endpoint it fixes the first fiber and pushes every vertical line over the second fiber
into the bottom face.  Requiring `v = 0` on `boundary (I^n)` makes the entire boundary jar fixed.
This file packages that deformation, the required Urysohn separator, compactness of projected
point fibers, and the resulting two-point avoidance lemma.

## Main results

* `Submission.cubeLastCompressionHomotopy`
* `Submission.exists_cubeUrysohnSeparator`
* `Submission.cubeLastFiberProjection_isClosed`
* `Submission.exists_cubeLastFiberSeparator`
* `Submission.cubeLastCompressedMap_avoids_of_selector`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {n : ℕ}

/-- Compress the last coordinate of an `(n+1)`-cube according to a control function on the
remaining `n` coordinates. -/
def cubeLastCompression (v : C(I^ Fin n, I)) :
    C(I × (I^ Fin (n + 1)), I^ Fin (n + 1)) where
  toFun p := Cube.splitAtLast.symm
    ((Cube.splitAtLast p.2).1 * σ (p.1 * v (Cube.splitAtLast p.2).2),
      (Cube.splitAtLast p.2).2)
  continuous_toFun := by fun_prop

@[simp] theorem cubeLastCompression_splitAtLast
    (v : C(I^ Fin n, I)) (t : I) (y : I^ Fin (n + 1)) :
    Cube.splitAtLast (cubeLastCompression v (t, y)) =
      ((Cube.splitAtLast y).1 * σ (t * v (Cube.splitAtLast y).2),
        (Cube.splitAtLast y).2) := by
  simp [cubeLastCompression]

@[simp] theorem cubeLastCompression_zero
    (v : C(I^ Fin n, I)) (y : I^ Fin (n + 1)) :
    cubeLastCompression v (0, y) = y := by
  apply Cube.splitAtLast.injective
  simp

theorem cubeLastCompression_eq_of_v_eq_zero
    (v : C(I^ Fin n, I)) (t : I) (y : I^ Fin (n + 1))
    (hv : v (Cube.splitAtLast y).2 = 0) :
    cubeLastCompression v (t, y) = y := by
  apply Cube.splitAtLast.injective
  simp [hv]

theorem cubeLastCompression_one_eq_bot_of_v_eq_one
    (v : C(I^ Fin n, I)) (y : I^ Fin (n + 1))
    (hv : v (Cube.splitAtLast y).2 = 1) :
    cubeLastCompression v (1, y) =
      Cube.splitAtLast.symm (0, (Cube.splitAtLast y).2) := by
  apply Cube.splitAtLast.injective
  simp [hv]

theorem cubeLastCompression_mem_boundaryJar
    (v : C(I^ Fin n, I)) (t : I) {y : I^ Fin (n + 1)}
    (hy : y ∈ (⊔I^(n + 1))) :
    cubeLastCompression v (t, y) ∈ (⊔I^(n + 1)) := by
  rw [Cube.mem_boundaryJar_iff_splitAtLast] at hy ⊢
  simp only [cubeLastCompression_splitAtLast]
  rcases hy with hbot | hside
  · left
    simp [hbot]
  · exact Or.inr hside

/-- The endpoint of `cubeLastCompression`. -/
def cubeLastCompressionEnd (v : C(I^ Fin n, I)) :
    C(I^ Fin (n + 1), I^ Fin (n + 1)) where
  toFun y := cubeLastCompression v (1, y)
  continuous_toFun := (cubeLastCompression v).continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem cubeLastCompressionEnd_apply
    (v : C(I^ Fin n, I)) (y : I^ Fin (n + 1)) :
    cubeLastCompressionEnd v y = cubeLastCompression v (1, y) :=
  rfl

/-- The last-coordinate deformation, viewed as a homotopy from the identity to its endpoint. -/
def cubeLastCompressionHomotopy (v : C(I^ Fin n, I)) :
    ContinuousMap.Homotopy (ContinuousMap.id (I^ Fin (n + 1)))
      (cubeLastCompressionEnd v) where
  toFun := cubeLastCompression v
  continuous_toFun := (cubeLastCompression v).continuous
  map_zero_left := cubeLastCompression_zero v
  map_one_left _ := rfl

/-- Precompose a map with the endpoint of the last-coordinate compression. -/
def cubeLastCompressedMap {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) :
    C(I^ Fin (n + 1), X) :=
  g.comp (cubeLastCompressionEnd v)

@[simp] theorem cubeLastCompressedMap_apply {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I))
    (y : I^ Fin (n + 1)) :
    cubeLastCompressedMap g v y = g (cubeLastCompression v (1, y)) :=
  rfl

/-- Precomposition with the compression is homotopic to the original map. -/
def cubeLastCompressedMapHomotopy {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) :
    ContinuousMap.Homotopy g (cubeLastCompressedMap g v) where
  toFun p := g (cubeLastCompression v p)
  continuous_toFun := g.continuous.comp (cubeLastCompression v).continuous
  map_zero_left y := by simp
  map_one_left _ := rfl

/-- The boundary of a finite-dimensional cube is closed. -/
theorem isClosed_cubeBoundary (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  have hrepr : Cube.boundary (Fin n) =
      ⋃ i : Fin n, ({y : I^ Fin n | y i = 0} ∪ {y : I^ Fin n | y i = 1}) := by
    ext y
    simp [Cube.boundary]
  rw [hrepr]
  apply isClosed_iUnion_of_finite
  intro i
  exact (isClosed_eq (continuous_apply i) continuous_const).union
    (isClosed_eq (continuous_apply i) continuous_const)

/-- Urysohn's lemma bundled with codomain the unit interval. -/
theorem exists_cubeUrysohnSeparator
    {s t : Set (I^ Fin n)} (hs : IsClosed s) (ht : IsClosed t)
    (hdisj : Disjoint s t) :
    ∃ v : C(I^ Fin n, I), Set.EqOn v 0 s ∧ Set.EqOn v 1 t := by
  obtain ⟨f, hfs, hft, hf⟩ :=
    exists_continuous_zero_one_of_isClosed hs ht hdisj
  refine ⟨⟨fun y => ⟨f y, hf y⟩, f.continuous.subtype_mk _⟩, ?_, ?_⟩
  · intro y hy
    exact Subtype.ext (hfs hy)
  · intro y hy
    exact Subtype.ext (hft hy)

/-- A separator that is additionally zero on the boundary of the cube. -/
theorem exists_cubeUrysohnSeparator_zero_on_boundary
    {s t : Set (I^ Fin n)} (hs : IsClosed s) (ht : IsClosed t)
    (hdisj : Disjoint (s ∪ Cube.boundary (Fin n)) t) :
    ∃ v : C(I^ Fin n, I),
      Set.EqOn v 0 s ∧ Set.EqOn v 0 (Cube.boundary (Fin n)) ∧
        Set.EqOn v 1 t := by
  obtain ⟨v, hvzero, hvone⟩ := exists_cubeUrysohnSeparator
    (hs.union (isClosed_cubeBoundary n)) ht hdisj
  exact ⟨v, fun y hy => hvzero (Or.inl hy),
    fun y hy => hvzero (Or.inr hy), hvone⟩

/-- Projection to `I^n` of the fiber over `a` along the last coordinate of an `(n+1)`-cube. -/
def cubeLastFiberProjection {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (a : X) : Set (I^ Fin n) :=
  {r | ∃ s : I, g (Cube.splitAtLast.symm (s, r)) = a}

theorem mem_cubeLastFiberProjection_iff {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (a : X) (r : I^ Fin n) :
    r ∈ cubeLastFiberProjection g a ↔
      ∃ s : I, g (Cube.splitAtLast.symm (s, r)) = a :=
  Iff.rfl

/-- If the selector vanishes on the projected `a`-fiber, every point which the deformation sends
into that fiber was fixed by the deformation. -/
theorem cubeLastCompression_eq_of_image_eq
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) (a : X)
    (hv : Set.EqOn v 0 (cubeLastFiberProjection g a))
    (t : I) (y : I^ Fin (n + 1))
    (ha : g (cubeLastCompression v (t, y)) = a) :
    cubeLastCompression v (t, y) = y := by
  have hr : (Cube.splitAtLast y).2 ∈ cubeLastFiberProjection g a := by
    refine ⟨(Cube.splitAtLast (cubeLastCompression v (t, y))).1, ?_⟩
    simpa [cubeLastCompression] using ha
  exact cubeLastCompression_eq_of_v_eq_zero v t y (hv hr)

/-- Vanishing on the projected `a`-fiber makes the deformation preserve that fiber exactly, at
every time. -/
theorem cubeLastCompression_image_eq_iff
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) (a : X)
    (hv : Set.EqOn v 0 (cubeLastFiberProjection g a))
    (t : I) (y : I^ Fin (n + 1)) :
    g (cubeLastCompression v (t, y)) = a ↔ g y = a := by
  constructor
  · intro ha
    rw [cubeLastCompression_eq_of_image_eq g v a hv t y ha] at ha
    exact ha
  · intro ha
    have hr : (Cube.splitAtLast y).2 ∈ cubeLastFiberProjection g a := by
      refine ⟨(Cube.splitAtLast y).1, ?_⟩
      simpa using ha
    rw [cubeLastCompression_eq_of_v_eq_zero v t y (hv hr)]
    exact ha

/-- Projected point fibers are compact: they are projections of closed subsets of a compact
product cube. -/
theorem cubeLastFiberProjection_isCompact {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a : X) :
    IsCompact (cubeLastFiberProjection g a) := by
  let g' : C(I × (I^ Fin n), X) :=
    g.comp ⟨Cube.splitAtLast.symm, Cube.splitAtLast.symm.continuous⟩
  have hfiber : IsClosed (g' ⁻¹' {a}) :=
    isClosed_singleton.preimage g'.continuous
  have himage : IsCompact (Prod.snd '' (g' ⁻¹' {a})) :=
    hfiber.isCompact.image continuous_snd
  have heq : Prod.snd '' (g' ⁻¹' {a}) = cubeLastFiberProjection g a := by
    ext r
    simp [g', cubeLastFiberProjection]
  rwa [heq] at himage

/-- Projected point fibers are closed in the lower-dimensional cube. -/
theorem cubeLastFiberProjection_isClosed {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a : X) :
    IsClosed (cubeLastFiberProjection g a) :=
  (cubeLastFiberProjection_isCompact g a).isClosed

/-- Disjoint projected fibers have a control function which is zero on the first fiber and the
cube boundary, and one on the second fiber. -/
theorem exists_cubeLastFiberSeparator {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (hdisj : Disjoint
      (cubeLastFiberProjection g a ∪ Cube.boundary (Fin n))
      (cubeLastFiberProjection g b)) :
    ∃ v : C(I^ Fin n, I),
      Set.EqOn v 0 (cubeLastFiberProjection g a) ∧
      Set.EqOn v 0 (Cube.boundary (Fin n)) ∧
      Set.EqOn v 1 (cubeLastFiberProjection g b) :=
  exists_cubeUrysohnSeparator_zero_on_boundary
    (cubeLastFiberProjection_isClosed g a)
    (cubeLastFiberProjection_isClosed g b) hdisj

/-- If the selector is zero on the lower-dimensional boundary, compression fixes the entire
boundary jar pointwise. -/
theorem cubeLastCompression_eq_of_mem_boundaryJar
    (v : C(I^ Fin n, I))
    (hv : Set.EqOn v 0 (Cube.boundary (Fin n)))
    (t : I) {y : I^ Fin (n + 1)} (hy : y ∈ (⊔I^(n + 1))) :
    cubeLastCompression v (t, y) = y := by
  rw [Cube.mem_boundaryJar_iff_splitAtLast] at hy
  rcases hy with hbot | hside
  · apply Cube.splitAtLast.injective
    rw [cubeLastCompression_splitAtLast]
    exact Prod.ext (by simp [hbot]) rfl
  · exact cubeLastCompression_eq_of_v_eq_zero v t y (hv hside)

/-- The compression homotopy is relative to the boundary jar when its selector vanishes on the
lower-dimensional boundary. -/
def cubeLastCompressedMapHomotopyRelBoundaryJar {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I))
    (hv : Set.EqOn v 0 (Cube.boundary (Fin n))) :
    ContinuousMap.HomotopyRel g (cubeLastCompressedMap g v) (⊔I^(n + 1)) where
  toHomotopy := cubeLastCompressedMapHomotopy g v
  prop' t _y hy := congrArg g (cubeLastCompression_eq_of_mem_boundaryJar v hv t hy)

/-- A selector which is one on the projected `b`-fiber pushes any putative `b`-preimage to the
bottom face.  Hence the compressed map avoids `b` whenever the original map avoids `b` there. -/
theorem cubeLastCompressedMap_avoids_of_selector {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) (b : X)
    (hv : Set.EqOn v 1 (cubeLastFiberProjection g b))
    (hbot : ∀ r : I^ Fin n, g (Cube.splitAtLast.symm (0, r)) ≠ b) :
    ∀ y, cubeLastCompressedMap g v y ≠ b := by
  intro y hy
  let r := (Cube.splitAtLast y).2
  change g (cubeLastCompression v (1, y)) = b at hy
  have hr : r ∈ cubeLastFiberProjection g b := by
    refine ⟨(Cube.splitAtLast (cubeLastCompression v (1, y))).1, ?_⟩
    simpa [r, cubeLastCompression] using hy
  have hvone : v (Cube.splitAtLast y).2 = 1 := hv hr
  exact hbot r <| (congrArg g
    (cubeLastCompression_one_eq_bot_of_v_eq_one v y hvone).symm).trans hy

/-- If the original map avoids `a` and the selector is zero on its projected fiber, compression
continues to avoid `a`. -/
theorem cubeLastCompressedMap_preserves_avoidance_of_selector
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (v : C(I^ Fin n, I)) (a : X)
    (hv : Set.EqOn v 0 (cubeLastFiberProjection g a))
    (ha : ∀ y, g y ≠ a) :
    ∀ y, cubeLastCompressedMap g v y ≠ a := by
  intro y hy
  let r := (Cube.splitAtLast y).2
  change g (cubeLastCompression v (1, y)) = a at hy
  have hr : r ∈ cubeLastFiberProjection g a := by
    refine ⟨(Cube.splitAtLast (cubeLastCompression v (1, y))).1, ?_⟩
    simpa [r, cubeLastCompression] using hy
  have hvzero : v (Cube.splitAtLast y).2 = 0 := hv hr
  rw [cubeLastCompression_eq_of_v_eq_zero v 1 y hvzero] at hy
  exact ha y hy

/-- The reusable two-point conclusion: under disjointness of the projected fibers, a map already
avoiding `a` can be deformed relative to the boundary jar to avoid both `a` and `b`, provided its
bottom face avoids `b`. -/
theorem exists_homotopicRel_boundaryJar_avoiding_two_points
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (hdisj : Disjoint
      (cubeLastFiberProjection g a ∪ Cube.boundary (Fin n))
      (cubeLastFiberProjection g b))
    (ha : ∀ y, g y ≠ a)
    (hbot : ∀ r : I^ Fin n, g (Cube.splitAtLast.symm (0, r)) ≠ b) :
    ∃ g' : C(I^ Fin (n + 1), X),
      ∃ _H : ContinuousMap.HomotopyRel g g' (⊔I^(n + 1)),
        (∀ y, g' y ≠ a) ∧ ∀ y, g' y ≠ b := by
  obtain ⟨v, hva, hvboundary, hvb⟩ :=
    exists_cubeLastFiberSeparator g a b hdisj
  refine ⟨cubeLastCompressedMap g v,
    cubeLastCompressedMapHomotopyRelBoundaryJar g v hvboundary,
    cubeLastCompressedMap_preserves_avoidance_of_selector g v a hva ha,
    cubeLastCompressedMap_avoids_of_selector g v b hvb hbot⟩

end Submission
