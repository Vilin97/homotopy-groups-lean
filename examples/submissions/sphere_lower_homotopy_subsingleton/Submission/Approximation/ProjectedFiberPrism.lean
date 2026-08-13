/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.TwoPointCompression

/-!
# The vertical prism over a projected point fiber

For a map `g : I^(n+1) -> X` and a point `b : X`, take the projection of `g⁻¹(b)` onto the
first `n` coordinates and then restore the whole last-coordinate interval over that projection.
The resulting vertical prism is precisely the set used in the cubical proof of homotopy excision.

If `a` is absent from the image of this prism, then the projected `a`- and `b`-fibers are
disjoint.  If the side faces also avoid `b`, the boundary can be adjoined to the projected
`a`-fiber.  The Urysohn compression from `TwoPointCompression` then removes `b` while preserving
the `a`-fiber exactly throughout the homotopy.  This is the topological deduction that follows
the dimension-theoretic choice of `a` and `b` in the stable excision argument.

## Main results

* `Submission.cubeLastFiberProjection_disjoint_of_not_mem_prism_image`
* `Submission.cubeLastFiberProjection_union_boundary_disjoint`
* `Submission.exists_homotopicRel_boundaryJar_avoiding_second_preserving_firstFiber`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {n : ℕ}

/-- The full last-coordinate prism over a subset of the lower-dimensional cube. -/
def cubeLastPrism (s : Set (I^ Fin n)) : Set (I^ Fin (n + 1)) :=
  {y | (Cube.splitAtLast y).2 ∈ s}

@[simp] theorem mem_cubeLastPrism_iff (s : Set (I^ Fin n))
    (y : I^ Fin (n + 1)) :
    y ∈ cubeLastPrism s ↔ (Cube.splitAtLast y).2 ∈ s :=
  Iff.rfl

theorem cubeLastPrism_isClosed {s : Set (I^ Fin n)} (hs : IsClosed s) :
    IsClosed (cubeLastPrism s) := by
  exact hs.preimage (continuous_snd.comp Cube.splitAtLast.continuous)

theorem cubeLastPrism_isCompact {s : Set (I^ Fin n)} (hs : IsClosed s) :
    IsCompact (cubeLastPrism s) :=
  (cubeLastPrism_isClosed hs).isCompact

/-- The vertical prism over the projected fiber of `g` at `b`. -/
def cubeLastFiberPrism {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (b : X) : Set (I^ Fin (n + 1)) :=
  cubeLastPrism (cubeLastFiberProjection g b)

@[simp] theorem mem_cubeLastFiberPrism_iff {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (b : X) (y : I^ Fin (n + 1)) :
    y ∈ cubeLastFiberPrism g b ↔
      ∃ s : I, g (Cube.splitAtLast.symm (s, (Cube.splitAtLast y).2)) = b :=
  Iff.rfl

theorem cubeLastFiberPrism_isClosed {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (b : X) :
    IsClosed (cubeLastFiberPrism g b) :=
  cubeLastPrism_isClosed (cubeLastFiberProjection_isClosed g b)

theorem cubeLastFiberPrism_isCompact {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (b : X) :
    IsCompact (cubeLastFiberPrism g b) :=
  (cubeLastFiberPrism_isClosed g b).isCompact

/-- If `a` is missed by the image of the vertical prism over the projected `b`-fiber, the two
projected fibers are disjoint. -/
theorem cubeLastFiberProjection_disjoint_of_not_mem_prism_image
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (ha : a ∉ g '' cubeLastFiberPrism g b) :
    Disjoint (cubeLastFiberProjection g a) (cubeLastFiberProjection g b) := by
  rw [Set.disjoint_left]
  intro r hra hrb
  obtain ⟨sa, hsa⟩ := hra
  apply ha
  refine ⟨Cube.splitAtLast.symm (sa, r), ?_, hsa⟩
  simpa [cubeLastFiberPrism, cubeLastPrism] using hrb

/-- Avoidance of `b` on the side faces says that its projected fiber misses the boundary of the
lower-dimensional cube. -/
theorem cubeBoundary_disjoint_cubeLastFiberProjection
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (b : X)
    (hside : ∀ (r : I^ Fin n), r ∈ Cube.boundary (Fin n) →
      ∀ s : I, g (Cube.splitAtLast.symm (s, r)) ≠ b) :
    Disjoint (Cube.boundary (Fin n)) (cubeLastFiberProjection g b) := by
  rw [Set.disjoint_left]
  intro r hrboundary hrb
  obtain ⟨s, hs⟩ := hrb
  exact hside r hrboundary s hs

/-- The prism and side-face hypotheses give exactly the disjoint closed sets required by the
Urysohn compression. -/
theorem cubeLastFiberProjection_union_boundary_disjoint
    {X : Type*} [TopologicalSpace X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (ha : a ∉ g '' cubeLastFiberPrism g b)
    (hside : ∀ (r : I^ Fin n), r ∈ Cube.boundary (Fin n) →
      ∀ s : I, g (Cube.splitAtLast.symm (s, r)) ≠ b) :
    Disjoint
      (cubeLastFiberProjection g a ∪ Cube.boundary (Fin n))
      (cubeLastFiberProjection g b) := by
  rw [Set.disjoint_left]
  intro r hr hrb
  rcases hr with hra | hrboundary
  · exact Set.disjoint_left.mp
      (cubeLastFiberProjection_disjoint_of_not_mem_prism_image g a b ha) hra hrb
  · exact Set.disjoint_left.mp
      (cubeBoundary_disjoint_cubeLastFiberProjection g b hside) hrboundary hrb

/-- The topological core of the two-cell compression argument.  Missing `a` on the prism over
the projected `b`-fiber, avoiding `b` on the side and bottom faces, and compactness of the cube
produce a jar-relative deformation whose endpoint avoids `b`.  At every intermediate time the
preimage of `a` is exactly the original preimage, so any source face that initially maps into
`X \ {a}` continues to do so. -/
theorem exists_homotopicRel_boundaryJar_avoiding_second_preserving_firstFiber
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a b : X)
    (ha : a ∉ g '' cubeLastFiberPrism g b)
    (hside : ∀ (r : I^ Fin n), r ∈ Cube.boundary (Fin n) →
      ∀ s : I, g (Cube.splitAtLast.symm (s, r)) ≠ b)
    (hbot : ∀ r : I^ Fin n, g (Cube.splitAtLast.symm (0, r)) ≠ b) :
    ∃ g' : C(I^ Fin (n + 1), X),
      ∃ H : ContinuousMap.HomotopyRel g g' (⊔I^(n + 1)),
        (∀ t y, H.toHomotopy (t, y) = a ↔ g y = a) ∧
        ∀ y, g' y ≠ b := by
  have hdisj := cubeLastFiberProjection_union_boundary_disjoint g a b ha hside
  obtain ⟨v, hva, hvboundary, hvb⟩ :=
    exists_cubeLastFiberSeparator g a b hdisj
  let H := cubeLastCompressedMapHomotopyRelBoundaryJar g v hvboundary
  refine ⟨cubeLastCompressedMap g v, H, ?_,
    cubeLastCompressedMap_avoids_of_selector g v b hvb hbot⟩
  intro t y
  exact cubeLastCompression_image_eq_iff g v a hva t y

/-- A source subset which initially avoids `a` continues to avoid it during the prism
compression. -/
theorem exists_homotopicRel_boundaryJar_avoiding_on_protectedSet
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (g : C(I^ Fin (n + 1), X)) (a b : X) (S : Set (I^ Fin (n + 1)))
    (ha : a ∉ g '' cubeLastFiberPrism g b)
    (hside : ∀ (r : I^ Fin n), r ∈ Cube.boundary (Fin n) →
      ∀ s : I, g (Cube.splitAtLast.symm (s, r)) ≠ b)
    (hbot : ∀ r : I^ Fin n, g (Cube.splitAtLast.symm (0, r)) ≠ b)
    (hS : ∀ y ∈ S, g y ≠ a) :
    ∃ g' : C(I^ Fin (n + 1), X),
      ∃ H : ContinuousMap.HomotopyRel g g' (⊔I^(n + 1)),
        (∀ t y, y ∈ S → H.toHomotopy (t, y) ≠ a) ∧
        ∀ y, g' y ≠ b := by
  obtain ⟨g', H, hpreserve, hb⟩ :=
    exists_homotopicRel_boundaryJar_avoiding_second_preserving_firstFiber
      g a b ha hside hbot
  refine ⟨g', H, ?_, hb⟩
  intro t y hy hya
  exact hS y hy ((hpreserve t y).mp hya)

end Submission
