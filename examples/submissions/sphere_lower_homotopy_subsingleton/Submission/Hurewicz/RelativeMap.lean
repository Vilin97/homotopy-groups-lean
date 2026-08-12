/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.RelMap
import Submission.WhiteheadTheorem.Shapes.Cube

/-!
# The relative homology class carried by a relative cubical loop

A relative generalized loop of dimension `n + 1` is a map of pairs

`(I^(n+1), boundary I^(n+1)) ⟶ (X, A)`.

It therefore sends every relative homology class of the cube pair to a class in `H_*(X,A)`.
This file packages that map of pairs, proves the induced homology map depends only on the relative
homotopy class, and proves naturality under postcomposition by based maps of pairs. Choosing the
oriented top class of the cube pair will turn this evaluator into the relative Hurewicz map.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The all-zero vertex, regarded as the basepoint of the boundary of a positive-dimensional
cube. -/
def cubeBoundaryBase (n : ℕ) : ∂I^(n + 1) :=
  ⟨0, Cube.boundaryJar_subset_boundary _
    (Cube.mem_boundaryJar_of_exists_eq_zero 0 ⟨0, rfl⟩)⟩

namespace RelGenLoop

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y} {a : A} {b : B}

/-- A relative cubical loop, regarded as a based map from the cube/boundary pair. -/
def pairMap (p : RelGenLoop (n + 1) X A a) :
    BasedPairMap (∂I^(n + 1)) A (cubeBoundaryBase n) a where
  toContinuousMap := p.val
  mapsTo' y hy := p.property.1 y hy
  map_basepoint' := p.property.2 0
    (Cube.mem_boundaryJar_of_exists_eq_zero 0 ⟨0, rfl⟩)

@[simp]
theorem pairMap_toContinuousMap (p : RelGenLoop (n + 1) X A a) :
    (pairMap p).toContinuousMap = p.val :=
  rfl

/-- The relative homology map induced by a relative cubical loop. -/
def hrelMap (degree : ℕ) (p : RelGenLoop (n + 1) X A a) :
    HrelSet (Y := TopCat.of (I^Fin (n + 1))) degree (∂I^(n + 1)) ⟶
      HrelSet (Y := TopCat.of X) degree A :=
  BasedPairMap.hrelMap degree (pairMap p)

/-- Relatively homotopic cubical loops induce the same map on relative singular homology. -/
theorem hrelMap_eq_of_homotopic {p q : RelGenLoop (n + 1) X A a}
    (H : RelGenLoop.Homotopic p q) (degree : ℕ) :
    hrelMap degree p = hrelMap degree q := by
  obtain ⟨H⟩ := H
  let sub : TopCat.Homotopy (pairMap p).subspaceHom (pairMap q).subspaceHom :=
    { toFun := fun ty => ⟨H (ty.1, ty.2.1), (H.prop ty.1).1 ty.2.1 ty.2.2⟩
      continuous_toFun := Continuous.subtype_mk
        (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
      map_zero_left := fun y => Subtype.ext (H.map_zero_left y.1)
      map_one_left := fun y => Subtype.ext (H.map_one_left y.1) }
  exact HrelMap_congr
    (pairMap p).subIncl_naturality (pairMap q).subIncl_naturality
    (PairHomotopy.ofPointwise
      (pairMap p).subIncl_naturality (pairMap q).subIncl_naturality
      sub H.toHomotopy (fun _ _ => rfl)) degree

/-- Postcomposition of a relative loop agrees with composition of its based pair map. -/
theorem pairMap_map (f : BasedPairMap A B a b) (p : RelGenLoop (n + 1) X A a) :
    f.comp (pairMap p) = pairMap (map f p) := by
  cases f
  rfl

/-- The relative homology maps carried by relative loops respect postcomposition. -/
theorem hrelMap_comp (f : BasedPairMap A B a b) (p : RelGenLoop (n + 1) X A a)
    (degree : ℕ) :
    hrelMap degree p ≫ f.hrelMap degree = hrelMap degree (map f p) := by
  rw [hrelMap, hrelMap, BasedPairMap.hrelMap_comp, pairMap_map]

end RelGenLoop

namespace RelHomotopyGroup

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y} {a : A} {b : B}

/-- Evaluation of a relative homotopy class on a chosen relative homology class of the cube pair.
The construction is independent of the representative. -/
def homologyEval (degree : ℕ)
    (u : HrelSet (Y := TopCat.of (I^Fin (n + 1))) degree (∂I^(n + 1))) :
    π_rel (n + 1) X A a → HrelSet (Y := TopCat.of X) degree A :=
  Quotient.lift (fun p => RelGenLoop.hrelMap degree p u) fun _ _ H =>
    ConcreteCategory.congr_hom (RelGenLoop.hrelMap_eq_of_homotopic H degree) u

@[simp]
theorem homologyEval_mk (degree : ℕ)
    (u : HrelSet (Y := TopCat.of (I^Fin (n + 1))) degree (∂I^(n + 1)))
    (p : RelGenLoop (n + 1) X A a) :
    homologyEval degree u ⟦p⟧ = RelGenLoop.hrelMap degree p u :=
  rfl

/-- Naturality of relative-homology evaluation under a based map of pairs. -/
theorem homologyEval_naturality (f : BasedPairMap A B a b) (degree : ℕ)
    (u : HrelSet (Y := TopCat.of (I^Fin (n + 1))) degree (∂I^(n + 1)))
    (x : π_rel (n + 1) X A a) :
    f.hrelMap degree (homologyEval degree u x) =
      homologyEval degree u (map f x) := by
  refine Quotient.inductionOn x ?_
  intro p
  rw [homologyEval_mk, map_mk, homologyEval_mk]
  exact ConcreteCategory.congr_hom (RelGenLoop.hrelMap_comp f p degree) u

end RelHomotopyGroup

end Submission
