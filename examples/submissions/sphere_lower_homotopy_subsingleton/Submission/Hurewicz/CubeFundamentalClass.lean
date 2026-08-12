/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.RelativeMap
import Submission.Homology.SphereOne
import Submission.WhiteheadTheorem.Shapes.DiskHomeoCube

/-!
# The fundamental relative homology class of a cube

The boundary map for the contractible cube identifies

`H_{n+2}(I^{n+2}, ∂I^{n+2})`

with the top homology of its boundary.  The standard disk-to-cube homeomorphism identifies that
boundary with `S^{n+1}`, whose top integral homology has already been computed as `ℤ`.  Pulling back
`1 : ℤ` defines an oriented fundamental class of the cube pair.

Evaluating relative cubical homotopy classes on this fundamental class gives the relative
Hurewicz comparison map in every degree at least two.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- A finite-dimensional cube is contractible.  This version is kept local to the homological
development and follows from the standard disk-to-cube homeomorphism. -/
theorem contractibleSpace_cube (d : ℕ) : ContractibleSpace (I^Fin d) := by
  letI : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  letI : ContractibleSpace (TopCat.disk.{0} d) :=
    Homeomorph.ulift.contractibleSpace
  exact (TopCat.diskHomeoCube.{0} d).symm.contractibleSpace

/-- The boundary of the `(n+2)`-cube is homeomorphic to `S^{n+1}`. -/
noncomputable def cubeBoundaryHomeoSphere (n : ℕ) :
    (∂I^(n + 2)) ≃ₜ Sph (n + 1) :=
  (TopCat.diskBoundaryHomeoCubeBoundary.{0} (n + 2)).symm.trans Homeomorph.ulift

/-- The top homology of the boundary of the `(n+2)`-cube is `ℤ`. -/
noncomputable def cubeBoundaryTopHomologyIsoInt (n : ℕ) :
    Hgrp (n + 1) (TopCat.of (∂I^(n + 2))) ≅ AddCommGrpCat.of ℤ :=
  hgrpIsoOfIso (n + 1) (TopCat.isoOfHomeo (cubeBoundaryHomeoSphere n)) ≪≫
    hgrpSphereSelfIsoZ n

/-- For a contractible cube, the relative boundary map in top degree is an isomorphism. -/
noncomputable def cubePairRelativeBoundaryIso (n : ℕ) :
    HrelSet (Y := TopCat.of (I^Fin (n + 2))) (n + 2) (∂I^(n + 2)) ≅
      Hgrp (n + 1) (TopCat.of (∂I^(n + 2))) := by
  let i := subIncl (Y := TopCat.of (I^Fin (n + 2))) (∂I^(n + 2))
  letI : ContractibleSpace (I^Fin (n + 2)) := contractibleSpace_cube (n + 2)
  letI : IsIso (relδ (n + 1) i) :=
    isIso_relδ i (n + 1)
      (isZero_Hgrp_of_contractible (X := TopCat.of (I^Fin (n + 2))) (n + 1))
      (isZero_Hgrp_of_contractible (X := TopCat.of (I^Fin (n + 2))) n)
  exact asIso (relδ (n + 1) i)

/-- The top relative homology of the `(n+2)`-cube modulo its boundary is `ℤ`. -/
noncomputable def cubePairTopHomologyIsoInt (n : ℕ) :
    HrelSet (Y := TopCat.of (I^Fin (n + 2))) (n + 2) (∂I^(n + 2)) ≅
      AddCommGrpCat.of ℤ :=
  cubePairRelativeBoundaryIso n ≪≫ cubeBoundaryTopHomologyIsoInt n

/-- The oriented fundamental class of `(I^{n+2}, ∂I^{n+2})`, normalized to map to `1 ∈ ℤ`. -/
noncomputable def cubePairFundamentalClass (n : ℕ) :
    HrelSet (Y := TopCat.of (I^Fin (n + 2))) (n + 2) (∂I^(n + 2)) :=
  (cubePairTopHomologyIsoInt n).inv (1 : ℤ)

@[simp]
theorem cubePairTopHomologyIsoInt_fundamentalClass (n : ℕ) :
    (cubePairTopHomologyIsoInt n).hom (cubePairFundamentalClass n) = (1 : ℤ) := by
  simp [cubePairFundamentalClass]

/-- The relative Hurewicz comparison: evaluate a relative cubical homotopy class on the oriented
fundamental class of its source cube pair. -/
noncomputable def relativeHurewicz (n : ℕ) {X : Type} [TopologicalSpace X]
    (A : Set X) (a : A) :
    π_rel (n + 2) X A a → HrelSet (Y := TopCat.of X) (n + 2) A :=
  RelHomotopyGroup.homologyEval (n := n + 1) (n + 2) (cubePairFundamentalClass n)

@[simp]
theorem relativeHurewicz_mk (n : ℕ) {X : Type} [TopologicalSpace X]
    {A : Set X} {a : A} (p : RelGenLoop (n + 2) X A a) :
    relativeHurewicz n A a ⟦p⟧ =
      RelGenLoop.hrelMap (n + 2) p (cubePairFundamentalClass n) :=
  rfl

/-- The relative Hurewicz comparison is natural under based maps of pairs. -/
theorem relativeHurewicz_naturality (n : ℕ)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {a : A} {b : B}
    (f : BasedPairMap A B a b) (x : π_rel (n + 2) X A a) :
    f.hrelMap (n + 2) (relativeHurewicz n A a x) =
      relativeHurewicz n B b (RelHomotopyGroup.map f x) :=
  RelHomotopyGroup.homologyEval_naturality f (n + 2) (cubePairFundamentalClass n) x

end Submission
