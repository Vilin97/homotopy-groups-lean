/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Pair
import Submission.Cohomology.Sphere
import Submission.WhiteheadTheorem.Shapes.Disk

/-!
# Cohomology of a disk relative to its boundary

The boundary of the `(n+1)`-disk is the universe-lift of the metric `n`-sphere used throughout
this development.  Together with contractibility of the disk and the long exact sequence of a
pair, this shows that relative cohomology vanishes in every degree between `2` and the top degree.

## Main results

* `Submission.diskBoundaryHomeoSph` -- `∂Dⁿ⁺¹` is homeomorphic to the metric `n`-sphere;
* `Submission.contractibleSpace_disk` -- every standard disk is contractible;
* `Submission.isZero_HrelCoh_diskBoundaryIncl` -- relative disk cohomology vanishes away from
  its top positive degree.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-- The boundary of the `(n+1)`-disk is the universe-lift of the metric `n`-sphere. -/
def diskBoundaryHomeoSph (n : ℕ) :
    (TopCat.diskBoundary.{0} (n + 1) : Type) ≃ₜ Sph n :=
  Homeomorph.ulift

/-- Every standard finite-dimensional disk is contractible. -/
theorem contractibleSpace_disk (d : ℕ) : ContractibleSpace (TopCat.disk.{0} d) := by
  letI : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  exact Homeomorph.ulift.contractibleSpace

variable (R : Type) [CommRing R]

/-- Cohomology of a disk boundary agrees with cohomology of the corresponding metric sphere. -/
def hsingDiskBoundaryEquiv (n k : ℕ) :
    Hsing k (TopCat.of (Sph n)) R ≃+ Hsing k (TopCat.diskBoundary (n + 1)) R := by
  let e := (diskBoundaryHomeoSph n).toHomotopyEquiv
  exact (hsingLinearEquivOfHomotopyEquiv
    (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some e.right_inv.some k).toAddEquiv

/-- Positive cohomology of a disk boundary vanishes away from its sphere dimension. -/
theorem subsingleton_Hsing_diskBoundary (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    Subsingleton (Hsing k (TopCat.diskBoundary (n + 1)) R) := by
  let e := hsingDiskBoundaryEquiv R n k
  letI : Subsingleton (Hsing k (TopCat.of (Sph n)) R) :=
    subsingleton_Hsing_sphere R k n hk hkn
  exact ⟨fun a b ↦ e.symm.injective
    (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-- Relative cohomology of `(Dⁿ⁺¹, ∂Dⁿ⁺¹)` vanishes in degree `k+1` whenever
`k` is positive and is not the boundary dimension `n`. -/
theorem isZero_HrelCoh_diskBoundaryIncl (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (HrelCoh (TopCat.diskBoundaryIncl.{0} (n + 1))
      (AddCommGrpCat.of R) (k + 1)) := by
  letI : ContractibleSpace (TopCat.disk.{0} (n + 1)) :=
    contractibleSpace_disk (n + 1)
  letI : Subsingleton (Hsing k (TopCat.diskBoundary (n + 1)) R) :=
    subsingleton_Hsing_diskBoundary R n k hk hkn
  exact isZero_HrelCoh_of_isZero_subspace_of_isZero_space
    (TopCat.diskBoundaryIncl.{0} (n + 1)) (AddCommGrpCat.of R) k
    (isZero_dualHomology_of_subsingleton_Hsing R k)
    (isZero_dualHomology_of_contractible R (k + 1) (by omega))

end Submission
