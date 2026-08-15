/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineCofiber

/-!
# Homotopy groups of the projective-line cofiber

The literal quotient `CP²/CP¹` is homeomorphic to the metric four-sphere.  This file chooses the
basepoint transported from the sphere coordinate and records the resulting homotopy groups:
the quotient is path connected, its positive homotopy groups below degree four vanish, and its
fourth homotopy group is infinite cyclic.
-/

open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- The literal quotient obtained by collapsing the embedded projective line in geometric
`CP²`. -/
abbrev complexProjectivePlaneQuotientProjectiveLine :=
  Quotient complexProjectivePlaneProjectiveLineSetoid

/-- The quotient basepoint corresponding to the maintained basepoint of the metric
four-sphere. -/
noncomputable def complexProjectivePlaneQuotientProjectiveLineBasepoint :
    complexProjectivePlaneQuotientProjectiveLine :=
  complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour.symm
    (sphereBasepoint 4)

@[simp]
theorem complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour_basepoint :
    complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour
        complexProjectivePlaneQuotientProjectiveLineBasepoint =
      sphereBasepoint 4 :=
  complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour.apply_symm_apply _

/-- The projective-line cofiber is path connected. -/
noncomputable instance complexProjectivePlaneQuotientProjectiveLinePathConnectedSpace :
    PathConnectedSpace complexProjectivePlaneQuotientProjectiveLine := by
  letI : PathConnectedSpace (Sph 4) := pathConnectedSpace_sph (by omega)
  exact
    complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour.symm.surjective
      |>.pathConnectedSpace
        complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour.symm.continuous

/-- Every positive-dimensional homotopy group of the projective-line cofiber is transported
exactly to the corresponding metric-four-sphere group. -/
noncomputable def
    complexProjectivePlaneQuotientProjectiveLineHomotopyGroupMulEquivSphereFour
    (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N] :
    HomotopyGroup N complexProjectivePlaneQuotientProjectiveLine
        complexProjectivePlaneQuotientProjectiveLineBasepoint ≃*
      HomotopyGroup N (Sph 4) (sphereBasepoint 4) :=
  HomotopyGroup.homeomorphMulEquivOfEq
    complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour
    complexProjectivePlaneQuotientProjectiveLineHomeomorphSphereFour_basepoint

/-- The set of path components of the projective-line cofiber is trivial. -/
theorem piZero_complexProjectivePlaneQuotientProjectiveLine_subsingleton :
    Subsingleton
      (π_ 0 complexProjectivePlaneQuotientProjectiveLine
        complexProjectivePlaneQuotientProjectiveLineBasepoint) :=
  subsingleton_piZero complexProjectivePlaneQuotientProjectiveLineBasepoint

/-- Every positive homotopy group of the projective-line cofiber below degree four is
trivial. -/
theorem piLower_complexProjectivePlaneQuotientProjectiveLine_subsingleton
    (k : ℕ) (hk : k + 1 < 4) :
    Subsingleton
      (π_ (k + 1) complexProjectivePlaneQuotientProjectiveLine
        complexProjectivePlaneQuotientProjectiveLineBasepoint) := by
  let e :=
    complexProjectivePlaneQuotientProjectiveLineHomotopyGroupMulEquivSphereFour
      (Fin (k + 1))
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt (k + 1) 4 hk
      (sphereBasepoint 4))

/-- The fourth homotopy group of the projective-line cofiber is infinite cyclic. -/
noncomputable def complexProjectivePlaneQuotientProjectiveLinePiFourMulEquivInt :
    π_ 4 complexProjectivePlaneQuotientProjectiveLine
        complexProjectivePlaneQuotientProjectiveLineBasepoint ≃*
      Multiplicative ℤ :=
  (complexProjectivePlaneQuotientProjectiveLineHomotopyGroupMulEquivSphereFour
      (Fin 4)).trans
    (Classical.choice
      (sphere_diagonal_sph_at_mulEquiv_int 3 (sphereBasepoint 4)))

/-- The fourth homotopy group of the projective-line cofiber is infinite. -/
theorem complexProjectivePlaneQuotientProjectiveLine_piFour_infinite :
    Infinite
      (π_ 4 complexProjectivePlaneQuotientProjectiveLine
        complexProjectivePlaneQuotientProjectiveLineBasepoint) := by
  let e := complexProjectivePlaneQuotientProjectiveLinePiFourMulEquivInt
  exact Infinite.of_injective e.symm e.symm.injective

end Submission
