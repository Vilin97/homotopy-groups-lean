/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfMappingCone
import Submission.Hurewicz.SphereDiagonal
import Submission.SphereSuspension
import Submission.Topology.PuppeHomotopyGroups

/-!
# Homotopy groups of the second Hopf mapping cone

The second mapping cone in the Puppe sequence of the quadratic Hopf map is homotopy equivalent
to the suspension of its target sphere, hence to `S³`.  This file packages that concrete
equivalence and its first homotopy-group consequences at every basepoint.
-/

open CategoryTheory
open scoped ContinuousMap Topology Topology.Homotopy TopCat
open HomotopyGroups

noncomputable section

namespace Submission

/-- The second mapping cone in the Puppe sequence of the quadratic Hopf map. -/
noncomputable abbrev hopfSecondMappingCone : TopCat.{0} :=
  topologicalMappingCone (topologicalMappingConeCollapse hopfTopCat)

/-- The chosen homeomorphism from the topological suspension of `S²` to `S³`. -/
noncomputable def topologicalSuspensionSphereTwoHomeomorphSphereThree :
    topologicalSuspension (TopCat.of (Sph 2)) ≃ₜ Sph 3 :=
  TopCat.homeoOfIso
    ((topologicalSuspensionIsoSusp (TopCat.of (Sph 2))).trans
      (suspSphTopCatIso 2))

/-- The second Hopf mapping cone is homotopy equivalent to `S³`.  Its forward map is the
canonical second Puppe comparison followed by the chosen suspension-sphere homeomorphism. -/
noncomputable def hopfSecondMappingConeHomotopyEquivSphereThree :
    hopfSecondMappingCone ≃ₕ Sph 3 :=
  (topologicalSecondMappingConeHomotopyEquivSuspension hopfTopCat).trans
    topologicalSuspensionSphereTwoHomeomorphSphereThree.toHomotopyEquiv

/-- The second Hopf mapping cone is path connected. -/
theorem pathConnectedSpace_hopfSecondMappingCone :
    PathConnectedSpace hopfSecondMappingCone := by
  letI : PathConnectedSpace (Sph 3) := pathConnectedSpace_sph (by omega)
  exact pathConnectedSpace_of_homotopyEquiv
    hopfSecondMappingConeHomotopyEquivSphereThree

/-- At every basepoint, the homotopy groups of the second Hopf mapping cone agree with those of
`S³` at the image basepoint. -/
noncomputable def hopfSecondMappingConeHomotopyGroupMulEquivSphereThreeAt
    (N : Type*) [Fintype N] [Nonempty N] [DecidableEq N]
    (c : hopfSecondMappingCone) :
    HomotopyGroup N hopfSecondMappingCone c ≃*
      HomotopyGroup N (Sph 3)
        (hopfSecondMappingConeHomotopyEquivSphereThree c) :=
  homotopyGroupMulEquivOfHomotopyEquiv
    hopfSecondMappingConeHomotopyEquivSphereThree c

/-- The set of path components of the second Hopf mapping cone is trivial at every
basepoint. -/
theorem piZero_hopfSecondMappingCone_subsingleton_at
    (c : hopfSecondMappingCone) :
    Subsingleton (π_ 0 hopfSecondMappingCone c) := by
  letI : PathConnectedSpace hopfSecondMappingCone :=
    pathConnectedSpace_hopfSecondMappingCone
  exact subsingleton_piZero c

/-- The fundamental group of the second Hopf mapping cone vanishes at every basepoint. -/
theorem piOne_hopfSecondMappingCone_subsingleton_at
    (c : hopfSecondMappingCone) :
    Subsingleton (π_ 1 hopfSecondMappingCone c) := by
  let e := hopfSecondMappingConeHomotopyGroupMulEquivSphereThreeAt (Fin 1) c
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 1 3 (by omega)
      (hopfSecondMappingConeHomotopyEquivSphereThree c))

/-- The second homotopy group of the second Hopf mapping cone vanishes at every basepoint. -/
theorem piTwo_hopfSecondMappingCone_subsingleton_at
    (c : hopfSecondMappingCone) :
    Subsingleton (π_ 2 hopfSecondMappingCone c) := by
  let e := hopfSecondMappingConeHomotopyGroupMulEquivSphereThreeAt (Fin 2) c
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 2 3 (by omega)
      (hopfSecondMappingConeHomotopyEquivSphereThree c))

/-- The third homotopy group of the second Hopf mapping cone is infinite cyclic at every
basepoint. -/
noncomputable def piThree_hopfSecondMappingCone_mulEquiv_int_at
    (c : hopfSecondMappingCone) :
    π_ 3 hopfSecondMappingCone c ≃* Multiplicative ℤ :=
  (hopfSecondMappingConeHomotopyGroupMulEquivSphereThreeAt (Fin 3) c).trans
    (Classical.choice
      (sphere_diagonal_sph_at_mulEquiv_int 2
        (hopfSecondMappingConeHomotopyEquivSphereThree c)))

end Submission
