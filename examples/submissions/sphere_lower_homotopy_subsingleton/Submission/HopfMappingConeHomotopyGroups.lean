/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCohomology
import Submission.Hurewicz.SphereDiagonal

/-!
# Homotopy groups of the Hopf mapping cone

The maintained geometric identification `CP^2 ≅ C_eta` transports the generalized complex Hopf
fibration calculations to the concrete quadratic Hopf mapping cone.  Thus its fundamental group
is trivial, its second homotopy group is infinite cyclic, and every homotopy group in degree at
least three agrees with that of `S^5`.  The low-dimensional consequences are recorded explicitly.
-/

open CategoryTheory
open scoped Topology TopCat
open HomotopyGroups

noncomputable section

namespace Submission

/-- The bottom-sphere basepoint of the concrete Hopf mapping cone. -/
noncomputable def hopfMappingConeBasepoint : hopfMappingCone :=
  hopfMappingConeIncl (sphereBasepoint 2)

/-- The geometric `CP^2`/Hopf-cone homeomorphism preserves the maintained basepoints. -/
@[simp]
theorem complexProjectivePlaneIsoHopfMappingCone_basepoint :
    complexProjectivePlaneIsoHopfMappingCone.hom
        (complexProjectiveModelBasepoint 2) =
      hopfMappingConeBasepoint := by
  rw [← complexProjectivePlaneBottomIncl_basepoint]
  change (complexProjectivePlaneBottomInclTopCat ≫
      complexProjectivePlaneIsoHopfMappingCone.hom)
        (complexProjectiveModelBasepoint 1) = _
  rw [complexProjectivePlaneIsoHopfMappingCone_hom_bottomIncl]
  change hopfMappingConeIncl
      (complexProjectiveLineHomeomorphSphere
        (complexProjectiveModelBasepoint 1)) = _
  rw [complexProjectiveLineHomeomorphSphere_basepoint]
  rfl

/-- The Hopf mapping cone has one path component. -/
theorem piZero_hopfMappingCone_subsingleton :
    Subsingleton (π_ 0 hopfMappingCone hopfMappingConeBasepoint) := by
  letI : PathConnectedSpace hopfMappingCone := pathConnectedSpace_hopfMappingCone
  exact subsingleton_piZero hopfMappingConeBasepoint

/-- The concrete Hopf mapping cone is simply connected. -/
theorem piOne_hopfMappingCone_subsingleton :
    Subsingleton (π_ 1 hopfMappingCone hopfMappingConeBasepoint) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 1)
    (TopCat.homeoOfIso complexProjectivePlaneIsoHopfMappingCone)
    complexProjectivePlaneIsoHopfMappingCone_basepoint
  exact e.toEquiv.subsingleton_congr.mp
    (piOne_complexProjectiveModel_subsingleton 2 (by omega))

/-- The second homotopy group of the concrete Hopf mapping cone is infinite cyclic. -/
noncomputable def piTwo_hopfMappingCone_mulEquiv_int :
    π_ 2 hopfMappingCone hopfMappingConeBasepoint ≃* Multiplicative ℤ :=
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 2)
    (TopCat.homeoOfIso complexProjectivePlaneIsoHopfMappingCone)
    complexProjectivePlaneIsoHopfMappingCone_basepoint
  e.symm.trans (Classical.choice
    (piTwo_complexProjectiveModel_mulEquiv_int 2 (by omega)))

/-- The second homotopy group of the Hopf mapping cone is nontrivial. -/
theorem piTwo_hopfMappingCone_not_subsingleton :
    ¬ Subsingleton (π_ 2 hopfMappingCone hopfMappingConeBasepoint) := by
  intro h
  have hZ : Subsingleton (Multiplicative ℤ) :=
    piTwo_hopfMappingCone_mulEquiv_int.toEquiv.subsingleton_congr.mp h
  have hz := hZ.elim (Multiplicative.ofAdd (0 : ℤ)) (Multiplicative.ofAdd (1 : ℤ))
  exact Int.zero_ne_one (congrArg Multiplicative.toAdd hz)

/-- In particular, the concrete Hopf mapping cone is not contractible. -/
theorem hopfMappingCone_not_contractible : ¬ ContractibleSpace hopfMappingCone := by
  intro h
  letI : ContractibleSpace hopfMappingCone := h
  exact piTwo_hopfMappingCone_not_subsingleton
    (subsingleton_homotopyGroup_of_contractible (N := Fin 2) hopfMappingConeBasepoint)

/-- In every degree at least three, the Hopf mapping cone has the homotopy group of `S^5`. -/
theorem hopfMappingCone_higher_homotopy_mulEquiv_sphereFive (k : ℕ) :
    Nonempty
      (π_ (k + 3) hopfMappingCone hopfMappingConeBasepoint ≃*
        π_ (k + 3) (Sph 5) (sphereBasepoint 5)) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (k + 3))
    (TopCat.homeoOfIso complexProjectivePlaneIsoHopfMappingCone)
    complexProjectivePlaneIsoHopfMappingCone_basepoint
  obtain ⟨h⟩ := complexProjectiveModel_higher_homotopy_mulEquiv_sphere 2 k (by omega)
  exact ⟨e.symm.trans (by simpa using h)⟩

/-- The third homotopy group of the Hopf mapping cone is trivial. -/
theorem piThree_hopfMappingCone_subsingleton :
    Subsingleton (π_ 3 hopfMappingCone hopfMappingConeBasepoint) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive 0
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 3 5 (by omega) (sphereBasepoint 5))

/-- The fourth homotopy group of the Hopf mapping cone is trivial. -/
theorem piFour_hopfMappingCone_subsingleton :
    Subsingleton (π_ 4 hopfMappingCone hopfMappingConeBasepoint) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive 1
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 4 5 (by omega) (sphereBasepoint 5))

/-- The fifth homotopy group of the Hopf mapping cone is infinite cyclic. -/
theorem piFive_hopfMappingCone_mulEquiv_int :
    Nonempty
      (π_ 5 hopfMappingCone hopfMappingConeBasepoint ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive 2
  obtain ⟨d⟩ := sphere_diagonal_sph_at_mulEquiv_int 4 (sphereBasepoint 5)
  exact ⟨e.trans d⟩

/-! ### Arbitrary basepoints -/

/-- The Hopf mapping cone has one path component at every basepoint. -/
theorem piZero_hopfMappingCone_subsingleton_at (x : hopfMappingCone) :
    Subsingleton (π_ 0 hopfMappingCone x) := by
  letI : PathConnectedSpace hopfMappingCone := pathConnectedSpace_hopfMappingCone
  exact subsingleton_piZero x

/-- Its fundamental group is trivial at every basepoint. -/
theorem piOne_hopfMappingCone_subsingleton_at (x : hopfMappingCone) :
    Subsingleton (π_ 1 hopfMappingCone x) := by
  letI : PathConnectedSpace hopfMappingCone := pathConnectedSpace_hopfMappingCone
  obtain ⟨e⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 1) x hopfMappingConeBasepoint
  exact e.toEquiv.subsingleton_congr.mpr piOne_hopfMappingCone_subsingleton

/-- Its second homotopy group is infinite cyclic at every basepoint. -/
theorem piTwo_hopfMappingCone_mulEquiv_int_at (x : hopfMappingCone) :
    Nonempty (π_ 2 hopfMappingCone x ≃* Multiplicative ℤ) := by
  letI : PathConnectedSpace hopfMappingCone := pathConnectedSpace_hopfMappingCone
  obtain ⟨e⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin 2) x hopfMappingConeBasepoint
  exact ⟨e.trans piTwo_hopfMappingCone_mulEquiv_int⟩

/-- Uniformly at every basepoint, its homotopy groups in degrees at least three agree with
those of the metric five-sphere. -/
theorem hopfMappingCone_higher_homotopy_mulEquiv_sphereFive_at
    (k : ℕ) (x : hopfMappingCone) :
    Nonempty
      (π_ (k + 3) hopfMappingCone x ≃*
        π_ (k + 3) (Sph 5) (sphereBasepoint 5)) := by
  letI : PathConnectedSpace hopfMappingCone := pathConnectedSpace_hopfMappingCone
  obtain ⟨e⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin (k + 3)) x hopfMappingConeBasepoint
  obtain ⟨h⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive k
  exact ⟨e.trans h⟩

/-- Its third homotopy group vanishes at every basepoint. -/
theorem piThree_hopfMappingCone_subsingleton_at (x : hopfMappingCone) :
    Subsingleton (π_ 3 hopfMappingCone x) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive_at 0 x
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 3 5 (by omega) (sphereBasepoint 5))

/-- Its fourth homotopy group vanishes at every basepoint. -/
theorem piFour_hopfMappingCone_subsingleton_at (x : hopfMappingCone) :
    Subsingleton (π_ 4 hopfMappingCone x) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive_at 1 x
  exact e.toEquiv.subsingleton_congr.mpr
    (subsingleton_homotopyGroup_sphere_of_lt 4 5 (by omega) (sphereBasepoint 5))

/-- Its fifth homotopy group is infinite cyclic at every basepoint. -/
theorem piFive_hopfMappingCone_mulEquiv_int_at (x : hopfMappingCone) :
    Nonempty (π_ 5 hopfMappingCone x ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := hopfMappingCone_higher_homotopy_mulEquiv_sphereFive_at 2 x
  obtain ⟨d⟩ := sphere_diagonal_sph_at_mulEquiv_int 4 (sphereBasepoint 5)
  exact ⟨e.trans d⟩

end Submission
