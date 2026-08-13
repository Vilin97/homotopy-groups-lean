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

end Submission
