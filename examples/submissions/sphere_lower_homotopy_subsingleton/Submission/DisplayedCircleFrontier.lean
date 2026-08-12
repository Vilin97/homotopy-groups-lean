/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Lean4TwentyResults

/-!
# Exact group witnesses for the displayed metric-circle frontier

`Submission.sphere_one_higher_homotopy_subsingleton_at` proves vanishing in every degree.
This file packages that vanishing as an explicit multiplicative equivalence with the trivial
group, which is the form consumed by the extended lattice audit.
-/

open HomotopyGroups

noncomputable section

namespace Submission

/-- Every higher homotopy group of the exact metric circle, at every basepoint, is explicitly
isomorphic to the trivial group. -/
theorem sphere_one_higher_homotopy_mulEquiv_punit_at
    (k : ℕ) (x : SphereSpace 1) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) x ≃* PUnit) := by
  letI := sphere_one_higher_homotopy_subsingleton_at k x
  exact ⟨
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => rfl }⟩

/-- Distinguished-basepoint form of
`Submission.sphere_one_higher_homotopy_mulEquiv_punit_at`. -/
theorem sphere_one_higher_homotopy_mulEquiv_punit (k : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) :=
  sphere_one_higher_homotopy_mulEquiv_punit_at k (sphereBasepoint 1)

/-! Named witnesses for the eighteen newly displayed cells, `k = 91, ..., 108`. -/

theorem pi92_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 92 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 90

theorem pi93_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 93 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 91

theorem pi94_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 94 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 92

theorem pi95_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 95 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 93

theorem pi96_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 96 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 94

theorem pi97_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 97 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 95

theorem pi98_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 98 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 96

theorem pi99_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 99 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 97

theorem pi100_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 100 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 98

theorem pi101_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 101 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 99

theorem pi102_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 102 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 100

theorem pi103_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 103 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 101

theorem pi104_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 104 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 102

theorem pi105_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 105 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 103

theorem pi106_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 106 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 104

theorem pi107_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 107 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 105

theorem pi108_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 108 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 106

theorem pi109_sphere_one_mulEquiv_punit :
    Nonempty (HomotopyGroup.Pi 109 (SphereSpace 1) (sphereBasepoint 1) ≃* PUnit) := by
  simpa using sphere_one_higher_homotopy_mulEquiv_punit 107

end Submission
