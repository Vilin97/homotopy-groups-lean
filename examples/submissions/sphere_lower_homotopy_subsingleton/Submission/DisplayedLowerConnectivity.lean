/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import ChallengeDeps
import Submission.Model.SphereConnected

/-!
# Exact group witnesses below the sphere diagonal

`Submission.subsingleton_homotopyGroup_sphere_of_lt` proves the geometric connectivity theorem
for the exact metric-sphere model.  This file packages every *positive-dimensional* instance as
an explicit multiplicative equivalence with the trivial group.  In absolute-degree coordinates
this is the full region

`1 ≤ m < n  ⟹  π_m(S^n) ≃ 1`.

Unlike a list of numerical aliases, the theorem below is uniform in the sphere dimension, the
homotopy degree, and the basepoint.
-/

open HomotopyGroups

noncomputable section

namespace Submission

/-- Every positive homotopy group strictly below the dimension of the exact metric sphere is
explicitly isomorphic to the trivial group, at every basepoint. -/
theorem sphere_lower_positive_homotopy_mulEquiv_punit_at
    (n d : ℕ) (h : d + 1 < n) (x : SphereSpace n) :
    Nonempty
      (HomotopyGroup.Pi (d + 1) (SphereSpace n) x ≃* PUnit) := by
  letI : Subsingleton (HomotopyGroup.Pi (d + 1) (SphereSpace n) x) :=
    subsingleton_homotopyGroup_sphere_of_lt (d + 1) n h x
  exact ⟨
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => rfl }⟩

/-- Distinguished-basepoint form of
`Submission.sphere_lower_positive_homotopy_mulEquiv_punit_at`. -/
theorem sphere_lower_positive_homotopy_mulEquiv_punit
    (n d : ℕ) (h : d + 1 < n) :
    Nonempty
      (HomotopyGroup.Pi (d + 1) (SphereSpace n) (sphereBasepoint n) ≃* PUnit) :=
  sphere_lower_positive_homotopy_mulEquiv_punit_at n d h (sphereBasepoint n)

end Submission
