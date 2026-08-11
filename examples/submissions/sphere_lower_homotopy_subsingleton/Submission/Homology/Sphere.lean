/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.MayerVietorisIso
import Submission.Homology.SphereZero
import Submission.Homology.HomologyZero
import Submission.Homotopy.ContractionData

/-!
# The homology of the spheres

Mayer–Vietoris applied to the two enlarged hemispheres of `S^{m+1}` (whose interiors cover it,
which are contractible, and whose intersection — the belt — is homotopy equivalent to `S^m`)
gives the suspension isomorphism
```
Hₖ₊₂(S^{m+1}) ≅ Hₖ₊₁(S^m) .
```

## Main results

* `sphStepIso` — the suspension isomorphism above;
* `isZero_Hgrp_sphere_of_lt` — `Hₖ(Sⁿ) = 0` for `1 ≤ k` and `n < k`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-! ### Homology is invariant under homotopy equivalence of spaces -/

/-- A homotopy equivalence of topological spaces induces an isomorphism on singular homology. -/
def hgrpIsoOfCMHomotopyEquiv {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) (n : ℕ) :
    Hgrp n (TopCat.of Y) ≅ Hgrp n (TopCat.of Z) :=
  hgrpIsoOfHomotopyEquiv (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some e.right_inv.some n

/-! ### The suspension isomorphism

The geometry of the two enlarged hemispheres — that they are contractible and that the interiors
cover the sphere — lives in `Submission/Homotopy/ContractionData.lean`. -/

variable (m : ℕ)

/-- The homology of the belt is the homology of `S^m`. -/
def hgrpBeltIso (n : ℕ) :
    Hgrp n (TopCat.of (sphBelt m)) ≅ Hgrp n (TopCat.of (Sph m)) :=
  hgrpIsoOfCMHomotopyEquiv (sphBeltHomotopyEquiv m) n

/-- **The suspension isomorphism** `Hₖ₊₂(S^{m+1}) ≅ Hₖ₊₁(S^m)`. -/
def sphStepIso (k : ℕ) :
    Hgrp (k + 2) (TopCat.of (Sph (m + 1))) ≅ Hgrp (k + 1) (TopCat.of (Sph m)) :=
  mvδIso_of_contractible (sphLowerCap m) (sphUpperCap m)
    (sphCap_interior_union m) k ≪≫ hgrpBeltIso m (k + 1)

/-! ### Path-connectedness of the belt -/

instance instPathConnectedSpaceIcc :
    PathConnectedSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
  haveI : ContractibleSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by rw [Set.mem_Icc]; norm_num⟩
  inferInstance

instance instPathConnectedSpaceSphBelt (m : ℕ) :
    PathConnectedSpace (sphLowerCap (m + 1) ∩ sphUpperCap (m + 1) : Set (Sph (m + 2))) :=
  (sphBeltHomeo (m + 1)).symm.surjective.pathConnectedSpace
    (sphBeltHomeo (m + 1)).symm.continuous

/-! ### Vanishing of the homology of spheres -/

/-- `Hₖ(Sⁿ) = 0` above the dimension. -/
theorem isZero_Hgrp_sphere_of_lt (k : ℕ) :
    ∀ (n : ℕ), n < k → IsZero (Hgrp k (TopCat.of (Sph n))) := by
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n h
    match n, k with
    | 0, k => exact isZero_Hgrp_sphZero (k + 1) (by omega)
    | (_ + 1), 0 => omega
    | (n + 1), (k + 1) => exact IsZero.of_iso (ih n (by omega)) (sphStepIso n k)

/-- `H₁(S^{m+2}) = 0`: the higher spheres have no first homology. -/
theorem isZero_Hgrp_one_sphere (m : ℕ) : IsZero (Hgrp 1 (TopCat.of (Sph (m + 2)))) := by
  let X : TopCat.{0} := TopCat.of (Sph (m + 2))
  let A : Set X := sphLowerCap (m + 1)
  let B : Set X := sphUpperCap (m + 1)
  have hcov : interior A ∪ interior B = Set.univ := sphCap_interior_union (m + 1)
  have hzA : IsZero (Hgrp 1 (TopCat.of A)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of A) 0
  have hzB : IsZero (Hgrp 1 (TopCat.of B)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of B) 0
  have hisoA : IsIso (HgrpMap 0 (mvInclLeft A B)) := isIso_HgrpMap_zero _
  exact isZero_Hgrp_one_of_mono_mvIota A B hcov hzA hzB
    (mono_mvIota_of_mono_left A B inferInstance)

/-- `Hₖ(Sⁿ) = 0` for `1 ≤ k < n`. -/
theorem isZero_Hgrp_sphere_of_gt (k : ℕ) :
    ∀ (n : ℕ), 1 ≤ k → k < n → IsZero (Hgrp k (TopCat.of (Sph n))) := by
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n _ h
    match k, n with
    | 0, (n + 2) => exact isZero_Hgrp_one_sphere n
    | 0, 0 => omega
    | 0, 1 => omega
    | (k + 1), 0 => omega
    | (k + 1), (n + 1) => exact IsZero.of_iso (ih n (by omega) (by omega)) (sphStepIso n k)

/-- **`Hₖ(Sⁿ) = 0` whenever `k ≥ 1` and `k ≠ n`.** -/
theorem isZero_Hgrp_sphere (k n : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (Hgrp k (TopCat.of (Sph n))) := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact isZero_Hgrp_sphere_of_gt k n (Nat.one_le_iff_ne_zero.2 hk) h
  · exact isZero_Hgrp_sphere_of_lt k n h

/-- The top homology of every sphere of positive dimension is that of the circle. -/
def hgrpSphereSelfIso (n : ℕ) :
    Hgrp (n + 1) (TopCat.of (Sph (n + 1))) ≅ Hgrp 1 (TopCat.of (Sph 1)) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih => exact sphStepIso (n + 1) n ≪≫ ih

/-! ### Reduced homology -/

/-- **The reduced homology of `Sⁿ` vanishes in positive degrees other than `n`.** -/
theorem isZero_Hred_sphere (k n : ℕ) (hkn : k + 1 ≠ n) (x : (TopCat.of (Sph n) : TopCat.{0})) :
    IsZero (Hred (k + 1) x) :=
  IsZero.of_iso (isZero_Hgrp_sphere (k + 1) n (Nat.succ_ne_zero k) hkn)
    (hgrpIsoHred k x).symm

/-- The top reduced homology of `S^{n+1}` is the first homology of the circle. -/
def hredSphereSelfIso (n : ℕ) (x : (TopCat.of (Sph (n + 1)) : TopCat.{0})) :
    Hred (n + 1) x ≅ Hgrp 1 (TopCat.of (Sph 1)) :=
  (hgrpIsoHred n x).symm ≪≫ hgrpSphereSelfIso n

/-- `H₀(Sⁿ) ≅ ℤ` for `n ≥ 1`, since such spheres are path-connected. -/
def hgrpZeroSphereIso (n : ℕ) : Hgrp 0 (TopCat.of (Sph (n + 1))) ≅ AddCommGrpCat.of ℤ :=
  hgrpZeroIso (TopCat.of (Sph (n + 1)))

end Submission
