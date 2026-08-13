/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.MayerVietoris
import Submission.Homology.Sphere

/-!
# Vanishing of singular cohomology above the dimension of a sphere

The enlarged hemispheres of `S^{m+1}` form a cover by two contractible sets, and their
intersection is homotopy equivalent to `S^m`.  Cohomological Mayer--Vietoris therefore gives the
suspension isomorphism
```
H^{k+1}(S^m; R) ≅ H^{k+2}(S^{m+1}; R).
```
Starting from the positive-degree vanishing for the totally disconnected `0`-sphere yields
`H^k(S^n;R) = 0` whenever `n < k`.

## Main results

* `Submission.hsingSphStepEquiv` -- the cohomological suspension isomorphism;
* `Submission.subsingleton_Hsing_sphere` -- positive cohomology vanishes away from the sphere
  dimension;
* `Submission.sqTwoHsingDegreeThree_sphere_three` -- `Sq² : H³(S³;F₂) → H⁵(S³;F₂)` is zero.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable (R : Type) [CommRing R]

/-- The homotopy equivalence from the belt to `S^m`, used contravariantly on cohomology. -/
def hsingBeltEquiv (m n : ℕ) :
    Hsing n (TopCat.of (Sph m)) R ≃+ Hsing n (TopCat.of (sphBelt m)) R :=
  (hsingLinearEquivOfHomotopyEquiv
    (TopCat.ofHom (sphBeltHomotopyEquiv m).toFun)
    (TopCat.ofHom (sphBeltHomotopyEquiv m).invFun)
    (sphBeltHomotopyEquiv m).left_inv.some
    (sphBeltHomotopyEquiv m).right_inv.some n).toAddEquiv

/-- **Cohomological suspension for spheres:**
`H^{k+1}(S^m;R) ≅ H^{k+2}(S^{m+1};R)`. -/
def hsingSphStepEquiv (m k : ℕ) :
    Hsing (k + 1) (TopCat.of (Sph m)) R ≃+
      Hsing (k + 2) (TopCat.of (Sph (m + 1))) R :=
  (hsingBeltEquiv R m (k + 1)).trans
    (mvHsingδEquiv_of_contractible (X := TopCat.of (Sph (m + 1)))
      (sphLowerCap m) (sphUpperCap m) R
      (sphCap_interior_union m) k)

/-! ### Vanishing below the sphere dimension -/

/-- Degree-one cohomology of every sphere of dimension at least two vanishes. -/
theorem isZero_dualHomology_one_sphere (m : ℕ) :
    IsZero ((homDual (Csing (TopCat.of (Sph (m + 2))))
      (AddCommGrpCat.of R)).homology 1) :=
  isZero_dualHomology_one_of_contractible_cover
    (sphLowerCap (m + 1)) (sphUpperCap (m + 1)) R
    (sphCap_interior_union (m + 1))

/-- `H¹(Sⁿ;R) = 0` for `n ≥ 2`. -/
theorem subsingleton_Hsing_one_sphere (m : ℕ) :
    Subsingleton (Hsing 1 (TopCat.of (Sph (m + 2))) R) :=
  subsingleton_Hsing_of_isZero_dualHomology R 1
    (isZero_dualHomology_one_sphere R m)

/-- `Hᵏ(Sⁿ;R) = 0` for `1 ≤ k < n`. -/
theorem subsingleton_Hsing_sphere_of_gt (k : ℕ) :
    ∀ (n : ℕ), 1 ≤ k → k < n → Subsingleton (Hsing k (TopCat.of (Sph n)) R) := by
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n _ h
    match k, n with
    | 0, (n + 2) => exact subsingleton_Hsing_one_sphere R n
    | 0, 0 => omega
    | 0, 1 => omega
    | (k + 1), 0 => omega
    | (k + 1), (n + 1) =>
        let e := hsingSphStepEquiv R n k
        letI : Subsingleton (Hsing (k + 1) (TopCat.of (Sph n)) R) :=
          ih n (by omega) (by omega)
        exact ⟨fun a b ↦ e.symm.injective
          (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-! ### Vanishing above the sphere dimension -/

/-- **Singular cohomology of a sphere vanishes above its dimension.** -/
theorem subsingleton_Hsing_sphere_of_lt (k : ℕ) :
    ∀ n : ℕ, n < k → Subsingleton (Hsing k (TopCat.of (Sph n)) R) := by
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n h
    match n, k with
    | 0, k =>
        exact subsingleton_Hsing_of_totallyDisconnected R (k + 1) (by omega)
    | (_ + 1), 0 => omega
    | (n + 1), (k + 1) =>
        let e := hsingSphStepEquiv R n k
        letI : Subsingleton (Hsing (k + 1) (TopCat.of (Sph n)) R) := ih n (by omega)
        exact ⟨fun a b ↦ e.symm.injective
          (Subsingleton.elim (e.symm a) (e.symm b))⟩

/-- **Positive singular cohomology of a sphere vanishes away from its dimension.** -/
theorem subsingleton_Hsing_sphere (k n : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    Subsingleton (Hsing k (TopCat.of (Sph n)) R) := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact subsingleton_Hsing_sphere_of_gt R k n (Nat.one_le_iff_ne_zero.2 hk) h
  · exact subsingleton_Hsing_sphere_of_lt R k n h

/-- The target of `Sq² : H³(S³;F₂) → H⁵(S³;F₂)` vanishes, so the operation is zero on every
degree-three class of the `3`-sphere. -/
theorem sqTwoHsingDegreeThree_sphere_three
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2)) :
    sqTwoHsingDegreeThree x = 0 := by
  letI : Subsingleton (Hsing 5 (TopCat.of (Sph 3)) (ZMod 2)) :=
    subsingleton_Hsing_sphere_of_lt (ZMod 2) 5 3 (by omega)
  exact Subsingleton.elim _ _

end Submission
