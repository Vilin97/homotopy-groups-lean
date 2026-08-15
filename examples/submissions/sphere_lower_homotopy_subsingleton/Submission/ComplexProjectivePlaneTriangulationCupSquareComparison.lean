/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCohomology
import Submission.ComplexProjectivePlaneTriangulation
import Submission.SuspendedHopfMap

/-!
# Transferring the finite projective-plane cup square

The nine-vertex projective-plane complex carries an explicit degree-two simplicial class whose
cup square is nonzero.  This file isolates the exact comparison needed to transfer that finite
certificate to singular cohomology of the maintained geometric projective plane.

For any simplicial set `K`, the realization--singular adjunction has a unit
`K ⟶ Sing |K|`.  Consequently a singular class on the realization can be compared directly with
a class computed on `K`.  In the nine-vertex case, it is enough to know that one singular
degree-two class pulls back along this unit to the explicit finite class: naturality then forces
its singular cup square to be nonzero.  After a continuous comparison map to geometric `CP²` is
specified, the same single class-level equality forces the normalized geometric cup square to be
the top class and hence proves the mod-two Hopf-invariant-one identity.

This deliberately avoids requiring a full homeomorphism or a general cohomology comparison
theorem.  The remaining geometric task is reduced to one explicit pullback equality.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology

namespace Submission.ComplexProjectivePlaneTriangulation

/-- The adjunction unit from the finite nine-vertex simplicial set to the singular simplicial set
of its geometric realization. -/
noncomputable def projectivePlaneRealizationSingularUnit :
    projectivePlaneSSet ⟶ TopCat.toSSet.obj projectivePlaneRealization :=
  sSetTopAdj.unit.app projectivePlaneSSet

/-- A singular degree-two class on the finite realization whose adjunction-unit pullback is the
explicit finite class has nonzero singular cup square. -/
theorem projectivePlaneRealization_cupSquare_ne_zero_of_unit_pullback
    (u : Hsing 2 projectivePlaneRealization (ZMod 2))
    (hu : Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 2 u =
      degreeTwoSSetClass) :
    cupHsing (by omega : 2 + 2 = 4) u u ≠ 0 := by
  intro hzero
  apply degreeTwoSSetClass_cup_self_ne_zero
  calc
    cupH (by omega : 2 + 2 = 4) degreeTwoSSetClass degreeTwoSSetClass =
        cupH (by omega : 2 + 2 = 4)
          (Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 2 u)
          (Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 2 u) := by
      rw [hu]
    _ = Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 4
        (cupHsing (by omega : 2 + 2 = 4) u u) :=
      (map_cupH projectivePlaneRealizationSingularUnit
        (by omega : 2 + 2 = 4) u u).symm
    _ = Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 4 0 :=
      congrArg
        (Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 4)
        hzero
    _ = 0 := map_zero _

/-- The minimal class-level certificate for a continuous map from the finite realization to the
maintained geometric projective plane.  It asks only that the normalized geometric degree-two
class pull back to the explicit finite class after applying the realization--singular unit. -/
def IsProjectivePlaneCupSquareComparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2)) : Prop :=
  Hcoh.map (ZMod 2) projectivePlaneRealizationSingularUnit 2
      (Hsing.map f 2 complexProjectivePlaneModTwoClass) =
    degreeTwoSSetClass

/-- Any continuous comparison satisfying the single finite-class pullback certificate forces the
normalized geometric projective-plane cup square to be nonzero. -/
theorem complexProjectivePlaneModTwoSquare_ne_zero_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f) :
    complexProjectivePlaneModTwoSquare ≠ 0 := by
  intro hzero
  have hfinite :
      cupHsing (by omega : 2 + 2 = 4)
          (Hsing.map f 2 complexProjectivePlaneModTwoClass)
          (Hsing.map f 2 complexProjectivePlaneModTwoClass) ≠ 0 :=
    projectivePlaneRealization_cupSquare_ne_zero_of_unit_pullback
      (Hsing.map f 2 complexProjectivePlaneModTwoClass) hf
  apply hfinite
  calc
    cupHsing (by omega : 2 + 2 = 4)
        (Hsing.map f 2 complexProjectivePlaneModTwoClass)
        (Hsing.map f 2 complexProjectivePlaneModTwoClass) =
      Hsing.map f 4
        (cupHsing (by omega : 2 + 2 = 4)
          complexProjectivePlaneModTwoClass
          complexProjectivePlaneModTwoClass) :=
      (map_cupHsing f (by omega : 2 + 2 = 4)
        complexProjectivePlaneModTwoClass
        complexProjectivePlaneModTwoClass).symm
    _ = Hsing.map f 4 complexProjectivePlaneModTwoSquare := rfl
    _ = 0 := by rw [hzero, map_zero]

/-- The same minimal comparison certificate identifies the normalized geometric square with the
top class. -/
theorem complexProjectivePlaneModTwoSquare_eq_top_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f) :
    complexProjectivePlaneModTwoSquare =
      complexProjectivePlaneModTwoTopClass :=
  complexProjectivePlaneDegreeFourClass_eq_zero_or_eq_top
      complexProjectivePlaneModTwoSquare |>.resolve_left
    (complexProjectivePlaneModTwoSquare_ne_zero_of_finite_comparison f hf)

/-- In Hopf-cone coordinates, the finite comparison certificate proves the mod-two
Hopf-invariant-one identity. -/
theorem hopfMappingConeBottomSquare_eq_top_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f) :
    hopfMappingConeBottomSquare = hopfMappingConeTopClass :=
  complexProjectivePlaneModTwoSquare_eq_top_iff.mp
    (complexProjectivePlaneModTwoSquare_eq_top_of_finite_comparison f hf)

/-- Equivalently, the normalized mod-two Hopf invariant is one. -/
theorem hopfMappingConeModTwoHopfInvariant_eq_one_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f) :
    hopfMappingConeModTwoHopfInvariant = 1 :=
  hopfMappingConeModTwoHopfInvariant_eq_one_iff.mpr
    (hopfMappingConeBottomSquare_eq_top_of_finite_comparison f hf)

/-! ## The remaining suspension comparison -/

/-- The exact operation-level suspension certificate still needed after transferring the finite
cup square to the geometric Hopf cone.  It says that the normalized `Sq²` invariant of the
suspended-Hopf cone agrees with the normalized cup-square invariant of the Hopf cone. -/
def HopfInvariantSuspensionCompatible : Prop :=
  suspendedHopfModTwoSqTwoInvariant = hopfMappingConeModTwoHopfInvariant

/-- The finite realization comparison and the operation-level suspension certificate together
evaluate the normalized suspended-Hopf invariant. -/
theorem suspendedHopfModTwoSqTwoInvariant_eq_one_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f)
    (hSusp : HopfInvariantSuspensionCompatible) :
    suspendedHopfModTwoSqTwoInvariant = 1 :=
  hSusp.trans
    (hopfMappingConeModTwoHopfInvariant_eq_one_of_finite_comparison f hf)

/-- The same two comparison certificates discharge the maintained canonical cup-one
evaluation. -/
theorem suspendedHopfCanonicalRepresentativeEvaluation_eq_one_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f)
    (hSusp : HopfInvariantSuspensionCompatible) :
    sqTwoHsingDegreeThreeRepresentativeEvaluation
        suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle = 1 := by
  rw [← suspendedHopfModTwoSqTwoInvariant_eq_representativeEvaluation]
  exact suspendedHopfModTwoSqTwoInvariant_eq_one_of_finite_comparison f hf hSusp

/-- The two missing comparison equalities are sufficient to compute the first stable
representative `π₄(S³)`. -/
theorem piFourSphereThree_mulEquiv_zmod_two_of_finite_comparison
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f)
    (hSusp : HopfInvariantSuspensionCompatible) :
    Nonempty
      (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) := by
  simpa using
    sphere_first_stable_homotopy_mulEquiv_zmod_two_of_modTwoSqTwoInvariant_eq_one
      3 (by omega)
        (suspendedHopfModTwoSqTwoInvariant_eq_one_of_finite_comparison f hf hSusp)

/-- The two comparison equalities propagate the `Z/2` computation through every sphere in the
first stable stem. -/
theorem sphere_first_stable_homotopy_mulEquiv_zmod_two_of_finite_comparison
    (n : ℕ) (hn : 3 ≤ n)
    (f : projectivePlaneRealization ⟶
      TopCat.of (ComplexProjectiveModel 2))
    (hf : IsProjectivePlaneCupSquareComparison f)
    (hSusp : HopfInvariantSuspensionCompatible) :
    Nonempty
      (π_ (n + 1) (Sph n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) :=
  sphere_first_stable_homotopy_mulEquiv_zmod_two_of_modTwoSqTwoInvariant_eq_one
    n hn (suspendedHopfModTwoSqTwoInvariant_eq_one_of_finite_comparison f hf hSusp)

end Submission.ComplexProjectivePlaneTriangulation
