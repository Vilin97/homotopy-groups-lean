/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineRelativeHomology
import Submission.Homology.MappingCone

/-!
# Integral homology of the complex projective plane

This file packages the complete integral homology calculation for the maintained geometric
model of `CP²`.  Path connectedness gives degree zero.  The three-connected inclusion of the
literal projective line identifies degree two with the top homology of `S²`, while the
projective-line relative calculation supplies degree four.  The same connectivity argument
kills degrees one and three, and the Hopf mapping-cone model kills every degree at least five.

Consequently

`H_k(CP²; ℤ) ≅ ℤ` for `k = 0, 2, 4`, and `H_k(CP²; ℤ) = 0` otherwise.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology TopCat

noncomputable section

namespace Submission

/-! ## Degrees zero and two -/

/-- Degree-zero integral homology of geometric `CP²` is infinite cyclic. -/
noncomputable def complexProjectivePlaneHomologyZeroIsoInt :
    Hgrp 0 (TopCat.of (ComplexProjectiveModel 2)) ≅ AddCommGrpCat.of ℤ := by
  letI : PathConnectedSpace (ComplexProjectiveModel 2) :=
    pathConnectedSpace_complexProjectiveModel 2
  exact hgrpZeroIso (TopCat.of (ComplexProjectiveModel 2))

/-- Degree-two integral homology of the literal projective line is infinite cyclic. -/
noncomputable def complexProjectivePlaneProjectiveLineHomologyTwoIsoInt :
    Hgrp 2 (TopCat.of complexProjectivePlaneProjectiveLine) ≅
      AddCommGrpCat.of ℤ :=
  hgrpIsoOfIso 2 complexProjectivePlaneProjectiveLineIsoSphereTwo ≪≫
    hgrpSphereSelfIsoZ 1

/-- The normalized degree-two homology generator of the literal projective line. -/
noncomputable def complexProjectivePlaneProjectiveLineHomologyTwoGenerator :
    Hgrp 2 (TopCat.of complexProjectivePlaneProjectiveLine) :=
  complexProjectivePlaneProjectiveLineHomologyTwoIsoInt.inv (1 : ℤ)

/-- The normalized projective-line degree-two generator has coordinate one. -/
@[simp]
theorem complexProjectivePlaneProjectiveLineHomologyTwoIsoInt_generator :
    complexProjectivePlaneProjectiveLineHomologyTwoIsoInt.hom
        complexProjectivePlaneProjectiveLineHomologyTwoGenerator =
      (1 : ℤ) := by
  rw [complexProjectivePlaneProjectiveLineHomologyTwoGenerator,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]

/-- The literal projective-line inclusion induces an isomorphism in degree-two homology. -/
theorem complexProjectivePlaneProjectiveLine_isIso_homologyMap_two :
    IsIso
      (HgrpMap 2
        (subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
          complexProjectivePlaneProjectiveLine)) :=
  complexProjectivePlaneProjectiveLine_isThreeConnectedPair
    |>.isIso_homologyMap_subIncl
      ⟨complexProjectivePlaneProjectiveLineBasepoint,
        complexProjectivePlaneProjectiveLineBasepoint.property⟩ 2 (by omega)

/-- Degree-two integral homology of geometric `CP²` is infinite cyclic. -/
noncomputable def complexProjectivePlaneHomologyTwoIsoInt :
    Hgrp 2 (TopCat.of (ComplexProjectiveModel 2)) ≅ AddCommGrpCat.of ℤ := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : IsIso (HgrpMap 2 i) :=
    complexProjectivePlaneProjectiveLine_isIso_homologyMap_two
  exact (asIso (HgrpMap 2 i)).symm ≪≫
    complexProjectivePlaneProjectiveLineHomologyTwoIsoInt

/-- The normalized degree-two homology generator of geometric `CP²`. -/
noncomputable def complexProjectivePlaneHomologyTwoGenerator :
    Hgrp 2 (TopCat.of (ComplexProjectiveModel 2)) :=
  HgrpMap 2
    (subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
      complexProjectivePlaneProjectiveLine)
    complexProjectivePlaneProjectiveLineHomologyTwoGenerator

/-- The normalized projective-plane degree-two generator has coordinate one. -/
@[simp]
theorem complexProjectivePlaneHomologyTwoIsoInt_generator :
    complexProjectivePlaneHomologyTwoIsoInt.hom
        complexProjectivePlaneHomologyTwoGenerator = (1 : ℤ) := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : IsIso (HgrpMap 2 i) :=
    complexProjectivePlaneProjectiveLine_isIso_homologyMap_two
  change complexProjectivePlaneProjectiveLineHomologyTwoIsoInt.hom
      ((asIso (HgrpMap 2 i)).inv
        (HgrpMap 2 i
          complexProjectivePlaneProjectiveLineHomologyTwoGenerator)) =
    (1 : ℤ)
  have hcancel :
      (asIso (HgrpMap 2 i)).inv
          (HgrpMap 2 i
            complexProjectivePlaneProjectiveLineHomologyTwoGenerator) =
        complexProjectivePlaneProjectiveLineHomologyTwoGenerator := by
    change (asIso (HgrpMap 2 i)).inv
        ((asIso (HgrpMap 2 i)).hom
          complexProjectivePlaneProjectiveLineHomologyTwoGenerator) = _
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply]
  rw [hcancel,
    complexProjectivePlaneProjectiveLineHomologyTwoIsoInt_generator]

/-! ## Vanishing in all remaining degrees -/

/-- The literal projective line has zero first integral homology. -/
theorem isZero_Hgrp_complexProjectivePlaneProjectiveLine_one :
    IsZero (Hgrp 1 (TopCat.of complexProjectivePlaneProjectiveLine)) :=
  IsZero.of_iso
    (isZero_Hgrp_sphere 1 2 (by omega) (by omega))
    (hgrpIsoOfIso 1 complexProjectivePlaneProjectiveLineIsoSphereTwo)

/-- Geometric `CP²` has zero first integral homology. -/
theorem isZero_Hgrp_complexProjectivePlane_one :
    IsZero (Hgrp 1 (TopCat.of (ComplexProjectiveModel 2))) := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : IsIso (HgrpMap 1 i) :=
    complexProjectivePlaneProjectiveLine_isThreeConnectedPair
      |>.isIso_homologyMap_subIncl
        ⟨complexProjectivePlaneProjectiveLineBasepoint,
          complexProjectivePlaneProjectiveLineBasepoint.property⟩ 1 (by omega)
  exact IsZero.of_iso
    isZero_Hgrp_complexProjectivePlaneProjectiveLine_one
    (asIso (HgrpMap 1 i)).symm

/-- Geometric `CP²` has zero third integral homology. -/
theorem isZero_Hgrp_complexProjectivePlane_three :
    IsZero (Hgrp 3 (TopCat.of (ComplexProjectiveModel 2))) := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : Epi (HgrpMap 3 i) :=
    complexProjectivePlaneProjectiveLine_isThreeConnectedPair
      |>.epi_homologyMap_subIncl
        ⟨complexProjectivePlaneProjectiveLineBasepoint,
          complexProjectivePlaneProjectiveLineBasepoint.property⟩ 3 (by omega)
  exact IsZero.of_epi (HgrpMap 3 i)
    isZero_Hgrp_complexProjectivePlaneProjectiveLine_three

/-- The concrete Hopf mapping cone has zero integral homology in every degree at least five. -/
theorem isZero_Hgrp_hopfMappingCone_of_five_le (k : ℕ) (hk : 5 ≤ k) :
    IsZero (Hgrp k hopfMappingCone) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 :=
    ⟨k - 2, by omega⟩
  exact IsZero.of_iso
    (isZero_Hgrp_sphere (n + 1) 3 (by omega) (by omega))
    (mappingConeHomologySuspensionIso hopfTopCat n
      (isZero_Hgrp_sphere (n + 2) 2 (by omega) (by omega))
      (isZero_Hgrp_sphere (n + 1) 2 (by omega) (by omega)))

/-- Geometric `CP²` has zero integral homology in every degree at least five. -/
theorem isZero_Hgrp_complexProjectivePlane_of_five_le
    (k : ℕ) (hk : 5 ≤ k) :
    IsZero (Hgrp k (TopCat.of (ComplexProjectiveModel 2))) :=
  IsZero.of_iso (isZero_Hgrp_hopfMappingCone_of_five_le k hk)
    (hgrpIsoOfIso k complexProjectivePlaneIsoHopfMappingCone)

/-- Geometric `CP²` has zero integral homology outside degrees zero, two, and four. -/
theorem isZero_Hgrp_complexProjectivePlane_of_ne_zero_two_four
    (k : ℕ) (hzero : k ≠ 0) (htwo : k ≠ 2) (hfour : k ≠ 4) :
    IsZero (Hgrp k (TopCat.of (ComplexProjectiveModel 2))) := by
  by_cases hone : k = 1
  · subst k
    exact isZero_Hgrp_complexProjectivePlane_one
  by_cases hthree : k = 3
  · subst k
    exact isZero_Hgrp_complexProjectivePlane_three
  exact isZero_Hgrp_complexProjectivePlane_of_five_le k (by omega)

/-! ## Complete classification -/

/-- In each nonzero homology degree, geometric `CP²` has an explicit infinite-cyclic
coordinate. -/
theorem complexProjectivePlaneHomologyIsoIntOfDegree
    (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) :
    Nonempty
      (Hgrp k (TopCat.of (ComplexProjectiveModel 2)) ≅
        AddCommGrpCat.of ℤ) := by
  rcases hk with rfl | rfl | rfl
  · exact ⟨complexProjectivePlaneHomologyZeroIsoInt⟩
  · exact ⟨complexProjectivePlaneHomologyTwoIsoInt⟩
  · exact ⟨complexProjectivePlaneHomologyIsoInt⟩

/-- Complete integral homology classification of geometric `CP²`. -/
theorem complexProjectivePlane_integralHomology_classification :
    (∀ k : ℕ, k ≠ 0 → k ≠ 2 → k ≠ 4 →
      IsZero (Hgrp k (TopCat.of (ComplexProjectiveModel 2)))) ∧
      Nonempty
        (Hgrp 0 (TopCat.of (ComplexProjectiveModel 2)) ≅
          AddCommGrpCat.of ℤ) ∧
      Nonempty
        (Hgrp 2 (TopCat.of (ComplexProjectiveModel 2)) ≅
          AddCommGrpCat.of ℤ) ∧
      Nonempty
        (Hgrp 4 (TopCat.of (ComplexProjectiveModel 2)) ≅
          AddCommGrpCat.of ℤ) :=
  ⟨isZero_Hgrp_complexProjectivePlane_of_ne_zero_two_four,
    ⟨complexProjectivePlaneHomologyZeroIsoInt⟩,
    ⟨complexProjectivePlaneHomologyTwoIsoInt⟩,
    ⟨complexProjectivePlaneHomologyIsoInt⟩⟩

end Submission
