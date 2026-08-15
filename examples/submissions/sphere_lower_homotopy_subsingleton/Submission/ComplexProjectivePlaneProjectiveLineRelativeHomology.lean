/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineRelativePiFour
import Submission.Homology.LesTools
import Submission.Hurewicz.ConnectedPair

/-!
# The first nonzero relative homology group of `(CP², CP¹)`

The literal embedded projective line is homeomorphic to `S²`, so its third and fourth
homology groups vanish.  The long exact sequence of the pair therefore identifies the
absolute-to-relative map in degree four with an isomorphism.  Transporting the normalized
degree-four generator of geometric `CP²` computes

`H₄(CP², CP¹; ℤ) ≅ ℤ`.

The pair's previously established three-connectivity also gives vanishing relative homology
through degree three.  Thus degree four is the first nonzero relative homology degree, matching
the first nonzero relative homotopy degree.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology TopCat

noncomputable section

namespace Submission

/-! ## Homology of the embedded projective line -/

/-- The literal embedded projective line, in the maintained metric two-sphere coordinate. -/
noncomputable def complexProjectivePlaneProjectiveLineIsoSphereTwo :
    TopCat.of complexProjectivePlaneProjectiveLine ≅ TopCat.of (Sph 2) :=
  TopCat.isoOfHomeo
    (complexProjectivePlaneProjectiveLineHomeomorph.symm.trans
      (TopCat.homeoOfIso complexProjectiveLineIsoSphereTwo))

/-- The literal embedded projective line has zero third integral homology. -/
theorem isZero_Hgrp_complexProjectivePlaneProjectiveLine_three :
    IsZero (Hgrp 3 (TopCat.of complexProjectivePlaneProjectiveLine)) :=
  IsZero.of_iso
    (isZero_Hgrp_sphere 3 2 (by omega) (by omega))
    (hgrpIsoOfIso 3 complexProjectivePlaneProjectiveLineIsoSphereTwo)

/-- The literal embedded projective line has zero fourth integral homology. -/
theorem isZero_Hgrp_complexProjectivePlaneProjectiveLine_four :
    IsZero (Hgrp 4 (TopCat.of complexProjectivePlaneProjectiveLine)) :=
  IsZero.of_iso
    (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
    (hgrpIsoOfIso 4 complexProjectivePlaneProjectiveLineIsoSphereTwo)

/-! ## The absolute degree-four coordinate -/

/-- Degree-four integral homology of geometric `CP²` in the normalized Hopf-cone
coordinate. -/
noncomputable def complexProjectivePlaneHomologyIsoInt :
    Hgrp 4 (TopCat.of (ComplexProjectiveModel 2)) ≅ AddCommGrpCat.of ℤ :=
  hgrpIsoOfIso 4 complexProjectivePlaneIsoHopfMappingCone ≪≫
    hopfMappingConeHomologyIsoInt

/-- The maintained geometric projective-plane homology generator has coordinate one. -/
@[simp]
theorem complexProjectivePlaneHomologyIsoInt_generator :
    complexProjectivePlaneHomologyIsoInt.hom
        complexProjectivePlaneHomologyGenerator = (1 : ℤ) := by
  change hopfMappingConeHomologyIsoInt.hom
      (HgrpMap 4 complexProjectivePlaneIsoHopfMappingCone.hom
        complexProjectivePlaneHomologyGenerator) = (1 : ℤ)
  rw [complexProjectivePlaneHomologyGenerator_map,
    hopfMappingConeHomologyIsoInt_generator]

/-! ## The first relative homology group -/

/-- The absolute-to-relative homology map in degree four for the literal pair is an
isomorphism. -/
theorem complexProjectivePlaneProjectiveLine_isIso_relJ_four :
    IsIso
      (relJ 4
        (subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
          complexProjectivePlaneProjectiveLine)) := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  exact isIso_relJ i 3
    (isZero_Hgrp_complexProjectivePlaneProjectiveLine_four.eq_zero_of_src _)
    (isZero_Hgrp_complexProjectivePlaneProjectiveLine_three.mono _)

/-- The fourth relative integral homology of the literal pair is infinite cyclic. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt :
    HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
        complexProjectivePlaneProjectiveLine ≅ AddCommGrpCat.of ℤ := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : IsIso (relJ 4 i) :=
    complexProjectivePlaneProjectiveLine_isIso_relJ_four
  exact (asIso (relJ 4 i)).symm ≪≫ complexProjectivePlaneHomologyIsoInt

/-- The normalized generator of fourth relative integral homology of the literal pair. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator :
    HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
      complexProjectivePlaneProjectiveLine :=
  relJ 4
    (subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
      complexProjectivePlaneProjectiveLine)
    complexProjectivePlaneHomologyGenerator

/-- The normalized relative degree-four homology generator has coordinate one. -/
@[simp]
theorem complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt_generator :
    complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.hom
        complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator =
      (1 : ℤ) := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  letI : IsIso (relJ 4 i) :=
    complexProjectivePlaneProjectiveLine_isIso_relJ_four
  change complexProjectivePlaneHomologyIsoInt.hom
      ((asIso (relJ 4 i)).inv
        (relJ 4 i complexProjectivePlaneHomologyGenerator)) = (1 : ℤ)
  have hcancel :
      (asIso (relJ 4 i)).inv
          (relJ 4 i complexProjectivePlaneHomologyGenerator) =
        complexProjectivePlaneHomologyGenerator := by
    change (asIso (relJ 4 i)).inv
        ((asIso (relJ 4 i)).hom complexProjectivePlaneHomologyGenerator) = _
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply]
  rw [hcancel, complexProjectivePlaneHomologyIsoInt_generator]

/-- The normalized fourth relative homology generator is nonzero. -/
theorem complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator_ne_zero :
    complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun z ↦ complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.hom z)
    hzero
  rw [complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt_generator,
    map_zero] at h
  exact one_ne_zero h

/-- Relative integral homology of the literal pair vanishes through degree three. -/
theorem isZero_complexProjectivePlaneProjectiveLine_relativeHomology
    (k : ℕ) (hk : k ≤ 3) :
    IsZero
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
        complexProjectivePlaneProjectiveLine) :=
  complexProjectivePlaneProjectiveLine_isThreeConnectedPair.isZero_relativeHomology
    ⟨complexProjectivePlaneProjectiveLineBasepoint,
      complexProjectivePlaneProjectiveLineBasepoint.property⟩ k hk

/-- Degree four is the first nonzero relative integral homology degree of the literal pair. -/
theorem complexProjectivePlaneProjectiveLine_relativeHomology_first_nonzero :
    (∀ k ≤ 3,
      IsZero
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) k
          complexProjectivePlaneProjectiveLine)) ∧
      ¬ IsZero
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneProjectiveLine) := by
  constructor
  · exact isZero_complexProjectivePlaneProjectiveLine_relativeHomology
  · intro hzero
    exact complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator_ne_zero
      (by
        have hid := (IsZero.iff_id_eq_zero _).1 hzero
        simpa using ConcreteCategory.congr_hom hid
          complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator)

end Submission
