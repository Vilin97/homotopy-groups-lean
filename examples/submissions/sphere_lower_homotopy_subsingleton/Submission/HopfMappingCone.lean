/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.CellAttachmentCupSquare
import Submission.Cohomology.MappingCone
import Submission.Cohomology.MappingConePair
import Submission.Cohomology.SingularCupEvaluation
import Submission.Cohomology.SphereTop
import Submission.Homology.MappingCone
import Submission.HopfMap

/-!
# The mapping cone of the Hopf map

This file packages the mapping cone of the concrete quadratic Hopf map `S³ ⟶ S²`.  Its
bottom mod-two class is the unique lift of the normalized generator of `H²(S²; 𝔽₂)`, and
its top class and homology generator are normalized through the mapping-cone suspension
isomorphisms.  Consequently every degree-four class is either zero or the normalized top class.

These normalizations isolate the classical Hopf-invariant-one calculation as the assertion that
the square of the bottom class is the top class.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- The concrete quadratic Hopf map as a morphism of topological spaces. -/
noncomputable def hopfTopCat :
    TopCat.of (Sph 3) ⟶ TopCat.of (Sph 2) :=
  TopCat.ofHom hopfMap

/-- The topological mapping cone of the concrete Hopf map. -/
noncomputable abbrev hopfMappingCone : TopCat.{0} :=
  topologicalMappingCone hopfTopCat

/-- The inclusion of the bottom `S²` into the Hopf mapping cone. -/
noncomputable abbrev hopfMappingConeIncl :
    TopCat.of (Sph 2) ⟶ hopfMappingCone :=
  topologicalMappingConeIncl hopfTopCat

/-! ### The normalized top homology and cohomology classes -/

/-- The fourth homology of the Hopf mapping cone is infinite cyclic. -/
noncomputable def hopfMappingConeHomologyIsoInt :
    Hgrp 4 hopfMappingCone ≅ AddCommGrpCat.of ℤ :=
  mappingConeHomologySuspensionIso hopfTopCat 2
      (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
      (isZero_Hgrp_sphere 3 2 (by omega) (by omega)) ≪≫
    hgrpSphereSelfIsoZ 2

/-- The degree-four homology generator selected by the mapping-cone suspension isomorphism. -/
noncomputable def hopfMappingConeHomologyGenerator : Hgrp 4 hopfMappingCone :=
  hopfMappingConeHomologyIsoInt.inv (1 : ℤ)

@[simp]
theorem hopfMappingConeHomologyIsoInt_generator :
    hopfMappingConeHomologyIsoInt.hom hopfMappingConeHomologyGenerator = (1 : ℤ) := by
  rw [hopfMappingConeHomologyGenerator,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- The selected degree-four mapping-cone homology generator is nonzero. -/
theorem hopfMappingConeHomologyGenerator_ne_zero :
    hopfMappingConeHomologyGenerator ≠ 0 := by
  intro hzero
  have h := congrArg (fun z ↦ hopfMappingConeHomologyIsoInt.hom z) hzero
  rw [hopfMappingConeHomologyIsoInt_generator, map_zero] at h
  exact one_ne_zero h

/-- Degree-three mod-two cohomology of `S²` vanishes. -/
theorem isZero_sphereTwoDualCohomology_three :
    IsZero ((homDual (Csing (TopCat.of (Sph 2))) modTwoCoefficients).homology 3) := by
  letI : Subsingleton (Hsing 3 (TopCat.of (Sph 2)) (ZMod 2)) :=
    subsingleton_Hsing_sphere (ZMod 2) 3 2 (by omega) (by omega)
  exact isZero_dualHomology_of_subsingleton_Hsing (ZMod 2) 3

/-- Degree-four mod-two cohomology of `S²` vanishes. -/
theorem isZero_sphereTwoDualCohomology_four :
    IsZero ((homDual (Csing (TopCat.of (Sph 2))) modTwoCoefficients).homology 4) := by
  letI : Subsingleton (Hsing 4 (TopCat.of (Sph 2)) (ZMod 2)) :=
    subsingleton_Hsing_sphere (ZMod 2) 4 2 (by omega) (by omega)
  exact isZero_dualHomology_of_subsingleton_Hsing (ZMod 2) 4

/-- The normalized top mod-two class on the Hopf mapping cone. -/
noncomputable def hopfMappingConeTopDualClass :
    (homDual (Csing hopfMappingCone) modTwoCoefficients).homology 4 :=
  (mappingConeCohomologySuspensionIso hopfTopCat (ZMod 2) 2
    isZero_sphereTwoDualCohomology_three
    isZero_sphereTwoDualCohomology_four).hom
      (sphereTopModTwoDualClass 2)

set_option backward.isDefEq.respectTransparency false in
/-- The homological mapping-cone suspension sends the selected cone generator to the normalized
top generator of `S³`. -/
theorem hopfMappingConeHomologySuspensionIso_generator :
    (mappingConeHomologySuspensionIso hopfTopCat 2
      (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
      (isZero_Hgrp_sphere 3 2 (by omega) (by omega))).hom
        hopfMappingConeHomologyGenerator = sphereTopHomologyClass 2 := by
  rw [sphereTopHomologyClass_eq_generator, hopfMappingConeHomologyGenerator]
  change (mappingConeHomologySuspensionIso hopfTopCat 2
      (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
      (isZero_Hgrp_sphere 3 2 (by omega) (by omega))).hom
    ((mappingConeHomologySuspensionIso hopfTopCat 2
      (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
      (isZero_Hgrp_sphere 3 2 (by omega) (by omega)) ≪≫
        hgrpSphereSelfIsoZ 2).inv (1 : ℤ)) =
      (hgrpSphereSelfIsoZ 2).inv (1 : ℤ)
  rw [Iso.trans_inv, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- The normalized top cone class evaluates to one on the selected integral generator. -/
@[simp]
theorem hopfMappingConeTopDualClass_evaluation :
    ev (Csing hopfMappingCone) modTwoCoefficients 4
      hopfMappingConeTopDualClass hopfMappingConeHomologyGenerator = (1 : ZMod 2) := by
  have h := mappingConeSuspensionIso_adjoint hopfTopCat (ZMod 2) 2
    (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
    (isZero_Hgrp_sphere 3 2 (by omega) (by omega))
    isZero_sphereTwoDualCohomology_three isZero_sphereTwoDualCohomology_four
    (sphereTopModTwoDualClass 2) hopfMappingConeHomologyGenerator
  rw [hopfMappingConeHomologySuspensionIso_generator,
    sphereTopModTwoDualClass_evaluation] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The normalized top cone class is nonzero. -/
theorem hopfMappingConeTopDualClass_ne_zero : hopfMappingConeTopDualClass ≠ 0 := by
  intro hzero
  have h := hopfMappingConeTopDualClass_evaluation
  rw [hzero, map_zero] at h
  exact one_ne_zero h.symm

/-- The normalized top cone class in singular cohomology. -/
noncomputable def hopfMappingConeTopClass : Hsing 4 hopfMappingCone (ZMod 2) :=
  (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4).symm
    hopfMappingConeTopDualClass

/-- The normalized singular cohomology class is nonzero. -/
theorem hopfMappingConeTopClass_ne_zero : hopfMappingConeTopClass ≠ 0 := by
  intro hzero
  apply hopfMappingConeTopDualClass_ne_zero
  have h := congrArg (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4) hzero
  rw [hopfMappingConeTopClass, AddEquiv.apply_symm_apply, map_zero] at h
  exact h

/-- Every degree-four dual cohomology class of the Hopf mapping cone is zero or its normalized
top class. -/
theorem hopfMappingConeDualClass_eq_zero_or_eq_top
    (Φ : (homDual (Csing hopfMappingCone) modTwoCoefficients).homology 4) :
    Φ = 0 ∨ Φ = hopfMappingConeTopDualClass := by
  let e := mappingConeCohomologySuspensionIso hopfTopCat (ZMod 2) 2
    isZero_sphereTwoDualCohomology_three
    isZero_sphereTwoDualCohomology_four
  rcases sphereTopDualClass_eq_zero_or_eq_top 2 (e.inv Φ) with hzero | htop
  · left
    have h := congrArg (fun x ↦ e.hom x) hzero
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply, map_zero] at h
    exact h
  · right
    have h := congrArg (fun x ↦ e.hom x) htop
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] at h
    exact h

/-- Every degree-four singular cohomology class of the Hopf mapping cone is zero or its
normalized top class. -/
theorem hopfMappingConeClass_eq_zero_or_eq_top (x : Hsing 4 hopfMappingCone (ZMod 2)) :
    x = 0 ∨ x = hopfMappingConeTopClass := by
  rcases hopfMappingConeDualClass_eq_zero_or_eq_top
      (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4 x) with hzero | htop
  · left
    apply (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4).injective
    rw [map_zero]
    exact hzero
  · right
    apply (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4).injective
    rw [hopfMappingConeTopClass, AddEquiv.apply_symm_apply]
    exact htop

/-! ### The canonical bottom class and its square -/

/-- Degree-two relative mod-two cohomology of the Hopf mapping-cone pair vanishes. -/
theorem isZero_HrelCoh_hopfMappingConeIncl_two :
    IsZero (HrelCoh hopfMappingConeIncl (AddCommGrpCat.of (ZMod 2)) 2) := by
  simpa using isZero_HrelCoh_mappingConeIncl_sphere
    (ZMod 2) 3 hopfTopCat 1 (by omega) (by omega)

/-- Degree-three relative mod-two cohomology of the Hopf mapping-cone pair vanishes. -/
theorem isZero_HrelCoh_hopfMappingConeIncl_three :
    IsZero (HrelCoh hopfMappingConeIncl (AddCommGrpCat.of (ZMod 2)) 3) := by
  simpa using isZero_HrelCoh_mappingConeIncl_sphere
    (ZMod 2) 3 hopfTopCat 2 (by omega) (by omega)

/-- Restriction from the Hopf mapping cone to its bottom `S²` is bijective in degree two. -/
theorem hopfMappingConeIncl_bijective :
    Function.Bijective (Hsing.map (R := ZMod 2) hopfMappingConeIncl 2) :=
  bijective_Hsing_map_of_isZero_HrelCoh hopfMappingConeIncl (ZMod 2) 2
    isZero_HrelCoh_hopfMappingConeIncl_two
    isZero_HrelCoh_hopfMappingConeIncl_three

/-- The unique degree-two cone class restricting to `x`. -/
noncomputable def hopfMappingConeLift (x : Hsing 2 (TopCat.of (Sph 2)) (ZMod 2)) :
    Hsing 2 hopfMappingCone (ZMod 2) :=
  Classical.choose (hopfMappingConeIncl_bijective.2 x)

@[simp]
theorem hopfMappingConeLift_restrict (x : Hsing 2 (TopCat.of (Sph 2)) (ZMod 2)) :
    Hsing.map hopfMappingConeIncl 2 (hopfMappingConeLift x) = x :=
  Classical.choose_spec (hopfMappingConeIncl_bijective.2 x)

/-- The canonical bottom class of the Hopf mapping cone. -/
noncomputable abbrev hopfMappingConeBottomClass : Hsing 2 hopfMappingCone (ZMod 2) :=
  hopfMappingConeLift (sphereTopModTwoClass 1)

/-- The canonical bottom class restricts to the normalized generator of `H²(S²; 𝔽₂)`. -/
@[simp]
theorem hopfMappingConeBottomClass_restrict :
    Hsing.map hopfMappingConeIncl 2 hopfMappingConeBottomClass =
      sphereTopModTwoClass 1 :=
  hopfMappingConeLift_restrict (sphereTopModTwoClass 1)

/-- The canonical bottom class is nonzero. -/
theorem hopfMappingConeBottomClass_ne_zero : hopfMappingConeBottomClass ≠ 0 := by
  intro hzero
  apply sphereTopModTwoClass_ne_zero 1
  rw [← hopfMappingConeBottomClass_restrict, hzero, map_zero]

/-- A fixed singular cocycle representing the canonical bottom class. -/
noncomputable def hopfMappingConeBottomCocycle :
    cocycles (TopCat.toSSet.obj hopfMappingCone) (ZMod 2) 2 :=
  Classical.choose (Hcoh.mk_surjective hopfMappingConeBottomClass)

/-- The chosen bottom cocycle represents the canonical bottom class. -/
@[simp]
theorem hopfMappingConeBottomCocycle_mk :
    Hcoh.mk hopfMappingConeBottomCocycle = hopfMappingConeBottomClass :=
  Classical.choose_spec (Hcoh.mk_surjective hopfMappingConeBottomClass)

/-- The cup square whose value is the mod-two Hopf invariant of the concrete Hopf map. -/
noncomputable def hopfMappingConeBottomSquare : Hsing 4 hopfMappingCone (ZMod 2) :=
  cupHsing (by omega : 2 + 2 = 4)
    hopfMappingConeBottomClass hopfMappingConeBottomClass

/-- The bottom square is either zero or the normalized top class. -/
theorem hopfMappingConeBottomSquare_eq_zero_or_eq_top :
    hopfMappingConeBottomSquare = 0 ∨
      hopfMappingConeBottomSquare = hopfMappingConeTopClass :=
  hopfMappingConeClass_eq_zero_or_eq_top hopfMappingConeBottomSquare

/-- Nonvanishing of the bottom square is equivalent to its being the normalized top class. -/
theorem hopfMappingConeBottomSquare_eq_top_iff_ne_zero :
    hopfMappingConeBottomSquare = hopfMappingConeTopClass ↔
      hopfMappingConeBottomSquare ≠ 0 := by
  constructor
  · intro htop hzero
    apply hopfMappingConeTopClass_ne_zero
    rw [← htop, hzero]
  · exact hopfMappingConeBottomSquare_eq_zero_or_eq_top.resolve_left

/-! ### A chain-level Hopf-invariant target -/

/-- A cycle representative of the selected degree-four mapping-cone homology generator. -/
noncomputable def hopfCanonicalFourCycleSub : cyclesSub (Csing hopfMappingCone) 4 :=
  Classical.choose
    (homologyMkHom_surjective
      (K := Csing hopfMappingCone) (i := 4) hopfMappingConeHomologyGenerator)

/-- The underlying degree-four singular chain of the canonical cycle representative. -/
noncomputable abbrev hopfCanonicalFourCycle : (Csing hopfMappingCone).X 4 :=
  hopfCanonicalFourCycleSub

/-- The canonical degree-four chain is a cycle. -/
theorem hopfCanonicalFourCycle_isCycle :
    (Csing hopfMappingCone).d 4
      ((ComplexShape.down ℕ).next 4) hopfCanonicalFourCycle = 0 :=
  hopfCanonicalFourCycleSub.2

/-- The homology class of the canonical cycle is the selected generator. -/
@[simp]
theorem homologyMk_hopfCanonicalFourCycle :
    homologyMk hopfCanonicalFourCycle hopfCanonicalFourCycle_isCycle =
      hopfMappingConeHomologyGenerator := by
  change homologyMkHom (Csing hopfMappingCone) 4 hopfCanonicalFourCycleSub =
    hopfMappingConeHomologyGenerator
  exact Classical.choose_spec
    (homologyMkHom_surjective
      (K := Csing hopfMappingCone) (i := 4) hopfMappingConeHomologyGenerator)

set_option backward.isDefEq.respectTransparency false in
/-- The Hopf invariant is one exactly when the bottom square evaluates to one on the normalized
top homology generator. -/
theorem hopfMappingConeBottomSquare_eq_top_iff_evaluation_eq_one :
    hopfMappingConeBottomSquare = hopfMappingConeTopClass ↔
      ev (Csing hopfMappingCone) modTwoCoefficients 4
        (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4
          hopfMappingConeBottomSquare)
        hopfMappingConeHomologyGenerator = (1 : ZMod 2) := by
  constructor
  · intro htop
    rw [htop, hopfMappingConeTopClass, AddEquiv.apply_symm_apply,
      hopfMappingConeTopDualClass_evaluation]
  · intro heval
    rcases hopfMappingConeBottomSquare_eq_zero_or_eq_top with hzero | htop
    · rw [hzero, map_zero, map_zero] at heval
      exact (zero_ne_one heval).elim
    · exact htop

set_option backward.isDefEq.respectTransparency false in
/-- The Hopf-invariant-one assertion is exactly one explicit Alexander--Whitney evaluation on
the selected degree-four cycle. -/
theorem hopfMappingConeBottomSquare_eq_top_iff_representativeEvaluation_eq_one :
    hopfMappingConeBottomSquare = hopfMappingConeTopClass ↔
      cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
        hopfMappingConeBottomCocycle hopfMappingConeBottomCocycle
        hopfCanonicalFourCycle = (1 : ZMod 2) := by
  have hvalue := cupHsing_evaluation_homologyMk (R := ZMod 2)
    (by omega : 2 + 2 = 4)
    hopfMappingConeBottomCocycle hopfMappingConeBottomCocycle
    hopfCanonicalFourCycle hopfCanonicalFourCycle_isCycle
  rw [hopfMappingConeBottomCocycle_mk, homologyMk_hopfCanonicalFourCycle] at hvalue
  change ev (Csing hopfMappingCone) modTwoCoefficients 4
      (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4
        hopfMappingConeBottomSquare)
      hopfMappingConeHomologyGenerator =
    cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
      hopfMappingConeBottomCocycle hopfMappingConeBottomCocycle
      hopfCanonicalFourCycle at hvalue
  rw [← hvalue]
  exact hopfMappingConeBottomSquare_eq_top_iff_evaluation_eq_one

/-! ### The cup-square obstruction -/

/-- The square of the normalized degree-two class vanishes on `S²` for dimensional reasons. -/
theorem sphereTwoModTwoClass_cupSquare_eq_zero :
    cupHsing (by omega : 2 + 2 = 4)
      (sphereTopModTwoClass 1) (sphereTopModTwoClass 1) = 0 := by
  letI : Subsingleton (Hsing 4 (TopCat.of (Sph 2)) (ZMod 2)) :=
    subsingleton_Hsing_sphere (ZMod 2) 4 2 (by omega) (by omega)
  exact Subsingleton.elim _ _

/-- A nonzero bottom square proves that the concrete quadratic Hopf map is not based
nullhomotopic. -/
theorem hopfMap_not_nullhomotopic_of_bottomSquare_ne_zero
    (hSq : hopfMappingConeBottomSquare ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy hopfTopCat (TopCat.const (sphereBasepoint 2))) := by
  intro H
  apply not_exists_nullhomotopy_of_mappingCone_cupSquareDegreeTwo
    hopfTopCat (sphereTopModTwoClass 1) hopfMappingConeBottomClass
    hopfMappingConeBottomClass_restrict hopfMappingConeIncl_bijective.1
    sphereTwoModTwoClass_cupSquare_eq_zero (by
      simpa only [hopfMappingConeBottomSquare] using hSq)
  let p : 𝟙_ TopCat.{0} ⟶ TopCat.of (Sph 2) :=
    TopCat.const (sphereBasepoint 2)
  have hp : toUnit (TopCat.of (Sph 3)) ≫ p =
      TopCat.const (sphereBasepoint 2) := by
    ext z
    rfl
  exact ⟨p, H.map fun K ↦ K.cast rfl
    (congrArg
      (fun q : TopCat.of (Sph 3) ⟶ TopCat.of (Sph 2) ↦ q.hom)
      hp.symm)⟩

/-- Hopf invariant one proves that the concrete quadratic Hopf map is not based nullhomotopic. -/
theorem hopfMap_not_nullhomotopic_of_bottomSquare_eq_top
    (hSq : hopfMappingConeBottomSquare = hopfMappingConeTopClass) :
    ¬ Nonempty
      (TopCat.Homotopy hopfTopCat (TopCat.const (sphereBasepoint 2))) :=
  hopfMap_not_nullhomotopic_of_bottomSquare_ne_zero (by
    rw [hSq]
    exact hopfMappingConeTopClass_ne_zero)

/-- The explicit Alexander--Whitney evaluation equal to one proves that the concrete quadratic
Hopf map is not based nullhomotopic. -/
theorem hopfMap_not_nullhomotopic_of_representativeEvaluation_eq_one
    (heval : cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
      hopfMappingConeBottomCocycle hopfMappingConeBottomCocycle
      hopfCanonicalFourCycle = (1 : ZMod 2)) :
    ¬ Nonempty
      (TopCat.Homotopy hopfTopCat (TopCat.const (sphereBasepoint 2))) :=
  hopfMap_not_nullhomotopic_of_bottomSquare_eq_top
    (hopfMappingConeBottomSquare_eq_top_iff_representativeEvaluation_eq_one.mpr heval)

end Submission
