/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.CellAttachmentSqTwo
import Submission.Cohomology.MappingCone
import Submission.Cohomology.MappingConePair
import Submission.Cohomology.SphereTop
import Submission.FirstStableStemPresentation
import Submission.Homology.MappingCone
import Submission.Hurewicz.SphereMappingConeBridge
import Submission.HopfMap
import Submission.HopfMappingCone
import Submission.SphereSuspensionGeneral

/-!
# The suspended Hopf map and its mapping cone

This file suspends the concrete quadratic Hopf map using the explicit reduced-suspension sphere
homeomorphisms.  It names the resulting continuous map `S⁴ ⟶ S³`, its `TopCat` incarnation,
and its mapping cone.  The sphere-side square vanishes because `H⁵(S³; F₂) = 0`.  The cone's
bottom and top classes are normalized against explicit homology generators, and its degree-five
cohomology is shown to have only zero and that top class.  The general degree-three `Sq²`
obstruction therefore specializes to one chain-level calculation: the cup-one square must
evaluate nontrivially on the selected degree-five cycle.

## Main definitions and results

* `Submission.suspendedHopfMap : C(Sph 4, Sph 3)`;
* `Submission.exists_hopfMappingConeIncl_retraction_iff_class_eq_one`;
* `Submission.not_exists_hopfMappingConeIncl_retraction`;
* `Submission.suspendedHopfMapClass_eq_piFourSphereThreeGeometricHopfGenerator`;
* `Submission.suspendedHopfTopCat` and `Submission.suspendedHopfMappingCone`;
* `Submission.hopfSuspensionMappingConeIso`;
* `Submission.hopfSuspensionCanonicalLift_sqTwo_eq_top_iff`;
* `Submission.suspendedHopfMappingConeClass_eq_zero_or_eq_top`;
* `Submission.suspendedHopfCanonicalLift_sqTwo_eq_top_of_cycle_evaluation`;
* `Submission.suspendedHopfCanonicalLift_sqTwo_eq_top_iff_evaluation_eq_one`;
* `Submission.suspendedHopfMap_not_nullhomotopic_of_sqTwo`;
* `Submission.piFourSphereThreeGeometricHopfGenerator_ne_one_of_canonical_evaluation`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

/-- Retraction of the Hopf mapping-cone inclusion is exactly triviality of the concrete Hopf
class. -/
theorem exists_hopfMappingConeIncl_retraction_iff_class_eq_one :
    (∃ r : hopfMappingCone ⟶ TopCat.of (Sph 2),
        hopfMappingConeIncl ≫ r = 𝟙 (TopCat.of (Sph 2))) ↔
      piThreeSphereTwoHopfGenerator = 1 := by
  letI : SimplyConnectedSpace (Sph 2) :=
    simplyConnectedSpace_sph_of_two_le (by omega)
  simpa only [hopfMappingCone, hopfMappingConeIncl, hopfTopCat,
    piThreeSphereTwoHopfGenerator_eq_hopfMapClass] using
      (exists_sphereTargetMappingConeIncl_retraction_iff_class_eq_one
        2 (sphereBasepoint 2) hopfMap hopfMap_basepoint)

/-- The bottom sphere in the Hopf mapping cone is not a retract.  Otherwise the general
mapping-cone converse would make the concrete Hopf attaching map nullhomotopic, contradicting
its computed nontrivial class in `π₃(S²)`. -/
theorem not_exists_hopfMappingConeIncl_retraction :
    ¬ ∃ r : hopfMappingCone ⟶ TopCat.of (Sph 2),
      hopfMappingConeIncl ≫ r = 𝟙 (TopCat.of (Sph 2)) := by
  exact fun h ↦ piThreeSphereTwoHopfGenerator_ne_one
    (exists_hopfMappingConeIncl_retraction_iff_class_eq_one.mp h)

/-- The geometric suspension `S⁴ ⟶ S³` of the concrete quadratic Hopf map. -/
noncomputable def suspendedHopfMap : C(Sph 4, Sph 3) :=
  sphereSuspensionMap 3 2 hopfMap

/-- The suspended Hopf map preserves the chosen sphere basepoints. -/
@[simp]
theorem suspendedHopfMap_basepoint :
    suspendedHopfMap (sphereBasepoint 4) = sphereBasepoint 3 :=
  sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint

/-- The positive-dimensional homotopy class represented by the explicit suspended Hopf map. -/
noncomputable def suspendedHopfMapClass :
    π_ 4 (Sph 3) (sphereBasepoint 3) :=
  sphereTargetMapClass 4 suspendedHopfMap suspendedHopfMap_basepoint

/-- The explicit suspended Hopf map represents the geometric suspension of the original Hopf
map's cubical homotopy class. -/
theorem suspendedHopfMapClass_eq_geometricSuspension :
    suspendedHopfMapClass =
      sphereGeometricSuspension 2 2
        (sphereTargetMapClass 3 hopfMap hopfMap_basepoint) := by
  symm
  simpa only [suspendedHopfMapClass, suspendedHopfMap,
    sphereSuspensionTargetMapClass] using
      sphereGeometricSuspension_sphereTargetMapClass 2 2 hopfMap hopfMap_basepoint

/-- The homotopy class used by the suspended-Hopf cohomology obstruction is the geometric
first-stem generator named in the one-generator presentation. -/
theorem suspendedHopfMapClass_eq_piFourSphereThreeGeometricHopfGenerator :
    suspendedHopfMapClass = piFourSphereThreeGeometricHopfGenerator := by
  calc
    suspendedHopfMapClass =
        sphereGeometricSuspension 2 2
          (sphereTargetMapClass 3 hopfMap hopfMap_basepoint) :=
      suspendedHopfMapClass_eq_geometricSuspension
    _ = sphereGeometricSuspension 2 2 piThreeSphereTwoHopfGenerator :=
      congrArg (sphereGeometricSuspension 2 2)
        piThreeSphereTwoHopfGenerator_eq_hopfMapClass.symm
    _ = piFourSphereThreeGeometricHopfGenerator := rfl

/-- The suspended Hopf map as a morphism of topological spaces. -/
noncomputable def suspendedHopfTopCat :
    TopCat.of (Sph 4) ⟶ TopCat.of (Sph 3) :=
  TopCat.ofHom suspendedHopfMap

/-- Any obstruction to an unbased nullhomotopy of the suspended Hopf map also proves that its
based homotopy-group class is nontrivial. -/
theorem suspendedHopfMapClass_ne_one_of_not_nullhomotopic
    (hnull : ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3)))) :
    suspendedHopfMapClass ≠ 1 := by
  intro hclass
  have hbased :=
    (sphereTargetMapClass_eq_one_iff_basedNullhomotopic 3
      suspendedHopfMap suspendedHopfMap_basepoint).mp hclass
  obtain ⟨H, _⟩ := hbased
  exact hnull ⟨H⟩

/-- Because the target `S³` is simply connected, nontriviality of the explicit suspended-Hopf
class is equivalent to the absence of any free nullhomotopy of its representing map. -/
theorem suspendedHopfMapClass_ne_one_iff_not_nullhomotopic :
    suspendedHopfMapClass ≠ 1 ↔
      ¬ Nonempty
        (TopCat.Homotopy suspendedHopfTopCat
          (TopCat.const (sphereBasepoint 3))) := by
  letI : SimplyConnectedSpace (Sph 3) :=
    simplyConnectedSpace_sph_of_two_le (by omega)
  exact sphereTargetMapClass_ne_one_iff_not_freelyNullhomotopic
    3 suspendedHopfMap suspendedHopfMap_basepoint

/-- The same nullhomotopy obstruction proves that the named geometric first-stem generator is
nontrivial. -/
theorem piFourSphereThreeGeometricHopfGenerator_ne_one_of_not_nullhomotopic
    (hnull : ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3)))) :
    piFourSphereThreeGeometricHopfGenerator ≠ 1 := by
  rw [← suspendedHopfMapClass_eq_piFourSphereThreeGeometricHopfGenerator]
  exact suspendedHopfMapClass_ne_one_of_not_nullhomotopic hnull

/-- The raw unreduced suspension of the Hopf map as a morphism of topological spaces. -/
noncomputable def hopfSuspensionTopCat :
    TopCat.of (Susp (Sph 3)) ⟶ TopCat.of (Susp (Sph 2)) :=
  TopCat.ofHom (Susp.map hopfMap)

/-- The raw suspension of the Hopf map commutes with the chosen sphere coordinates. -/
theorem hopfSuspensionTopCat_naturality :
    hopfSuspensionTopCat ≫ (suspSphTopCatIso 2).hom =
      (suspSphTopCatIso 3).hom ≫ suspendedHopfTopCat := by
  simpa only [hopfSuspensionTopCat, suspendedHopfTopCat, suspendedHopfMap] using
    sphereSuspensionMap_naturality 3 2 hopfMap

/-- The mapping cone of the raw unreduced suspension of the Hopf map. -/
noncomputable abbrev hopfSuspensionMappingCone : TopCat.{0} :=
  topologicalMappingCone hopfSuspensionTopCat

/-- The topological mapping cone of the suspended Hopf map. -/
noncomputable abbrev suspendedHopfMappingCone : TopCat.{0} :=
  topologicalMappingCone suspendedHopfTopCat

/-- The inclusion of the bottom `S³` into the suspended-Hopf mapping cone. -/
noncomputable abbrev suspendedHopfMappingConeIncl :
    TopCat.of (Sph 3) ⟶ suspendedHopfMappingCone :=
  topologicalMappingConeIncl suspendedHopfTopCat

/-- Retraction of the suspended-Hopf mapping-cone inclusion is exactly triviality of its
explicit geometric homotopy class. -/
theorem exists_suspendedHopfMappingConeIncl_retraction_iff_class_eq_one :
    (∃ r : suspendedHopfMappingCone ⟶ TopCat.of (Sph 3),
        suspendedHopfMappingConeIncl ≫ r = 𝟙 (TopCat.of (Sph 3))) ↔
      suspendedHopfMapClass = 1 := by
  letI : SimplyConnectedSpace (Sph 3) :=
    simplyConnectedSpace_sph_of_two_le (by omega)
  simpa only [suspendedHopfMappingCone, suspendedHopfMappingConeIncl,
    suspendedHopfTopCat, suspendedHopfMapClass, Nat.reduceAdd] using
      (exists_sphereTargetMappingConeIncl_retraction_iff_class_eq_one
        3 (sphereBasepoint 3) suspendedHopfMap suspendedHopfMap_basepoint)

/-- Equivalently, the suspended-Hopf class is nontrivial exactly when its mapping-cone bottom
sphere admits no retraction. -/
theorem suspendedHopfMapClass_ne_one_iff_not_exists_mappingConeIncl_retraction :
    suspendedHopfMapClass ≠ 1 ↔
      ¬ ∃ r : suspendedHopfMappingCone ⟶ TopCat.of (Sph 3),
        suspendedHopfMappingConeIncl ≫ r = 𝟙 (TopCat.of (Sph 3)) :=
  (not_congr exists_suspendedHopfMappingConeIncl_retraction_iff_class_eq_one).symm

/-- Transporting source and target through the chosen suspension-sphere homeomorphisms
identifies the raw-suspension mapping cone with the concrete suspended-Hopf mapping cone. -/
noncomputable def hopfSuspensionMappingConeIso :
    hopfSuspensionMappingCone ≅ suspendedHopfMappingCone :=
  topologicalMappingConeIso hopfSuspensionTopCat suspendedHopfTopCat
    (suspSphTopCatIso 3).hom (suspSphTopCatIso 2).hom
    hopfSuspensionTopCat_naturality

/-- On the bottom summand, the suspension-cone coordinate isomorphism is the chosen
suspension-sphere homeomorphism. -/
@[reassoc]
theorem hopfSuspensionMappingConeIso_hom_incl :
    topologicalMappingConeIncl hopfSuspensionTopCat ≫
        hopfSuspensionMappingConeIso.hom =
      (suspSphTopCatIso 2).hom ≫ suspendedHopfMappingConeIncl := by
  exact topologicalMappingConeIncl_map hopfSuspensionTopCat suspendedHopfTopCat
    (suspSphTopCatIso 3).hom (suspSphTopCatIso 2).hom
    hopfSuspensionTopCat_naturality

/-- On the cone summand, the suspension-cone coordinate isomorphism is induced by the chosen
homeomorphism of attaching spheres. -/
@[reassoc]
theorem hopfSuspensionMappingConeIso_hom_coneIncl :
    topologicalMappingConeConeIncl hopfSuspensionTopCat ≫
        hopfSuspensionMappingConeIso.hom =
      topologicalConeMap (suspSphTopCatIso 3).hom ≫
        topologicalMappingConeConeIncl suspendedHopfTopCat := by
  exact topologicalMappingConeConeIncl_map hopfSuspensionTopCat suspendedHopfTopCat
    (suspSphTopCatIso 3).hom (suspSphTopCatIso 2).hom
    hopfSuspensionTopCat_naturality

/-- The fifth homology of the suspended-Hopf mapping cone is infinite cyclic. -/
noncomputable def suspendedHopfMappingConeHomologyIsoInt :
    Hgrp 5 suspendedHopfMappingCone ≅ AddCommGrpCat.of ℤ :=
  mappingConeHomologySuspensionIso suspendedHopfTopCat 3
      (isZero_Hgrp_sphere 5 3 (by omega) (by omega))
      (isZero_Hgrp_sphere 4 3 (by omega) (by omega)) ≪≫
    hgrpSphereSelfIsoZ 3

/-- The degree-five homology generator selected by the mapping-cone suspension isomorphism. -/
noncomputable def suspendedHopfMappingConeHomologyGenerator :
    Hgrp 5 suspendedHopfMappingCone :=
  suspendedHopfMappingConeHomologyIsoInt.inv (1 : ℤ)

@[simp]
theorem suspendedHopfMappingConeHomologyIsoInt_generator :
    suspendedHopfMappingConeHomologyIsoInt.hom
      suspendedHopfMappingConeHomologyGenerator = (1 : ℤ) := by
  rw [suspendedHopfMappingConeHomologyGenerator,
    ← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- The selected degree-five mapping-cone homology generator is nonzero. -/
theorem suspendedHopfMappingConeHomologyGenerator_ne_zero :
    suspendedHopfMappingConeHomologyGenerator ≠ 0 := by
  intro hzero
  have h := congrArg (fun z ↦ suspendedHopfMappingConeHomologyIsoInt.hom z) hzero
  rw [suspendedHopfMappingConeHomologyIsoInt_generator, map_zero] at h
  exact one_ne_zero h

/-! ### The normalized top cohomology class -/

/-- Degree-four mod-two cohomology of `S³` vanishes. -/
theorem isZero_sphereThreeDualCohomology_four :
    IsZero ((homDual (Csing (TopCat.of (Sph 3))) modTwoCoefficients).homology 4) := by
  letI : Subsingleton (Hsing 4 (TopCat.of (Sph 3)) (ZMod 2)) :=
    subsingleton_Hsing_sphere (ZMod 2) 4 3 (by omega) (by omega)
  exact isZero_dualHomology_of_subsingleton_Hsing (ZMod 2) 4

/-- Degree-five mod-two cohomology of `S³` vanishes. -/
theorem isZero_sphereThreeDualCohomology_five :
    IsZero ((homDual (Csing (TopCat.of (Sph 3))) modTwoCoefficients).homology 5) := by
  letI : Subsingleton (Hsing 5 (TopCat.of (Sph 3)) (ZMod 2)) :=
    subsingleton_Hsing_sphere (ZMod 2) 5 3 (by omega) (by omega)
  exact isZero_dualHomology_of_subsingleton_Hsing (ZMod 2) 5

/-- The normalized top mod-two class on the suspended-Hopf mapping cone. -/
noncomputable def suspendedHopfMappingConeTopDualClass :
    (homDual (Csing suspendedHopfMappingCone) modTwoCoefficients).homology 5 :=
  (mappingConeCohomologySuspensionIso suspendedHopfTopCat (ZMod 2) 3
    isZero_sphereThreeDualCohomology_four
    isZero_sphereThreeDualCohomology_five).hom
      (sphereTopModTwoDualClass 3)

set_option backward.isDefEq.respectTransparency false in
/-- The homological mapping-cone suspension sends the selected cone generator to the normalized
top generator of `S⁴`. -/
theorem suspendedHopfMappingConeHomologySuspensionIso_generator :
    (mappingConeHomologySuspensionIso suspendedHopfTopCat 3
      (isZero_Hgrp_sphere 5 3 (by omega) (by omega))
      (isZero_Hgrp_sphere 4 3 (by omega) (by omega))).hom
        suspendedHopfMappingConeHomologyGenerator = sphereTopHomologyClass 3 := by
  rw [sphereTopHomologyClass_eq_generator, suspendedHopfMappingConeHomologyGenerator]
  change (mappingConeHomologySuspensionIso suspendedHopfTopCat 3
      (isZero_Hgrp_sphere 5 3 (by omega) (by omega))
      (isZero_Hgrp_sphere 4 3 (by omega) (by omega))).hom
    ((mappingConeHomologySuspensionIso suspendedHopfTopCat 3
      (isZero_Hgrp_sphere 5 3 (by omega) (by omega))
      (isZero_Hgrp_sphere 4 3 (by omega) (by omega)) ≪≫
        hgrpSphereSelfIsoZ 3).inv (1 : ℤ)) =
      (hgrpSphereSelfIsoZ 3).inv (1 : ℤ)
  rw [Iso.trans_inv, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- The normalized top cone class evaluates to one on the selected integral generator. -/
@[simp]
theorem suspendedHopfMappingConeTopDualClass_evaluation :
    ev (Csing suspendedHopfMappingCone) modTwoCoefficients 5
      suspendedHopfMappingConeTopDualClass suspendedHopfMappingConeHomologyGenerator =
        (1 : ZMod 2) := by
  have h := mappingConeSuspensionIso_adjoint suspendedHopfTopCat (ZMod 2) 3
    (isZero_Hgrp_sphere 5 3 (by omega) (by omega))
    (isZero_Hgrp_sphere 4 3 (by omega) (by omega))
    isZero_sphereThreeDualCohomology_four isZero_sphereThreeDualCohomology_five
    (sphereTopModTwoDualClass 3) suspendedHopfMappingConeHomologyGenerator
  rw [suspendedHopfMappingConeHomologySuspensionIso_generator,
    sphereTopModTwoDualClass_evaluation] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The normalized top cone class is nonzero. -/
theorem suspendedHopfMappingConeTopDualClass_ne_zero :
    suspendedHopfMappingConeTopDualClass ≠ 0 := by
  intro hzero
  have h := suspendedHopfMappingConeTopDualClass_evaluation
  rw [hzero, map_zero] at h
  exact one_ne_zero h.symm

/-- The normalized top cone class in singular cohomology. -/
noncomputable def suspendedHopfMappingConeTopClass :
    Hsing 5 suspendedHopfMappingCone (ZMod 2) :=
  (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5).symm
    suspendedHopfMappingConeTopDualClass

/-- The normalized singular cohomology class is nonzero. -/
theorem suspendedHopfMappingConeTopClass_ne_zero :
    suspendedHopfMappingConeTopClass ≠ 0 := by
  intro hzero
  apply suspendedHopfMappingConeTopDualClass_ne_zero
  have h := congrArg
    (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5) hzero
  rw [suspendedHopfMappingConeTopClass, AddEquiv.apply_symm_apply, map_zero] at h
  exact h

/-- A fixed singular cocycle representing the normalized top class. -/
noncomputable def suspendedHopfMappingConeTopCocycle :
    cocycles (TopCat.toSSet.obj suspendedHopfMappingCone) (ZMod 2) 5 :=
  Classical.choose (Hcoh.mk_surjective suspendedHopfMappingConeTopClass)

/-- The fixed top cocycle represents the normalized top class. -/
@[simp]
theorem suspendedHopfMappingConeTopCocycle_mk :
    Hcoh.mk suspendedHopfMappingConeTopCocycle =
      suspendedHopfMappingConeTopClass :=
  Classical.choose_spec (Hcoh.mk_surjective suspendedHopfMappingConeTopClass)

/-- Every degree-five dual cohomology class of the suspended-Hopf mapping cone is zero or its
normalized top class. -/
theorem suspendedHopfMappingConeDualClass_eq_zero_or_eq_top
    (Φ : (homDual (Csing suspendedHopfMappingCone) modTwoCoefficients).homology 5) :
    Φ = 0 ∨ Φ = suspendedHopfMappingConeTopDualClass := by
  let e := mappingConeCohomologySuspensionIso suspendedHopfTopCat (ZMod 2) 3
    isZero_sphereThreeDualCohomology_four
    isZero_sphereThreeDualCohomology_five
  rcases sphereTopDualClass_eq_zero_or_eq_top 3 (e.inv Φ) with hzero | htop
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

/-- Every degree-five singular cohomology class of the suspended-Hopf mapping cone is zero or
its normalized top class. -/
theorem suspendedHopfMappingConeClass_eq_zero_or_eq_top
    (x : Hsing 5 suspendedHopfMappingCone (ZMod 2)) :
    x = 0 ∨ x = suspendedHopfMappingConeTopClass := by
  rcases suspendedHopfMappingConeDualClass_eq_zero_or_eq_top
      (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5 x) with
    hzero | htop
  · left
    apply (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5).injective
    rw [map_zero]
    exact hzero
  · right
    apply (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5).injective
    rw [suspendedHopfMappingConeTopClass, AddEquiv.apply_symm_apply]
    exact htop

/-- A nonzero degree-five cone class is necessarily the normalized top class. -/
theorem suspendedHopfMappingConeClass_eq_top_of_ne_zero
    {x : Hsing 5 suspendedHopfMappingCone (ZMod 2)} (hx : x ≠ 0) :
    x = suspendedHopfMappingConeTopClass :=
  (suspendedHopfMappingConeClass_eq_zero_or_eq_top x).resolve_left hx

/-- A cycle representative of the selected degree-five mapping-cone homology generator. -/
noncomputable def suspendedHopfCanonicalFiveCycleSub :
    cyclesSub (Csing suspendedHopfMappingCone) 5 :=
  Classical.choose
    (homologyMkHom_surjective
      (K := Csing suspendedHopfMappingCone) (i := 5)
      suspendedHopfMappingConeHomologyGenerator)

/-- The underlying degree-five singular chain of the canonical cycle representative. -/
noncomputable abbrev suspendedHopfCanonicalFiveCycle :
    (Csing suspendedHopfMappingCone).X 5 :=
  suspendedHopfCanonicalFiveCycleSub

/-- The canonical degree-five chain is a cycle. -/
theorem suspendedHopfCanonicalFiveCycle_isCycle :
    (Csing suspendedHopfMappingCone).d 5
      ((ComplexShape.down ℕ).next 5) suspendedHopfCanonicalFiveCycle = 0 :=
  suspendedHopfCanonicalFiveCycleSub.2

/-- The homology class of the canonical cycle is the selected generator. -/
@[simp]
theorem homologyMk_suspendedHopfCanonicalFiveCycle :
    homologyMk suspendedHopfCanonicalFiveCycle
      suspendedHopfCanonicalFiveCycle_isCycle =
        suspendedHopfMappingConeHomologyGenerator := by
  change homologyMkHom (Csing suspendedHopfMappingCone) 5
    suspendedHopfCanonicalFiveCycleSub = suspendedHopfMappingConeHomologyGenerator
  exact Classical.choose_spec
    (homologyMkHom_surjective
      (K := Csing suspendedHopfMappingCone) (i := 5)
      suspendedHopfMappingConeHomologyGenerator)

/-- The normalized top cone class evaluates to one on the canonical degree-five cycle. -/
@[simp]
theorem suspendedHopfMappingConeTopDualClass_canonical_cycle_evaluation :
    ev (Csing suspendedHopfMappingCone) modTwoCoefficients 5
      suspendedHopfMappingConeTopDualClass
      (homologyMk suspendedHopfCanonicalFiveCycle
        suspendedHopfCanonicalFiveCycle_isCycle) = (1 : ZMod 2) := by
  rw [homologyMk_suspendedHopfCanonicalFiveCycle,
    suspendedHopfMappingConeTopDualClass_evaluation]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed top cocycle evaluates to one on the canonical degree-five cycle. -/
@[simp]
theorem suspendedHopfMappingConeTopCocycle_canonical_cycle_evaluation :
    (dualXEquiv (TopCat.toSSet.obj suspendedHopfMappingCone) (ZMod 2) 5).symm
      (suspendedHopfMappingConeTopCocycle :
        Cochain (TopCat.toSSet.obj suspendedHopfMappingCone) (ZMod 2) 5)
      suspendedHopfCanonicalFiveCycle = (1 : ZMod 2) := by
  have hdual :
      HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5
          (Hcoh.mk suspendedHopfMappingConeTopCocycle) =
        suspendedHopfMappingConeTopDualClass := by
    rw [suspendedHopfMappingConeTopCocycle_mk,
      suspendedHopfMappingConeTopClass, AddEquiv.apply_symm_apply]
  have hvalue := congrArg
    (fun Φ ↦ ev (Csing suspendedHopfMappingCone) modTwoCoefficients 5 Φ
      (homologyMk suspendedHopfCanonicalFiveCycle
        suspendedHopfCanonicalFiveCycle_isCycle)) hdual
  change ev (Csing suspendedHopfMappingCone) modTwoCoefficients 5
      (HcohEquivDualHomology
        (TopCat.toSSet.obj suspendedHopfMappingCone) (ZMod 2) 5
          (Hcoh.mk suspendedHopfMappingConeTopCocycle))
      (homologyMk suspendedHopfCanonicalFiveCycle
        suspendedHopfCanonicalFiveCycle_isCycle) =
    ev (Csing suspendedHopfMappingCone) modTwoCoefficients 5
      suspendedHopfMappingConeTopDualClass
      (homologyMk suspendedHopfCanonicalFiveCycle
        suspendedHopfCanonicalFiveCycle_isCycle) at hvalue
  rw [HcohEquivDualHomology_mk, ev_homologyMk,
    evCocycle_homologyMk,
    suspendedHopfMappingConeTopDualClass_canonical_cycle_evaluation] at hvalue
  exact hvalue

/-- The canonical degree-five cycle is nonzero already as a singular chain. -/
theorem suspendedHopfCanonicalFiveCycle_ne_zero :
    suspendedHopfCanonicalFiveCycle ≠ 0 := by
  intro hzero
  apply suspendedHopfMappingConeHomologyGenerator_ne_zero
  rw [← homologyMk_suspendedHopfCanonicalFiveCycle]
  exact (homologyMk_congr suspendedHopfCanonicalFiveCycle_isCycle
    (map_zero _) hzero).trans homologyMk_zero

/-- A degree-three class on the suspended-Hopf cone with nonzero `Sq²` proves that the concrete
suspended Hopf map is not based-nullhomotopic. -/
theorem suspendedHopfMap_not_nullhomotopic_of_sqTwo
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2))
    (u : Hsing 3 suspendedHopfMappingCone (ZMod 2))
    (hu : Hsing.map suspendedHopfMappingConeIncl 3 u = x)
    (hi : Function.Injective
      (Hsing.map (R := ZMod 2) suspendedHopfMappingConeIncl 3))
    (huSq : sqTwoHsingDegreeThree u ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) := by
  intro H
  apply not_exists_nullhomotopy_of_mappingCone_sqTwoDegreeThree
    suspendedHopfTopCat x u hu hi (sqTwoHsingDegreeThree_sphere_three x) huSq
  let p : 𝟙_ TopCat.{0} ⟶ TopCat.of (Sph 3) :=
    TopCat.const (sphereBasepoint 3)
  have hp : toUnit (TopCat.of (Sph 4)) ≫ p =
      TopCat.const (sphereBasepoint 3) := by
    ext z
    rfl
  exact ⟨p, H.map fun K ↦ K.cast rfl
    (congrArg
      (fun q : TopCat.of (Sph 4) ⟶ TopCat.of (Sph 3) ↦ q.hom)
      hp.symm)⟩

/-- Once the suspended-Hopf mapping-cone pair vanishes in degrees three and four, the bottom
restriction is bijective. -/
theorem suspendedHopfMappingConeIncl_bijective_of_relative_vanishing
    (h₃ : IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 3))
    (h₄ : IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 4)) :
    Function.Bijective
      (Hsing.map (R := ZMod 2) suspendedHopfMappingConeIncl 3) :=
  bijective_Hsing_map_of_isZero_HrelCoh
    suspendedHopfMappingConeIncl (ZMod 2) 3 h₃ h₄

/-- Degree-three relative mod-two cohomology of the suspended-Hopf mapping-cone pair vanishes. -/
theorem isZero_HrelCoh_suspendedHopfMappingConeIncl_three :
    IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 3) := by
  simpa using isZero_HrelCoh_mappingConeIncl_sphere
    (ZMod 2) 4 suspendedHopfTopCat 2 (by omega) (by omega)

/-- Degree-four relative mod-two cohomology of the suspended-Hopf mapping-cone pair vanishes. -/
theorem isZero_HrelCoh_suspendedHopfMappingConeIncl_four :
    IsZero (HrelCoh suspendedHopfMappingConeIncl
      (AddCommGrpCat.of (ZMod 2)) 4) := by
  simpa using isZero_HrelCoh_mappingConeIncl_sphere
    (ZMod 2) 4 suspendedHopfTopCat 3 (by omega) (by omega)

/-- Restriction from the suspended-Hopf mapping cone to its bottom `S³` is bijective in
degree three. -/
theorem suspendedHopfMappingConeIncl_bijective :
    Function.Bijective
      (Hsing.map (R := ZMod 2) suspendedHopfMappingConeIncl 3) :=
  suspendedHopfMappingConeIncl_bijective_of_relative_vanishing
    isZero_HrelCoh_suspendedHopfMappingConeIncl_three
    isZero_HrelCoh_suspendedHopfMappingConeIncl_four

/-- The unique degree-three class on the suspended-Hopf mapping cone restricting to `x`. -/
noncomputable def suspendedHopfMappingConeLift
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2)) :
    Hsing 3 suspendedHopfMappingCone (ZMod 2) :=
  Classical.choose (suspendedHopfMappingConeIncl_bijective.2 x)

@[simp]
theorem suspendedHopfMappingConeLift_restrict
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2)) :
    Hsing.map suspendedHopfMappingConeIncl 3
      (suspendedHopfMappingConeLift x) = x :=
  Classical.choose_spec (suspendedHopfMappingConeIncl_bijective.2 x)

/-- The canonical mapping-cone lift of the distinguished nonzero class in
`H³(S³; 𝔽₂)`. -/
noncomputable abbrev suspendedHopfCanonicalLift :
    Hsing 3 suspendedHopfMappingCone (ZMod 2) :=
  suspendedHopfMappingConeLift sphereThreeModTwoClass

/-- The canonical mapping-cone lift restricts to the distinguished sphere class. -/
@[simp]
theorem suspendedHopfCanonicalLift_restrict :
    Hsing.map suspendedHopfMappingConeIncl 3 suspendedHopfCanonicalLift =
      sphereThreeModTwoClass :=
  suspendedHopfMappingConeLift_restrict sphereThreeModTwoClass

/-- The canonical mapping-cone lift is itself nonzero. -/
theorem suspendedHopfCanonicalLift_ne_zero : suspendedHopfCanonicalLift ≠ 0 := by
  intro hzero
  apply sphereThreeModTwoClass_ne_zero
  rw [← suspendedHopfCanonicalLift_restrict, hzero, map_zero]

/-! ### Transport to the raw suspension cone -/

/-- The canonical degree-three class pulled back to the mapping cone of the raw suspension. -/
noncomputable def hopfSuspensionCanonicalLift :
    Hsing 3 hopfSuspensionMappingCone (ZMod 2) :=
  Hsing.map hopfSuspensionMappingConeIso.hom 3 suspendedHopfCanonicalLift

/-- The raw-suspension cone class restricts to the pullback of the normalized sphere class
through the chosen suspension coordinate. -/
@[simp]
theorem hopfSuspensionCanonicalLift_restrict :
    Hsing.map (topologicalMappingConeIncl hopfSuspensionTopCat) 3
        hopfSuspensionCanonicalLift =
      Hsing.map (suspSphTopCatIso 2).hom 3 sphereThreeModTwoClass := by
  rw [hopfSuspensionCanonicalLift, ← LinearMap.comp_apply, ← Hsing.map_comp,
    hopfSuspensionMappingConeIso_hom_incl, Hsing.map_comp,
    LinearMap.comp_apply, suspendedHopfCanonicalLift_restrict]

/-- The transported canonical class on the raw suspension cone is nonzero. -/
theorem hopfSuspensionCanonicalLift_ne_zero : hopfSuspensionCanonicalLift ≠ 0 := by
  intro hzero
  apply suspendedHopfCanonicalLift_ne_zero
  apply (Hsing.map_bijective_of_isIso hopfSuspensionMappingConeIso.hom 3).1
  rw [map_zero]
  exact hzero

/-- The normalized top class pulled back to the mapping cone of the raw suspension. -/
noncomputable def hopfSuspensionMappingConeTopClass :
    Hsing 5 hopfSuspensionMappingCone (ZMod 2) :=
  Hsing.map hopfSuspensionMappingConeIso.hom 5 suspendedHopfMappingConeTopClass

/-- The transported top class on the raw suspension cone is nonzero. -/
theorem hopfSuspensionMappingConeTopClass_ne_zero :
    hopfSuspensionMappingConeTopClass ≠ 0 := by
  intro hzero
  apply suspendedHopfMappingConeTopClass_ne_zero
  apply (Hsing.map_bijective_of_isIso hopfSuspensionMappingConeIso.hom 5).1
  rw [map_zero]
  exact hzero

/-- `Sq²` commutes with transport from the concrete suspended-Hopf cone to the raw suspension
cone. -/
theorem hopfSuspensionCanonicalLift_sqTwo_naturality :
    sqTwoHsingDegreeThree hopfSuspensionCanonicalLift =
      Hsing.map hopfSuspensionMappingConeIso.hom 5
        (sqTwoHsingDegreeThree suspendedHopfCanonicalLift) := by
  exact (sqTwoHsingDegreeThree_natural hopfSuspensionMappingConeIso.hom
    suspendedHopfCanonicalLift).symm

/-- Identifying the concrete suspended-Hopf square with its top class identifies the transported
raw-suspension square with its transported top class. -/
theorem hopfSuspensionCanonicalLift_sqTwo_eq_top_of_concrete
    (hSq : sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
      suspendedHopfMappingConeTopClass) :
    sqTwoHsingDegreeThree hopfSuspensionCanonicalLift =
      hopfSuspensionMappingConeTopClass := by
  rw [hopfSuspensionCanonicalLift_sqTwo_naturality, hSq]
  rfl

/-- The top-square identity is unchanged by passing between the raw suspension cone and the
concrete suspended-Hopf cone. -/
theorem hopfSuspensionCanonicalLift_sqTwo_eq_top_iff :
    sqTwoHsingDegreeThree hopfSuspensionCanonicalLift =
        hopfSuspensionMappingConeTopClass ↔
      sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
        suspendedHopfMappingConeTopClass := by
  rw [hopfSuspensionCanonicalLift_sqTwo_naturality]
  change Hsing.map hopfSuspensionMappingConeIso.hom 5
      (sqTwoHsingDegreeThree suspendedHopfCanonicalLift) =
        Hsing.map hopfSuspensionMappingConeIso.hom 5
          suspendedHopfMappingConeTopClass ↔ _
  constructor
  · intro h
    exact (Hsing.map_bijective_of_isIso (R := ZMod 2)
      hopfSuspensionMappingConeIso.hom 5).1 h
  · intro h
    exact congrArg (Hsing.map (R := ZMod 2) hopfSuspensionMappingConeIso.hom 5) h

/-- A fixed singular cocycle representing the canonical degree-three mapping-cone lift. -/
noncomputable def suspendedHopfCanonicalCocycle :
    cocycles (TopCat.toSSet.obj suspendedHopfMappingCone) (ZMod 2) 3 :=
  Classical.choose (Hcoh.mk_surjective suspendedHopfCanonicalLift)

/-- The chosen cocycle represents the canonical mapping-cone lift. -/
@[simp]
theorem suspendedHopfCanonicalCocycle_mk :
    Hcoh.mk suspendedHopfCanonicalCocycle = suspendedHopfCanonicalLift :=
  Classical.choose_spec (Hcoh.mk_surjective suspendedHopfCanonicalLift)

/-- It is enough to evaluate the cup-one square of the canonical cocycle nontrivially on one
degree-five singular cycle. -/
theorem suspendedHopfCanonicalLift_sqTwo_ne_zero_of_cycle
    (z : (Csing suspendedHopfMappingCone).X 5)
    (hz : (Csing suspendedHopfMappingCone).d 5
      ((ComplexShape.down ℕ).next 5) z = 0)
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle z ≠ 0) :
    sqTwoHsingDegreeThree suspendedHopfCanonicalLift ≠ 0 := by
  rw [← suspendedHopfCanonicalCocycle_mk]
  exact sqTwoHsingDegreeThree_mk_ne_zero_of_eval_cycle
    suspendedHopfCanonicalCocycle z hz heval

/-- A nonzero canonical cup-one evaluation identifies `Sq²` with the normalized top class. -/
theorem suspendedHopfCanonicalLift_sqTwo_eq_top_of_cycle_evaluation
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
      suspendedHopfMappingConeTopClass :=
  suspendedHopfMappingConeClass_eq_top_of_ne_zero
    (suspendedHopfCanonicalLift_sqTwo_ne_zero_of_cycle
      suspendedHopfCanonicalFiveCycle suspendedHopfCanonicalFiveCycle_isCycle heval)

set_option backward.isDefEq.respectTransparency false in
/-- The remaining cup-one calculation is exactly the assertion that the canonical square is
the normalized top class. -/
theorem suspendedHopfCanonicalLift_sqTwo_eq_top_iff_evaluation_eq_one :
    sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
        suspendedHopfMappingConeTopClass ↔
      sqTwoHsingDegreeThreeRepresentativeEvaluation
        suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle = 1 := by
  constructor
  · intro hSq
    have hvalue := sqTwoHsingDegreeThree_evaluation_homologyMk
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle
      suspendedHopfCanonicalFiveCycle_isCycle
    rw [suspendedHopfCanonicalCocycle_mk] at hvalue
    have hdual := congrArg
      (HsingEquivDualHomology (ZMod 2) suspendedHopfMappingCone 5) hSq
    rw [suspendedHopfMappingConeTopClass, AddEquiv.apply_symm_apply] at hdual
    rw [hdual, suspendedHopfMappingConeTopDualClass_canonical_cycle_evaluation]
      at hvalue
    exact hvalue.symm
  · intro heval
    apply suspendedHopfCanonicalLift_sqTwo_eq_top_of_cycle_evaluation
    rw [heval]
    exact one_ne_zero

/-- The remaining Steenrod-square calculation for the canonical lift implies that the suspended
Hopf map is not nullhomotopic. -/
theorem suspendedHopfMap_not_nullhomotopic_of_lift_sqTwo
    (x : Hsing 3 (TopCat.of (Sph 3)) (ZMod 2))
    (hSq : sqTwoHsingDegreeThree (suspendedHopfMappingConeLift x) ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) :=
  suspendedHopfMap_not_nullhomotopic_of_sqTwo x
    (suspendedHopfMappingConeLift x)
    (suspendedHopfMappingConeLift_restrict x)
    suspendedHopfMappingConeIncl_bijective.1 hSq

/-- It now suffices to calculate `Sq²` on one fixed, nonzero mapping-cone class. -/
theorem suspendedHopfMap_not_nullhomotopic_of_canonical_sqTwo
    (hSq : sqTwoHsingDegreeThree suspendedHopfCanonicalLift ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) :=
  suspendedHopfMap_not_nullhomotopic_of_lift_sqTwo sphereThreeModTwoClass hSq

/-- Identifying the canonical square with the normalized top class proves that the suspended
Hopf map is not nullhomotopic. -/
theorem suspendedHopfMap_not_nullhomotopic_of_sqTwo_eq_top
    (hSq : sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
      suspendedHopfMappingConeTopClass) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) :=
  suspendedHopfMap_not_nullhomotopic_of_canonical_sqTwo (by
    rw [hSq]
    exact suspendedHopfMappingConeTopClass_ne_zero)

/-- A nonzero cup-one-square evaluation on a degree-five cycle is the final chain-level
certificate needed to prove that the suspended Hopf map is not nullhomotopic. -/
theorem suspendedHopfMap_not_nullhomotopic_of_canonical_cycle
    (z : (Csing suspendedHopfMappingCone).X 5)
    (hz : (Csing suspendedHopfMappingCone).d 5
      ((ComplexShape.down ℕ).next 5) z = 0)
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle z ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) :=
  suspendedHopfMap_not_nullhomotopic_of_canonical_sqTwo
    (suspendedHopfCanonicalLift_sqTwo_ne_zero_of_cycle z hz heval)

/-- The remaining suspended-Hopf obstruction is a single evaluation of the canonical cup-one
square on the canonical degree-five mapping-cone cycle. -/
theorem suspendedHopfMap_not_nullhomotopic_of_canonical_evaluation
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    ¬ Nonempty
      (TopCat.Homotopy suspendedHopfTopCat
        (TopCat.const (sphereBasepoint 3))) :=
  suspendedHopfMap_not_nullhomotopic_of_canonical_cycle
    suspendedHopfCanonicalFiveCycle suspendedHopfCanonicalFiveCycle_isCycle heval

/-- A nonzero value of the remaining canonical cup-one calculation proves that the geometric
first-stem generator is a nonidentity element of `π₄(S³)`. -/
theorem piFourSphereThreeGeometricHopfGenerator_ne_one_of_canonical_evaluation
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    piFourSphereThreeGeometricHopfGenerator ≠ 1 :=
  piFourSphereThreeGeometricHopfGenerator_ne_one_of_not_nullhomotopic
    (suspendedHopfMap_not_nullhomotopic_of_canonical_evaluation heval)

/-- The same canonical cup-one evaluation proves that the cap-excision edge generator is
nonidentity, without requiring an identification of the two named generators. -/
theorem piFourSphereThreeEdgeGenerator_ne_one_of_canonical_evaluation
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    piFourSphereThreeEdgeGenerator ≠ 1 :=
  piFourSphereThreeEdgeGenerator_ne_one_of_element_ne_one
    piFourSphereThreeGeometricHopfGenerator
    (piFourSphereThreeGeometricHopfGenerator_ne_one_of_canonical_evaluation heval)

/-- The exact first-stem computation now follows from its independent upper and lower halves:
doubling kills the edge generator, while the fixed cup-one evaluation detects a nonidentity
element in the group. -/
theorem piFourSphereThree_mulEquiv_zmod_two_of_edge_square_and_canonical_evaluation
    (hsquare : piFourSphereThreeEdgeGenerator ^ 2 = 1)
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    Nonempty
      (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) :=
  piFourSphereThree_mulEquiv_zmod_two_iff_edge_square_and_nontrivial.mpr
    ⟨hsquare, piFourSphereThreeEdgeGenerator_ne_one_of_canonical_evaluation heval⟩

/-- The same two certificates propagate the `Z/2` computation through every sphere dimension
in the first stable stem. -/
theorem sphere_first_stable_homotopy_mulEquiv_zmod_two_of_edge_square_and_canonical_evaluation
    (n : ℕ) (hn : 3 ≤ n)
    (hsquare : piFourSphereThreeEdgeGenerator ^ 2 = 1)
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation
      suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle ≠ 0) :
    Nonempty
      (π_ (n + 1) (Sph n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  apply sphere_first_stable_homotopy_mulEquiv_zmod_two_of_orderOf_edgeGenerator n hn
  exact orderOf_eq_prime_iff.mpr
    ⟨hsquare, piFourSphereThreeEdgeGenerator_ne_one_of_canonical_evaluation heval⟩

end Submission
