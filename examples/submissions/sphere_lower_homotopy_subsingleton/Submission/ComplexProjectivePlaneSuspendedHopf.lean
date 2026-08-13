/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlanePuppe
import Submission.SuspendedHopfMap
import Submission.Topology.SuspensionComparison

/-!
# Comparing the exact projective attaching map with the suspended Hopf map

This file transports the suspension of the exact four-cell attaching map through the explicit
boundary-sphere and projective-line-sphere coordinates. The resulting square identifies it
with the quotient-model suspension of the concrete Hopf map.
-/

open CategoryTheory
open scoped Topology TopCat

noncomputable section

namespace Submission

noncomputable local instance : Nonempty (TopCat.diskBoundary.{0} 4) :=
  ⟨diskBoundaryFourHomeomorphSphereThree.symm (sphereBasepoint 3)⟩

/-- The mapping-cone suspension of `∂D⁴`, expressed as the quotient suspension of `S³`. -/
noncomputable def diskBoundaryFourSuspensionIsoHopfSource :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) ≅
      TopCat.of (Susp (Sph 3)) :=
  (topologicalSuspensionIsoSusp (TopCat.diskBoundary 4)).trans
    (TopCat.isoOfHomeo
      (Susp.mapHomeomorph diskBoundaryFourHomeomorphSphereThree))

/-- The mapping-cone suspension of `CP¹`, expressed as the quotient suspension of `S²`. -/
noncomputable def complexProjectiveLineSuspensionIsoHopfTarget :
    topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)) ≅
      TopCat.of (Susp (Sph 2)) :=
  (topologicalSuspensionIsoSusp
      (TopCat.of (ComplexProjectiveModel 1))).trans
    (TopCat.isoOfHomeo
      (Susp.mapHomeomorph complexProjectiveLineHomeomorphSphere))

/-- The suspended projective line in the maintained metric-three-sphere coordinates. -/
noncomputable def complexProjectiveLineSuspensionIsoSphereThree :
    topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)) ≅
      TopCat.of (Sph 3) :=
  complexProjectiveLineSuspensionIsoHopfTarget.trans (suspSphTopCatIso 2)

/-- The suspended four-disk boundary in the maintained metric-four-sphere coordinates. -/
noncomputable def diskBoundaryFourSuspensionIsoSphereFour :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) ≅
      TopCat.of (Sph 4) :=
  diskBoundaryFourSuspensionIsoHopfSource.trans (suspSphTopCatIso 3)

/-- Suspending the exact attaching-map square gives the raw quotient-suspension Hopf square. -/
theorem exactHopfSuspension_raw_square :
    TopCat.ofHom (Susp.map diskBoundaryFourComplexHopfMap.hom) ≫
        TopCat.ofHom (Susp.map
          (complexProjectiveLineHomeomorphSphere :
            C(ComplexProjectiveModel 1, Sph 2))) =
      TopCat.ofHom (Susp.map
          (diskBoundaryFourHomeomorphSphereThree :
            C(TopCat.diskBoundary 4, Sph 3))) ≫
        hopfSuspensionTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  induction q using Susp.ind with
  | h p =>
      rcases p with ⟨t, z⟩
      simp only [ConcreteCategory.comp_apply]
      change Susp.mk
          (t, complexProjectiveLineHomeomorphSphere
            (diskBoundaryFourComplexHopfMap z)) =
        Susp.mk (t, hopfMap (diskBoundaryFourHomeomorphSphereThree z))
      exact congrArg (fun y ↦ (Susp.mk (t, y) : Susp (Sph 2)))
        (ConcreteCategory.congr_hom
          diskBoundaryFourComplexHopfMap_is_hopfMap z)

/-- In mapping-cone suspension coordinates, the exact projective attaching map suspends to the
raw quotient-model suspension of the concrete Hopf map. -/
theorem exactHopfSuspension_comparison :
    topologicalSuspensionMap (TopCat.diskBoundary 4)
          diskBoundaryFourComplexHopfMap ≫
        complexProjectiveLineSuspensionIsoHopfTarget.hom =
      diskBoundaryFourSuspensionIsoHopfSource.hom ≫
        hopfSuspensionTopCat := by
  rw [complexProjectiveLineSuspensionIsoHopfTarget,
    diskBoundaryFourSuspensionIsoHopfSource, Iso.trans_hom,
    Iso.trans_hom]
  change (topologicalSuspensionMap (TopCat.diskBoundary 4)
          diskBoundaryFourComplexHopfMap ≫
        topologicalSuspensionToSusp
          (TopCat.of (ComplexProjectiveModel 1))) ≫
      TopCat.ofHom (Susp.map
        (complexProjectiveLineHomeomorphSphere :
          C(ComplexProjectiveModel 1, Sph 2))) =
    (topologicalSuspensionToSusp (TopCat.diskBoundary 4) ≫
      TopCat.ofHom (Susp.map
        (diskBoundaryFourHomeomorphSphereThree :
          C(TopCat.diskBoundary 4, Sph 3)))) ≫
      hopfSuspensionTopCat
  rw [topologicalSuspensionToSusp_natural]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ topologicalSuspensionToSusp
      (TopCat.diskBoundary 4) ≫ q) exactHopfSuspension_raw_square

/-- The exact suspended attaching map is the concrete suspended Hopf map in metric-sphere
coordinates. -/
theorem exactHopfSuspension_concrete_square :
    topologicalSuspensionMap (TopCat.diskBoundary 4)
          diskBoundaryFourComplexHopfMap ≫
        complexProjectiveLineSuspensionIsoSphereThree.hom =
      diskBoundaryFourSuspensionIsoSphereFour.hom ≫
        suspendedHopfTopCat := by
  rw [complexProjectiveLineSuspensionIsoSphereThree,
    diskBoundaryFourSuspensionIsoSphereFour, Iso.trans_hom, Iso.trans_hom]
  rw [← Category.assoc, exactHopfSuspension_comparison, Category.assoc,
    hopfSuspensionTopCat_naturality, ← Category.assoc]

/-- The exact suspended attaching map is nullhomotopic exactly when the maintained raw
suspended Hopf map is nullhomotopic. -/
theorem exactHopfSuspension_nullhomotopic_iff :
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
        diskBoundaryFourComplexHopfMap).hom.Nullhomotopic ↔
      hopfSuspensionTopCat.hom.Nullhomotopic :=
  nullhomotopic_iff_of_iso_square
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource
    complexProjectiveLineSuspensionIsoHopfTarget
    exactHopfSuspension_comparison

/-- The raw quotient-model suspension of the Hopf map is nullhomotopic exactly when its concrete
sphere-coordinate representative is. -/
theorem hopfSuspension_nullhomotopic_iff_suspendedHopf :
    hopfSuspensionTopCat.hom.Nullhomotopic ↔
      suspendedHopfTopCat.hom.Nullhomotopic :=
  nullhomotopic_iff_of_iso_square hopfSuspensionTopCat suspendedHopfTopCat
    (suspSphTopCatIso 3) (suspSphTopCatIso 2)
    hopfSuspensionTopCat_naturality

/-- Nullhomotopy of the exact suspended projective attaching map is equivalent to nullhomotopy
of the concrete suspended quadratic Hopf map. -/
theorem exactHopfSuspension_nullhomotopic_iff_suspendedHopf :
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
        diskBoundaryFourComplexHopfMap).hom.Nullhomotopic ↔
      suspendedHopfTopCat.hom.Nullhomotopic :=
  exactHopfSuspension_nullhomotopic_iff.trans
    hopfSuspension_nullhomotopic_iff_suspendedHopf

/-- The mapping cone of the suspended exact attaching map, before changing sphere coordinates. -/
noncomputable abbrev exactHopfSuspensionMappingCone : TopCat.{0} :=
  topologicalMappingCone
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)

/-- Changing the suspension coordinates identifies the mapping cone of the exact attaching map
with the raw suspended-Hopf mapping cone. -/
noncomputable def exactHopfSuspensionMappingConeIso :
    exactHopfSuspensionMappingCone ≅ hopfSuspensionMappingCone :=
  topologicalMappingConeIso
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

/-- The same coordinate change, followed by the chosen suspension-sphere coordinates, identifies
the exact suspended attaching cone with the concrete suspended-Hopf cone. -/
noncomputable def exactHopfSuspensionMappingConeIsoConcrete :
    exactHopfSuspensionMappingCone ≅ suspendedHopfMappingCone :=
  exactHopfSuspensionMappingConeIso.trans hopfSuspensionMappingConeIso

@[reassoc]
theorem exactHopfSuspensionMappingConeIso_hom_incl :
    topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫
        exactHopfSuspensionMappingConeIso.hom =
      complexProjectiveLineSuspensionIsoHopfTarget.hom ≫
        topologicalMappingConeIncl hopfSuspensionTopCat := by
  exact topologicalMappingConeIncl_map
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

@[reassoc]
theorem exactHopfSuspensionMappingConeIso_hom_coneIncl :
    topologicalMappingConeConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫
        exactHopfSuspensionMappingConeIso.hom =
      topologicalConeMap diskBoundaryFourSuspensionIsoHopfSource.hom ≫
        topologicalMappingConeConeIncl hopfSuspensionTopCat := by
  exact topologicalMappingConeConeIncl_map
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

/-- On the bottom summand, the exact-to-concrete mapping-cone isomorphism is the composite
suspension coordinate. -/
@[reassoc]
theorem exactHopfSuspensionMappingConeIsoConcrete_hom_incl :
    topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫
        exactHopfSuspensionMappingConeIsoConcrete.hom =
      complexProjectiveLineSuspensionIsoSphereThree.hom ≫
        suspendedHopfMappingConeIncl := by
  rw [exactHopfSuspensionMappingConeIsoConcrete, Iso.trans_hom,
    complexProjectiveLineSuspensionIsoSphereThree, Iso.trans_hom]
  rw [← Category.assoc, exactHopfSuspensionMappingConeIso_hom_incl,
    Category.assoc, hopfSuspensionMappingConeIso_hom_incl, ← Category.assoc]

/-! ### Cohomological transport to the exact projective attaching cone -/

/-- The canonical degree-three suspended-Hopf class pulled back to the exact projective
attaching cone. -/
noncomputable def exactHopfSuspensionCanonicalLift :
    Hsing 3 exactHopfSuspensionMappingCone (ZMod 2) :=
  Hsing.map exactHopfSuspensionMappingConeIsoConcrete.hom 3
    suspendedHopfCanonicalLift

/-- The exact-cone class restricts to the pullback of the normalized metric-sphere class. -/
@[simp]
theorem exactHopfSuspensionCanonicalLift_restrict :
    Hsing.map
        (topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap)) 3
        exactHopfSuspensionCanonicalLift =
      Hsing.map complexProjectiveLineSuspensionIsoSphereThree.hom 3
        sphereThreeModTwoClass := by
  rw [exactHopfSuspensionCanonicalLift, ← LinearMap.comp_apply,
    ← Hsing.map_comp, exactHopfSuspensionMappingConeIsoConcrete_hom_incl,
    Hsing.map_comp, LinearMap.comp_apply, suspendedHopfCanonicalLift_restrict]

/-- The exact-cone canonical degree-three class is nonzero. -/
theorem exactHopfSuspensionCanonicalLift_ne_zero :
    exactHopfSuspensionCanonicalLift ≠ 0 := by
  intro hzero
  apply suspendedHopfCanonicalLift_ne_zero
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    exactHopfSuspensionMappingConeIsoConcrete.hom 3).1
  rw [map_zero]
  exact hzero

/-- The normalized degree-five class pulled back to the exact projective attaching cone. -/
noncomputable def exactHopfSuspensionMappingConeTopClass :
    Hsing 5 exactHopfSuspensionMappingCone (ZMod 2) :=
  Hsing.map exactHopfSuspensionMappingConeIsoConcrete.hom 5
    suspendedHopfMappingConeTopClass

/-- The exact-cone normalized top class is nonzero. -/
theorem exactHopfSuspensionMappingConeTopClass_ne_zero :
    exactHopfSuspensionMappingConeTopClass ≠ 0 := by
  intro hzero
  apply suspendedHopfMappingConeTopClass_ne_zero
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    exactHopfSuspensionMappingConeIsoConcrete.hom 5).1
  rw [map_zero]
  exact hzero

/-- Every degree-five mod-two class on the exact suspended projective attaching cone is zero or
its normalized top class. -/
theorem exactHopfSuspensionMappingConeClass_eq_zero_or_eq_top
    (x : Hsing 5 exactHopfSuspensionMappingCone (ZMod 2)) :
    x = 0 ∨ x = exactHopfSuspensionMappingConeTopClass := by
  let e := exactHopfSuspensionMappingConeIsoConcrete
  let x' := Hsing.map e.inv 5 x
  rcases suspendedHopfMappingConeClass_eq_zero_or_eq_top x' with hzero | htop
  · left
    apply (Hsing.map_bijective_of_isIso (R := ZMod 2) e.inv 5).1
    rw [map_zero]
    exact hzero
  · right
    apply (Hsing.map_bijective_of_isIso (R := ZMod 2) e.inv 5).1
    change Hsing.map e.inv 5 x =
      Hsing.map e.inv 5
        (Hsing.map e.hom 5 suspendedHopfMappingConeTopClass)
    rw [← LinearMap.comp_apply, ← Hsing.map_comp, Iso.inv_hom_id,
      Hsing.map_id, LinearMap.id_apply]
    exact htop

/-- Normalized additive coordinate on degree-five mod-two cohomology of the exact suspended
projective attaching cone. -/
noncomputable def exactHopfSuspensionMappingConeDegreeFiveCohomologyEquivModTwo :
    Hsing 5 exactHopfSuspensionMappingCone (ZMod 2) ≃+ ZMod 2 :=
  addEquivZModTwoOfGenerator exactHopfSuspensionMappingConeTopClass
    exactHopfSuspensionMappingConeClass_eq_zero_or_eq_top
    exactHopfSuspensionMappingConeTopClass_ne_zero

/-- The normalized exact-cone top class has degree-five coordinate one. -/
@[simp]
theorem exactHopfSuspensionMappingConeDegreeFiveCohomologyEquivModTwo_top :
    exactHopfSuspensionMappingConeDegreeFiveCohomologyEquivModTwo
      exactHopfSuspensionMappingConeTopClass = 1 :=
  addEquivZModTwoOfGenerator_apply_generator _ _ _

/-- `Sq²` commutes with the exact-to-concrete mapping-cone coordinate change. -/
theorem exactHopfSuspensionCanonicalLift_sqTwo_naturality :
    sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift =
      Hsing.map exactHopfSuspensionMappingConeIsoConcrete.hom 5
        (sqTwoHsingDegreeThree suspendedHopfCanonicalLift) := by
  exact (sqTwoHsingDegreeThree_natural
    exactHopfSuspensionMappingConeIsoConcrete.hom
    suspendedHopfCanonicalLift).symm

/-- The normalized top-degree coordinate of `Sq²` on the exact suspended projective attaching
cone. -/
noncomputable def exactHopfSuspensionModTwoSqTwoInvariant : ZMod 2 :=
  exactHopfSuspensionMappingConeDegreeFiveCohomologyEquivModTwo
    (sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift)

/-- Exact projective transport preserves the normalized suspended `Sq²` invariant. -/
theorem exactHopfSuspensionModTwoSqTwoInvariant_eq_suspendedHopfInvariant :
    exactHopfSuspensionModTwoSqTwoInvariant =
      suspendedHopfModTwoSqTwoInvariant := by
  rw [exactHopfSuspensionModTwoSqTwoInvariant,
    exactHopfSuspensionCanonicalLift_sqTwo_naturality,
    suspendedHopfModTwoSqTwoInvariant]
  let f : Hsing 5 suspendedHopfMappingCone (ZMod 2) →+
      Hsing 5 exactHopfSuspensionMappingCone (ZMod 2) :=
    (Hsing.map (R := ZMod 2)
      exactHopfSuspensionMappingConeIsoConcrete.hom 5).toAddHom
  have htop : f suspendedHopfMappingConeTopClass =
      exactHopfSuspensionMappingConeTopClass := rfl
  exact addEquivZModTwoOfGenerator_natural
    suspendedHopfMappingConeTopClass exactHopfSuspensionMappingConeTopClass
    suspendedHopfMappingConeClass_eq_zero_or_eq_top
    suspendedHopfMappingConeTopClass_ne_zero
    exactHopfSuspensionMappingConeClass_eq_zero_or_eq_top
    exactHopfSuspensionMappingConeTopClass_ne_zero
    f htop (sqTwoHsingDegreeThree suspendedHopfCanonicalLift)

/-- The exact suspended-projective invariant is one exactly when its canonical `Sq²` is the
normalized top class. -/
theorem exactHopfSuspensionModTwoSqTwoInvariant_eq_one_iff :
    exactHopfSuspensionModTwoSqTwoInvariant = 1 ↔
      sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift =
        exactHopfSuspensionMappingConeTopClass :=
  addEquivZModTwoOfGenerator_apply_eq_one_iff _ _ _ _

/-- The normalized `Sq²` identity is unchanged between the exact projective attaching cone and
the concrete suspended-Hopf cone. -/
theorem exactHopfSuspensionCanonicalLift_sqTwo_eq_top_iff :
    sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift =
        exactHopfSuspensionMappingConeTopClass ↔
      sqTwoHsingDegreeThree suspendedHopfCanonicalLift =
        suspendedHopfMappingConeTopClass := by
  rw [exactHopfSuspensionCanonicalLift_sqTwo_naturality]
  change Hsing.map exactHopfSuspensionMappingConeIsoConcrete.hom 5
      (sqTwoHsingDegreeThree suspendedHopfCanonicalLift) =
        Hsing.map exactHopfSuspensionMappingConeIsoConcrete.hom 5
          suspendedHopfMappingConeTopClass ↔ _
  constructor
  · intro h
    exact (Hsing.map_bijective_of_isIso (R := ZMod 2)
      exactHopfSuspensionMappingConeIsoConcrete.hom 5).1 h
  · exact congrArg
      (Hsing.map (R := ZMod 2)
        exactHopfSuspensionMappingConeIsoConcrete.hom 5)

/-- Nonvanishing of the canonical square is unchanged by the exact projective mapping-cone
coordinate change. -/
theorem exactHopfSuspensionCanonicalLift_sqTwo_ne_zero_iff :
    sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift ≠ 0 ↔
      sqTwoHsingDegreeThree suspendedHopfCanonicalLift ≠ 0 := by
  rw [exactHopfSuspensionCanonicalLift_sqTwo_naturality]
  constructor
  · intro hmapped hzero
    apply hmapped
    rw [hzero, map_zero]
  · intro hconcrete hmapped
    apply hconcrete
    apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
      exactHopfSuspensionMappingConeIsoConcrete.hom 5).1
    rw [map_zero]
    exact hmapped

/-- The exact projective-cone `Sq²` identity is equivalent to the single maintained cup-one
evaluation on the concrete suspended-Hopf cone. -/
theorem exactHopfSuspensionCanonicalLift_sqTwo_eq_top_iff_evaluation_eq_one :
    sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift =
        exactHopfSuspensionMappingConeTopClass ↔
      sqTwoHsingDegreeThreeRepresentativeEvaluation
        suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle = 1 :=
  exactHopfSuspensionCanonicalLift_sqTwo_eq_top_iff.trans
    suspendedHopfCanonicalLift_sqTwo_eq_top_iff_evaluation_eq_one

/-! ### Exact transport of the cup-one representatives -/

/-- The normalized degree-five homology generator on the exact suspended projective cone. -/
noncomputable def exactHopfSuspensionMappingConeHomologyGenerator :
    Hgrp 5 exactHopfSuspensionMappingCone :=
  HgrpMap 5 exactHopfSuspensionMappingConeIsoConcrete.inv
    suspendedHopfMappingConeHomologyGenerator

@[simp]
theorem exactHopfSuspensionMappingConeHomologyGenerator_map :
    HgrpMap 5 exactHopfSuspensionMappingConeIsoConcrete.hom
        exactHopfSuspensionMappingConeHomologyGenerator =
      suspendedHopfMappingConeHomologyGenerator := by
  rw [exactHopfSuspensionMappingConeHomologyGenerator,
    ← ConcreteCategory.comp_apply, ← HgrpMap_comp,
    Iso.inv_hom_id, HgrpMap_id, ConcreteCategory.id_apply]

/-- The canonical suspended-Hopf cocycle pulled back to the exact projective cone. -/
noncomputable def exactHopfSuspensionTransportedCanonicalCocycle :
    cocycles (TopCat.toSSet.obj exactHopfSuspensionMappingCone) (ZMod 2) 3 :=
  cocyclesMap (ZMod 2)
    (TopCat.toSSet.map exactHopfSuspensionMappingConeIsoConcrete.hom) 3
    suspendedHopfCanonicalCocycle

@[simp]
theorem exactHopfSuspensionTransportedCanonicalCocycle_mk :
    Hcoh.mk exactHopfSuspensionTransportedCanonicalCocycle =
      exactHopfSuspensionCanonicalLift := by
  rw [exactHopfSuspensionTransportedCanonicalCocycle,
    ← Hcoh.map_mk, suspendedHopfCanonicalCocycle_mk]
  rfl

/-- The canonical suspended-Hopf five-cycle transported to the exact projective cone. -/
noncomputable def exactHopfSuspensionTransportedFiveCycle :
    (Csing exactHopfSuspensionMappingCone).X 5 :=
  (CsingMap exactHopfSuspensionMappingConeIsoConcrete.inv).f 5
    suspendedHopfCanonicalFiveCycle

/-- The transported degree-five chain is a cycle. -/
theorem exactHopfSuspensionTransportedFiveCycle_isCycle :
    (Csing exactHopfSuspensionMappingCone).d 5
      ((ComplexShape.down ℕ).next 5)
      exactHopfSuspensionTransportedFiveCycle = 0 := by
  rw [exactHopfSuspensionTransportedFiveCycle,
    ← ConcreteCategory.comp_apply,
    (CsingMap exactHopfSuspensionMappingConeIsoConcrete.inv).comm]
  rw [ConcreteCategory.comp_apply, suspendedHopfCanonicalFiveCycle_isCycle, map_zero]

/-- The transported cycle represents the normalized exact-cone homology generator. -/
@[simp]
theorem homologyMk_exactHopfSuspensionTransportedFiveCycle :
    homologyMk exactHopfSuspensionTransportedFiveCycle
        exactHopfSuspensionTransportedFiveCycle_isCycle =
      exactHopfSuspensionMappingConeHomologyGenerator := by
  rw [exactHopfSuspensionMappingConeHomologyGenerator,
    ← homologyMk_suspendedHopfCanonicalFiveCycle]
  exact (homologyMap_homologyMk
    (CsingMap exactHopfSuspensionMappingConeIsoConcrete.inv)
    suspendedHopfCanonicalFiveCycle suspendedHopfCanonicalFiveCycle_isCycle
    exactHopfSuspensionTransportedFiveCycle_isCycle).symm

/-- Transporting the exact-cone cycle back recovers the selected suspended-Hopf cycle. -/
@[simp]
theorem exactHopfSuspensionTransportedFiveCycle_map :
    (CsingMap exactHopfSuspensionMappingConeIsoConcrete.hom).f 5
        exactHopfSuspensionTransportedFiveCycle =
      suspendedHopfCanonicalFiveCycle := by
  rw [exactHopfSuspensionTransportedFiveCycle,
    ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← CsingMap_comp, Iso.inv_hom_id, CsingMap_id,
    HomologicalComplex.id_f, ConcreteCategory.id_apply]

/-- The exact transported representatives retain the canonical cup-one value. -/
theorem exactHopfSuspensionTransportedRepresentativeEvaluation :
    sqTwoHsingDegreeThreeRepresentativeEvaluation
        exactHopfSuspensionTransportedCanonicalCocycle
        exactHopfSuspensionTransportedFiveCycle =
      sqTwoHsingDegreeThreeRepresentativeEvaluation
        suspendedHopfCanonicalCocycle suspendedHopfCanonicalFiveCycle := by
  unfold exactHopfSuspensionTransportedCanonicalCocycle
  rw [sqTwoHsingDegreeThreeRepresentativeEvaluation_natural
    exactHopfSuspensionMappingConeIsoConcrete.hom]
  rw [exactHopfSuspensionTransportedFiveCycle_map]

/-- The normalized exact suspended-projective invariant is precisely its transported cup-one
representative evaluation. -/
theorem exactHopfSuspensionModTwoSqTwoInvariant_eq_transportedEvaluation :
    exactHopfSuspensionModTwoSqTwoInvariant =
      sqTwoHsingDegreeThreeRepresentativeEvaluation
        exactHopfSuspensionTransportedCanonicalCocycle
        exactHopfSuspensionTransportedFiveCycle := by
  rw [exactHopfSuspensionModTwoSqTwoInvariant_eq_suspendedHopfInvariant,
    exactHopfSuspensionTransportedRepresentativeEvaluation,
    suspendedHopfModTwoSqTwoInvariant_eq_representativeEvaluation]

/-- The exact projective-cone square identity is precisely the transported cup-one evaluation. -/
theorem exactHopfSuspensionCanonicalLift_sqTwo_eq_top_iff_transportedEvaluation_eq_one :
    sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift =
        exactHopfSuspensionMappingConeTopClass ↔
      sqTwoHsingDegreeThreeRepresentativeEvaluation
        exactHopfSuspensionTransportedCanonicalCocycle
        exactHopfSuspensionTransportedFiveCycle = 1 := by
  rw [exactHopfSuspensionTransportedRepresentativeEvaluation,
    exactHopfSuspensionCanonicalLift_sqTwo_eq_top_iff_evaluation_eq_one]

/-- Retractions of the exact suspended attaching-cone inclusion are equivalent to retractions of
the concrete suspended-Hopf cone inclusion. -/
theorem exists_exactHopfSuspensionMappingConeIncl_retraction_iff :
    (∃ r : exactHopfSuspensionMappingCone ⟶
        topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)),
      topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫ r =
        𝟙 (topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)))) ↔
      ∃ r : suspendedHopfMappingCone ⟶ TopCat.of (Sph 3),
        suspendedHopfMappingConeIncl ≫ r = 𝟙 (TopCat.of (Sph 3)) := by
  rw [exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic,
    exists_topologicalMappingConeIncl_retraction_iff_nullhomotopic,
    exactHopfSuspension_nullhomotopic_iff_suspendedHopf]

/-- The same equivalence holds for retractions in the homotopy category. -/
theorem exists_exactHopfSuspensionMappingConeIncl_homotopy_retraction_iff :
    (∃ r : exactHopfSuspensionMappingCone ⟶
        topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)),
      Nonempty (TopCat.Homotopy
        (topologicalMappingConeIncl
            (topologicalSuspensionMap (TopCat.diskBoundary 4)
              diskBoundaryFourComplexHopfMap) ≫ r)
        (𝟙 (topologicalSuspension
          (TopCat.of (ComplexProjectiveModel 1)))))) ↔
      ∃ r : suspendedHopfMappingCone ⟶ TopCat.of (Sph 3),
        Nonempty (TopCat.Homotopy
          (suspendedHopfMappingConeIncl ≫ r) (𝟙 (TopCat.of (Sph 3)))) := by
  rw [exists_topologicalMappingConeIncl_homotopy_retraction_iff_nullhomotopic,
    exists_topologicalMappingConeIncl_homotopy_retraction_iff_nullhomotopic,
    exactHopfSuspension_nullhomotopic_iff_suspendedHopf]

/-- A nonzero canonical square on the exact projective attaching cone rules out a strict
retraction of its bottom inclusion. -/
theorem not_exists_exactHopfSuspensionMappingConeIncl_retraction_of_sqTwo
    (hSq : sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift ≠ 0) :
    ¬ ∃ r : exactHopfSuspensionMappingCone ⟶
        topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)),
      topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫ r =
        𝟙 (topologicalSuspension (TopCat.of (ComplexProjectiveModel 1))) := by
  intro hexact
  have hconcreteSq :
      sqTwoHsingDegreeThree suspendedHopfCanonicalLift ≠ 0 :=
    exactHopfSuspensionCanonicalLift_sqTwo_ne_zero_iff.mp hSq
  have hclass : suspendedHopfMapClass ≠ 1 :=
    suspendedHopfMapClass_ne_one_of_not_nullhomotopic
      (suspendedHopfMap_not_nullhomotopic_of_canonical_sqTwo hconcreteSq)
  exact
    (suspendedHopfMapClass_ne_one_iff_not_exists_mappingConeIncl_retraction.mp hclass)
      (exists_exactHopfSuspensionMappingConeIncl_retraction_iff.mp hexact)

/-- The same exact-cone square obstruction rules out a homotopy retraction. -/
theorem not_exists_exactHopfSuspensionMappingConeIncl_homotopy_retraction_of_sqTwo
    (hSq : sqTwoHsingDegreeThree exactHopfSuspensionCanonicalLift ≠ 0) :
    ¬ ∃ r : exactHopfSuspensionMappingCone ⟶
        topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)),
      Nonempty (TopCat.Homotopy
        (topologicalMappingConeIncl
            (topologicalSuspensionMap (TopCat.diskBoundary 4)
              diskBoundaryFourComplexHopfMap) ≫ r)
        (𝟙 (topologicalSuspension
          (TopCat.of (ComplexProjectiveModel 1))))) := by
  intro hexact
  have hconcreteSq :
      sqTwoHsingDegreeThree suspendedHopfCanonicalLift ≠ 0 :=
    exactHopfSuspensionCanonicalLift_sqTwo_ne_zero_iff.mp hSq
  have hclass : suspendedHopfMapClass ≠ 1 :=
    suspendedHopfMapClass_ne_one_of_not_nullhomotopic
      (suspendedHopfMap_not_nullhomotopic_of_canonical_sqTwo hconcreteSq)
  exact
    (suspendedHopfMapClass_ne_one_iff_not_exists_mappingConeIncl_homotopy_retraction.mp hclass)
      (exists_exactHopfSuspensionMappingConeIncl_homotopy_retraction_iff.mp hexact)

end Submission
