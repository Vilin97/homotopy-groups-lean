/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlanePuppe
import Submission.HopfMappingCone

/-!
# The mod-two cohomology classes of the complex projective plane

This file identifies the geometric complex projective plane with the mapping cone of the
concrete quadratic Hopf map. It transports the normalized degree-two and degree-four
mapping-cone classes to `CP²`, proves their basic normalization properties, and shows that
the projective-plane cup-square identity is exactly the Hopf-invariant-one identity on the
concrete Hopf mapping cone.
-/

open CategoryTheory
open scoped Topology TopCat

noncomputable section

namespace Submission

/-- The boundary of the four-disk in the metric three-sphere coordinate. -/
noncomputable def diskBoundaryFourIsoSphereThree :
    TopCat.diskBoundary.{0} 4 ≅ TopCat.of (Sph 3) :=
  TopCat.isoOfHomeo diskBoundaryFourHomeomorphSphereThree

/-- The complex projective line in the metric two-sphere coordinate. -/
noncomputable def complexProjectiveLineIsoSphereTwo :
    TopCat.of (ComplexProjectiveModel 1) ≅ TopCat.of (Sph 2) :=
  TopCat.isoOfHomeo complexProjectiveLineHomeomorphSphere

/-- Changing the boundary-sphere and projective-line coordinates identifies the exact
projective attaching cone with the concrete Hopf mapping cone. -/
noncomputable def diskBoundaryFourHopfMappingConeIso :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ≅ hopfMappingCone :=
  topologicalMappingConeIso diskBoundaryFourComplexHopfMap hopfTopCat
    diskBoundaryFourIsoSphereThree.hom
    complexProjectiveLineIsoSphereTwo.hom
    diskBoundaryFourComplexHopfMap_is_hopfMap

/-- The geometric mapping-cone homeomorphism as an isomorphism in `TopCat`. -/
noncomputable def complexProjectivePlaneMappingConeIso :
    topologicalMappingCone diskBoundaryFourComplexHopfMap ≅
      TopCat.of (ComplexProjectiveModel 2) :=
  TopCat.isoOfHomeo complexProjectivePlaneMappingConeHomeomorph

/-- The actual projective plane in the concrete Hopf mapping-cone coordinates. -/
noncomputable def complexProjectivePlaneIsoHopfMappingCone :
    TopCat.of (ComplexProjectiveModel 2) ≅ hopfMappingCone :=
  complexProjectivePlaneMappingConeIso.symm.trans
    diskBoundaryFourHopfMappingConeIso

@[reassoc]
theorem diskBoundaryFourHopfMappingConeIso_hom_incl :
    topologicalMappingConeIncl diskBoundaryFourComplexHopfMap ≫
        diskBoundaryFourHopfMappingConeIso.hom =
      complexProjectiveLineIsoSphereTwo.hom ≫
        hopfMappingConeIncl := by
  exact topologicalMappingConeIncl_map diskBoundaryFourComplexHopfMap hopfTopCat
    diskBoundaryFourIsoSphereThree.hom
    complexProjectiveLineIsoSphereTwo.hom
    diskBoundaryFourComplexHopfMap_is_hopfMap

@[reassoc]
theorem complexProjectivePlaneMappingConeIso_hom_incl :
    topologicalMappingConeIncl diskBoundaryFourComplexHopfMap ≫
        complexProjectivePlaneMappingConeIso.hom =
      complexProjectivePlaneBottomInclTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact complexProjectivePlaneMappingConeHomeomorph_incl p

@[reassoc]
theorem complexProjectivePlaneMappingConeIso_inv_bottomIncl :
    complexProjectivePlaneBottomInclTopCat ≫
        complexProjectivePlaneMappingConeIso.inv =
      topologicalMappingConeIncl diskBoundaryFourComplexHopfMap := by
  rw [← complexProjectivePlaneMappingConeIso_hom_incl,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- On the bottom projective line, the projective-plane/Hopf-cone coordinate is the maintained
homeomorphism to the metric two-sphere. -/
@[reassoc]
theorem complexProjectivePlaneIsoHopfMappingCone_hom_bottomIncl :
    complexProjectivePlaneBottomInclTopCat ≫
        complexProjectivePlaneIsoHopfMappingCone.hom =
      complexProjectiveLineIsoSphereTwo.hom ≫
        hopfMappingConeIncl := by
  rw [complexProjectivePlaneIsoHopfMappingCone, Iso.trans_hom,
    Iso.symm_hom, ← Category.assoc,
    complexProjectivePlaneMappingConeIso_inv_bottomIncl,
    diskBoundaryFourHopfMappingConeIso_hom_incl]

/-- The normalized mod-two degree-two class on the geometric projective plane. -/
noncomputable def complexProjectivePlaneModTwoClass :
    Hsing 2 (TopCat.of (ComplexProjectiveModel 2)) (ZMod 2) :=
  Hsing.map complexProjectivePlaneIsoHopfMappingCone.hom 2
    hopfMappingConeBottomClass

/-- The projective-plane class restricts to the normalized class on its bottom projective
line, expressed in metric-sphere coordinates. -/
@[simp]
theorem complexProjectivePlaneModTwoClass_restrict :
    Hsing.map complexProjectivePlaneBottomInclTopCat 2
        complexProjectivePlaneModTwoClass =
      Hsing.map complexProjectiveLineIsoSphereTwo.hom 2
        (sphereTopModTwoClass 1) := by
  rw [complexProjectivePlaneModTwoClass, ← LinearMap.comp_apply,
    ← Hsing.map_comp, complexProjectivePlaneIsoHopfMappingCone_hom_bottomIncl,
    Hsing.map_comp, LinearMap.comp_apply,
    hopfMappingConeBottomClass_restrict]

/-- The normalized projective-plane degree-two class is nonzero. -/
theorem complexProjectivePlaneModTwoClass_ne_zero :
    complexProjectivePlaneModTwoClass ≠ 0 := by
  intro hzero
  apply hopfMappingConeBottomClass_ne_zero
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    complexProjectivePlaneIsoHopfMappingCone.hom 2).1
  rw [map_zero]
  exact hzero

/-- The normalized mod-two top class on the geometric projective plane. -/
noncomputable def complexProjectivePlaneModTwoTopClass :
    Hsing 4 (TopCat.of (ComplexProjectiveModel 2)) (ZMod 2) :=
  Hsing.map complexProjectivePlaneIsoHopfMappingCone.hom 4
    hopfMappingConeTopClass

/-- The normalized projective-plane top class is nonzero. -/
theorem complexProjectivePlaneModTwoTopClass_ne_zero :
    complexProjectivePlaneModTwoTopClass ≠ 0 := by
  intro hzero
  apply hopfMappingConeTopClass_ne_zero
  apply (Hsing.map_bijective_of_isIso (R := ZMod 2)
    complexProjectivePlaneIsoHopfMappingCone.hom 4).1
  rw [map_zero]
  exact hzero

/-- Every degree-four mod-two class on the projective plane is zero or its normalized top
class. -/
theorem complexProjectivePlaneDegreeFourClass_eq_zero_or_eq_top
    (x : Hsing 4 (TopCat.of (ComplexProjectiveModel 2)) (ZMod 2)) :
    x = 0 ∨ x = complexProjectivePlaneModTwoTopClass := by
  let e := complexProjectivePlaneIsoHopfMappingCone
  let x' := Hsing.map e.inv 4 x
  rcases hopfMappingConeClass_eq_zero_or_eq_top x' with hzero | htop
  · left
    apply (Hsing.map_bijective_of_isIso (R := ZMod 2) e.inv 4).1
    rw [map_zero]
    exact hzero
  · right
    apply (Hsing.map_bijective_of_isIso (R := ZMod 2) e.inv 4).1
    change Hsing.map e.inv 4 x =
      Hsing.map e.inv 4 (Hsing.map e.hom 4 hopfMappingConeTopClass)
    rw [← LinearMap.comp_apply, ← Hsing.map_comp, Iso.inv_hom_id,
      Hsing.map_id, LinearMap.id_apply]
    exact htop

/-- The cup square of the normalized projective-plane degree-two class. -/
noncomputable def complexProjectivePlaneModTwoSquare :
    Hsing 4 (TopCat.of (ComplexProjectiveModel 2)) (ZMod 2) :=
  cupHsing (by omega : 2 + 2 = 4)
    complexProjectivePlaneModTwoClass complexProjectivePlaneModTwoClass

/-- Under the exact geometric coordinate, the projective-plane square is the Hopf-cone bottom
square. -/
theorem complexProjectivePlaneModTwoSquare_naturality :
    complexProjectivePlaneModTwoSquare =
      Hsing.map complexProjectivePlaneIsoHopfMappingCone.hom 4
        hopfMappingConeBottomSquare := by
  exact (map_cupHsing (R := ZMod 2)
    complexProjectivePlaneIsoHopfMappingCone.hom
    (by omega : 2 + 2 = 4)
    hopfMappingConeBottomClass hopfMappingConeBottomClass).symm

/-- The geometric projective-plane cup-square identity is exactly the Hopf-invariant-one
identity on the concrete Hopf mapping cone. -/
theorem complexProjectivePlaneModTwoSquare_eq_top_iff :
    complexProjectivePlaneModTwoSquare =
        complexProjectivePlaneModTwoTopClass ↔
      hopfMappingConeBottomSquare = hopfMappingConeTopClass := by
  rw [complexProjectivePlaneModTwoSquare_naturality]
  change Hsing.map complexProjectivePlaneIsoHopfMappingCone.hom 4
      hopfMappingConeBottomSquare =
        Hsing.map complexProjectivePlaneIsoHopfMappingCone.hom 4
          hopfMappingConeTopClass ↔ _
  constructor
  · intro h
    exact (Hsing.map_bijective_of_isIso (R := ZMod 2)
      complexProjectivePlaneIsoHopfMappingCone.hom 4).1 h
  · exact congrArg
      (Hsing.map (R := ZMod 2)
        complexProjectivePlaneIsoHopfMappingCone.hom 4)

/-! ### A chain-level projective-plane target -/

/-- The normalized degree-four integral homology generator on the geometric projective
plane. -/
noncomputable def complexProjectivePlaneHomologyGenerator :
    Hgrp 4 (TopCat.of (ComplexProjectiveModel 2)) :=
  HgrpMap 4 complexProjectivePlaneIsoHopfMappingCone.inv
    hopfMappingConeHomologyGenerator

@[simp]
theorem complexProjectivePlaneHomologyGenerator_map :
    HgrpMap 4 complexProjectivePlaneIsoHopfMappingCone.hom
        complexProjectivePlaneHomologyGenerator =
      hopfMappingConeHomologyGenerator := by
  rw [complexProjectivePlaneHomologyGenerator,
    ← ConcreteCategory.comp_apply, ← HgrpMap_comp,
    Iso.inv_hom_id, HgrpMap_id, ConcreteCategory.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized projective-plane top cohomology class evaluates to one on the normalized
homology generator. -/
theorem complexProjectivePlaneModTwoTopClass_evaluation :
    ev (Csing (TopCat.of (ComplexProjectiveModel 2))) modTwoCoefficients 4
        (HsingEquivDualHomology (ZMod 2)
          (TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneModTwoTopClass)
        complexProjectivePlaneHomologyGenerator = (1 : ZMod 2) := by
  let e := complexProjectivePlaneIsoHopfMappingCone
  have hbridge := HsingEquivDualHomology_naturality (R := ZMod 2)
    e.hom 4 hopfMappingConeTopClass
  have hnat := ev_naturality_apply
    (K := Csing (TopCat.of (ComplexProjectiveModel 2)))
    (L := Csing hopfMappingCone)
    (G := modTwoCoefficients) (i := 4)
    (CsingMap e.hom)
    (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4
      hopfMappingConeTopClass)
  have hnat' := ConcreteCategory.congr_hom hnat
    complexProjectivePlaneHomologyGenerator
  rw [← hbridge] at hnat'
  change ev (Csing (TopCat.of (ComplexProjectiveModel 2)))
      modTwoCoefficients 4
        (HsingEquivDualHomology (ZMod 2)
          (TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneModTwoTopClass)
        complexProjectivePlaneHomologyGenerator =
    ev (Csing hopfMappingCone) modTwoCoefficients 4
      (HsingEquivDualHomology (ZMod 2) hopfMappingCone 4
        hopfMappingConeTopClass)
      (HgrpMap 4 e.hom complexProjectivePlaneHomologyGenerator) at hnat'
  rw [complexProjectivePlaneHomologyGenerator_map,
    hopfMappingConeTopClass, AddEquiv.apply_symm_apply,
    hopfMappingConeTopDualClass_evaluation] at hnat'
  exact hnat'

/-- A fixed singular cocycle representing the normalized degree-two class on `CP²`. -/
noncomputable def complexProjectivePlaneModTwoCocycle :
    cocycles (TopCat.toSSet.obj (TopCat.of (ComplexProjectiveModel 2)))
      (ZMod 2) 2 :=
  Classical.choose (Hcoh.mk_surjective complexProjectivePlaneModTwoClass)

@[simp]
theorem complexProjectivePlaneModTwoCocycle_mk :
    Hcoh.mk complexProjectivePlaneModTwoCocycle =
      complexProjectivePlaneModTwoClass :=
  Classical.choose_spec (Hcoh.mk_surjective complexProjectivePlaneModTwoClass)

/-- A cycle representative of the normalized projective-plane homology generator. -/
noncomputable def complexProjectivePlaneCanonicalFourCycleSub :
    cyclesSub (Csing (TopCat.of (ComplexProjectiveModel 2))) 4 :=
  Classical.choose
    (homologyMkHom_surjective
      (K := Csing (TopCat.of (ComplexProjectiveModel 2))) (i := 4)
      complexProjectivePlaneHomologyGenerator)

/-- The underlying degree-four singular chain of the normalized projective-plane cycle. -/
noncomputable abbrev complexProjectivePlaneCanonicalFourCycle :
    (Csing (TopCat.of (ComplexProjectiveModel 2))).X 4 :=
  complexProjectivePlaneCanonicalFourCycleSub

/-- The canonical projective-plane chain is a cycle. -/
theorem complexProjectivePlaneCanonicalFourCycle_isCycle :
    (Csing (TopCat.of (ComplexProjectiveModel 2))).d 4
      ((ComplexShape.down ℕ).next 4)
      complexProjectivePlaneCanonicalFourCycle = 0 :=
  complexProjectivePlaneCanonicalFourCycleSub.2

/-- The homology class of the canonical cycle is the selected generator. -/
@[simp]
theorem homologyMk_complexProjectivePlaneCanonicalFourCycle :
    homologyMk complexProjectivePlaneCanonicalFourCycle
        complexProjectivePlaneCanonicalFourCycle_isCycle =
      complexProjectivePlaneHomologyGenerator := by
  change homologyMkHom (Csing (TopCat.of (ComplexProjectiveModel 2))) 4
      complexProjectivePlaneCanonicalFourCycleSub =
    complexProjectivePlaneHomologyGenerator
  exact Classical.choose_spec
    (homologyMkHom_surjective
      (K := Csing (TopCat.of (ComplexProjectiveModel 2))) (i := 4)
      complexProjectivePlaneHomologyGenerator)

set_option backward.isDefEq.respectTransparency false in
/-- The projective-plane cup-square identity is exactly one explicit Alexander--Whitney
evaluation on the selected projective-plane cycle. -/
theorem complexProjectivePlaneModTwoSquare_eq_top_iff_representativeEvaluation_eq_one :
    complexProjectivePlaneModTwoSquare = complexProjectivePlaneModTwoTopClass ↔
      cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
        complexProjectivePlaneModTwoCocycle complexProjectivePlaneModTwoCocycle
        complexProjectivePlaneCanonicalFourCycle = (1 : ZMod 2) := by
  have hvalue := cupHsing_evaluation_homologyMk (R := ZMod 2)
    (by omega : 2 + 2 = 4)
    complexProjectivePlaneModTwoCocycle complexProjectivePlaneModTwoCocycle
    complexProjectivePlaneCanonicalFourCycle
    complexProjectivePlaneCanonicalFourCycle_isCycle
  rw [complexProjectivePlaneModTwoCocycle_mk,
    homologyMk_complexProjectivePlaneCanonicalFourCycle] at hvalue
  change ev (Csing (TopCat.of (ComplexProjectiveModel 2)))
      modTwoCoefficients 4
        (HsingEquivDualHomology (ZMod 2)
          (TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneModTwoSquare)
        complexProjectivePlaneHomologyGenerator =
    cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
      complexProjectivePlaneModTwoCocycle complexProjectivePlaneModTwoCocycle
      complexProjectivePlaneCanonicalFourCycle at hvalue
  constructor
  · intro htop
    rw [← hvalue, htop]
    exact complexProjectivePlaneModTwoTopClass_evaluation
  · intro heval
    rcases complexProjectivePlaneDegreeFourClass_eq_zero_or_eq_top
        complexProjectivePlaneModTwoSquare with hzero | htop
    · rw [← hvalue, hzero, map_zero, map_zero] at heval
      exact (zero_ne_one heval).elim
    · exact htop

/-! ### Exact transport of representatives -/

/-- The Hopf-cone bottom cocycle pulled back to the geometric projective plane. -/
noncomputable def complexProjectivePlaneTransportedModTwoCocycle :
    cocycles (TopCat.toSSet.obj (TopCat.of (ComplexProjectiveModel 2)))
      (ZMod 2) 2 :=
  cocyclesMap (ZMod 2)
    (TopCat.toSSet.map complexProjectivePlaneIsoHopfMappingCone.hom) 2
    hopfMappingConeBottomCocycle

@[simp]
theorem complexProjectivePlaneTransportedModTwoCocycle_mk :
    Hcoh.mk complexProjectivePlaneTransportedModTwoCocycle =
      complexProjectivePlaneModTwoClass := by
  rw [complexProjectivePlaneTransportedModTwoCocycle,
    ← Hcoh.map_mk, hopfMappingConeBottomCocycle_mk]
  rfl

/-- The Hopf-cone top cycle transported to the geometric projective plane. -/
noncomputable def complexProjectivePlaneTransportedFourCycle :
    (Csing (TopCat.of (ComplexProjectiveModel 2))).X 4 :=
  (CsingMap complexProjectivePlaneIsoHopfMappingCone.inv).f 4
    hopfCanonicalFourCycle

/-- The transported projective-plane chain is a cycle. -/
theorem complexProjectivePlaneTransportedFourCycle_isCycle :
    (Csing (TopCat.of (ComplexProjectiveModel 2))).d 4
      ((ComplexShape.down ℕ).next 4)
      complexProjectivePlaneTransportedFourCycle = 0 := by
  rw [complexProjectivePlaneTransportedFourCycle,
    ← ConcreteCategory.comp_apply,
    (CsingMap complexProjectivePlaneIsoHopfMappingCone.inv).comm]
  rw [ConcreteCategory.comp_apply, hopfCanonicalFourCycle_isCycle, map_zero]

/-- The transported cycle represents the normalized projective-plane homology generator. -/
@[simp]
theorem homologyMk_complexProjectivePlaneTransportedFourCycle :
    homologyMk complexProjectivePlaneTransportedFourCycle
        complexProjectivePlaneTransportedFourCycle_isCycle =
      complexProjectivePlaneHomologyGenerator := by
  rw [complexProjectivePlaneHomologyGenerator,
    ← homologyMk_hopfCanonicalFourCycle]
  exact (homologyMap_homologyMk
    (CsingMap complexProjectivePlaneIsoHopfMappingCone.inv)
    hopfCanonicalFourCycle hopfCanonicalFourCycle_isCycle
    complexProjectivePlaneTransportedFourCycle_isCycle).symm

/-- Transporting the projective-plane cycle back to the Hopf cone recovers the selected cone
cycle exactly. -/
@[simp]
theorem complexProjectivePlaneTransportedFourCycle_map :
    (CsingMap complexProjectivePlaneIsoHopfMappingCone.hom).f 4
        complexProjectivePlaneTransportedFourCycle =
      hopfCanonicalFourCycle := by
  rw [complexProjectivePlaneTransportedFourCycle,
    ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← CsingMap_comp, Iso.inv_hom_id, CsingMap_id,
    HomologicalComplex.id_f, ConcreteCategory.id_apply]

/-- The exact transported representatives have the same Alexander--Whitney value as the
original Hopf-cone representatives. -/
theorem complexProjectivePlaneTransportedRepresentativeEvaluation :
    cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
        complexProjectivePlaneTransportedModTwoCocycle
        complexProjectivePlaneTransportedModTwoCocycle
        complexProjectivePlaneTransportedFourCycle =
      cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
        hopfMappingConeBottomCocycle hopfMappingConeBottomCocycle
        hopfCanonicalFourCycle := by
  unfold complexProjectivePlaneTransportedModTwoCocycle
  rw [cupHsingRepresentativeEvaluation_natural
    complexProjectivePlaneIsoHopfMappingCone.hom]
  rw [complexProjectivePlaneTransportedFourCycle_map]

/-- With exact transported representatives, the projective-plane cup-square identity is the
original concrete Hopf-cone representative evaluation. -/
theorem complexProjectivePlaneModTwoSquare_eq_top_iff_transportedEvaluation_eq_one :
    complexProjectivePlaneModTwoSquare = complexProjectivePlaneModTwoTopClass ↔
      cupHsingRepresentativeEvaluation (by omega : 2 + 2 = 4)
        complexProjectivePlaneTransportedModTwoCocycle
        complexProjectivePlaneTransportedModTwoCocycle
        complexProjectivePlaneTransportedFourCycle = (1 : ZMod 2) := by
  rw [complexProjectivePlaneTransportedRepresentativeEvaluation,
    complexProjectivePlaneModTwoSquare_eq_top_iff,
    hopfMappingConeBottomSquare_eq_top_iff_representativeEvaluation_eq_one]

end Submission
