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

end Submission
