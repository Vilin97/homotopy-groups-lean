/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineCofiberTarget
import Submission.Homology.MappingConeCollapse

/-!
# Homology of the projective-line cofiber collapse

Relative excision shows that the abstract collapse of the exact Hopf mapping cone is a
relative-homology isomorphism.  This file transports that result through the maintained
mapping-cone, projective-plane, suspension, and sphere coordinates.  In particular, the
geometric collapse `CP² → S⁴` and the induced map of literal pairs
`(CP², CP¹) → (S⁴, {basepoint})` are isomorphisms in degree four homology.
-/

open CategoryTheory Limits AlgebraicTopology MonoidalCategory
  CartesianMonoidalCategory
open scoped Topology TopCat

noncomputable section

namespace Submission

/-- The tensor unit of `TopCat` is the one-point space, as an explicit categorical
isomorphism. -/
noncomputable def topCatTensorUnitIsoPUnit :
    (𝟙_ TopCat.{0} : TopCat.{0}) ≅ TopCat.of PUnit.{1} :=
  SemiCartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
    TopCat.isTerminalPUnit

/-- Positive-degree homology of the tensor unit of `TopCat` vanishes. -/
theorem isZero_Hgrp_topCatTensorUnit (k : ℕ) (hk : k ≠ 0) :
    IsZero (Hgrp k (𝟙_ TopCat.{0} : TopCat.{0})) :=
  IsZero.of_iso (isZero_Hgrp_punit _ hk)
    (hgrpIsoOfIso k topCatTensorUnitIsoPUnit)

/-- In degree four, the absolute-to-relative map for the exact Hopf mapping-cone pair is an
isomorphism. -/
theorem isIso_relJ_diskBoundaryFourComplexHopfMappingCone_four :
    IsIso (relJ 4
      (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap)) := by
  have h4 : IsZero (Hgrp 4 (TopCat.of (ComplexProjectiveModel 1))) :=
    IsZero.of_iso
      (isZero_Hgrp_sphere 4 2 (by omega) (by omega))
      (hgrpIsoOfIso 4 complexProjectiveLineIsoSphereTwo)
  have h3 : IsZero (Hgrp 3 (TopCat.of (ComplexProjectiveModel 1))) :=
    IsZero.of_iso
      (isZero_Hgrp_sphere 3 2 (by omega) (by omega))
      (hgrpIsoOfIso 3 complexProjectiveLineIsoSphereTwo)
  exact isIso_relJ
    (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap) 3
    (h4.eq_zero_of_src _) (h3.mono _)

/-- In degree four, the absolute-to-relative map for the distinguished point of the abstract
suspension is an isomorphism. -/
theorem isIso_relJ_diskBoundaryFourSuspensionPoint_four :
    IsIso (relJ 4
      (topologicalMappingConeIncl
        (toUnit (TopCat.diskBoundary.{0} 4)))) := by
  exact isIso_relJ
    (topologicalMappingConeIncl
      (toUnit (TopCat.diskBoundary.{0} 4))) 3
    ((isZero_Hgrp_topCatTensorUnit 4 (by omega)).eq_zero_of_src _)
    ((isZero_Hgrp_topCatTensorUnit 3 (by omega)).mono _)

/-- The abstract cofiber collapse of the exact Hopf mapping cone is an isomorphism on fourth
absolute homology. -/
theorem isIso_HgrpMap_diskBoundaryFourComplexHopfMappingConeCollapse_four :
    IsIso (HgrpMap 4
      (topologicalMappingConeCollapseToMappingCone
        diskBoundaryFourComplexHopfMap)) := by
  letI : IsIso (relJ 4
      (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap)) :=
    isIso_relJ_diskBoundaryFourComplexHopfMappingCone_four
  letI : IsIso (relJ 4
      (topologicalMappingConeIncl
        (toUnit (TopCat.diskBoundary.{0} 4)))) :=
    isIso_relJ_diskBoundaryFourSuspensionPoint_four
  letI : IsIso
      (mappingConeCollapseHrelMap diskBoundaryFourComplexHopfMap 4) :=
    isIso_mappingConeCollapseHrelMap diskBoundaryFourComplexHopfMap 4
  have h := relJ_naturality 4
    (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap)
    (topologicalMappingConeIncl (toUnit (TopCat.diskBoundary.{0} 4)))
    (topologicalMappingConeIncl_collapseToMappingCone
      diskBoundaryFourComplexHopfMap)
  change relJ 4 (topologicalMappingConeIncl diskBoundaryFourComplexHopfMap) ≫
      mappingConeCollapseHrelMap diskBoundaryFourComplexHopfMap 4 =
    HgrpMap 4 (topologicalMappingConeCollapseToMappingCone
      diskBoundaryFourComplexHopfMap) ≫
      relJ 4 (topologicalMappingConeIncl
        (toUnit (TopCat.diskBoundary.{0} 4))) at h
  exact IsIso.of_isIso_fac_right h.symm

/-- The maintained suspension-to-sphere homeomorphism as an isomorphism with a literal
mapping-cone source. -/
noncomputable def diskBoundaryFourCofiberSuspensionIsoSphereFour :
    topologicalMappingCone (toUnit (TopCat.diskBoundary.{0} 4)) ≅
      TopCat.of (Sph 4) :=
  TopCat.isoOfHomeo diskBoundaryFourSuspensionHomeomorphSphere

/-- The mapping-cone and geometric projective-plane coordinates identify the abstract cofiber
collapse with the maintained geometric collapse to `S⁴`. -/
theorem complexProjectivePlaneMappingConeIso_collapse_square :
    complexProjectivePlaneMappingConeIso.hom ≫
        complexProjectivePlaneProjectiveLineCollapse =
      topologicalMappingConeCollapseToMappingCone
          diskBoundaryFourComplexHopfMap ≫
        diskBoundaryFourCofiberSuspensionIsoSphereFour.hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm
        (complexProjectivePlaneMappingConeHomeomorph p)) =
    diskBoundaryFourSuspensionHomeomorphSphere
      (topologicalMappingConeCollapseToMappingCone
        diskBoundaryFourComplexHopfMap p)
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm
        (complexProjectivePlaneCellHomeomorph
          (complexProjectivePlaneMappingConeHomeomorphCell p))) = _
  rw [complexProjectivePlaneCellHomeomorph.symm_apply_apply,
    diskBoundaryFourSuspensionHomeomorphSphere_apply]
  exact ConcreteCategory.congr_hom
    complexProjectivePlaneMappingCone_collapse_square p

/-- The geometric projective-line collapse induces an isomorphism on fourth absolute
homology. -/
theorem isIso_HgrpMap_complexProjectivePlaneProjectiveLineCollapse_four :
    IsIso (HgrpMap 4 complexProjectivePlaneProjectiveLineCollapse) := by
  letI : IsIso (HgrpMap 4 complexProjectivePlaneMappingConeIso.hom) := by
    infer_instance
  letI : IsIso (HgrpMap 4
      (topologicalMappingConeCollapseToMappingCone
        diskBoundaryFourComplexHopfMap)) :=
    isIso_HgrpMap_diskBoundaryFourComplexHopfMappingConeCollapse_four
  letI : IsIso (HgrpMap 4 diskBoundaryFourCofiberSuspensionIsoSphereFour.hom) := by
    infer_instance
  have h :
      HgrpMap 4 complexProjectivePlaneMappingConeIso.hom ≫
          HgrpMap 4 complexProjectivePlaneProjectiveLineCollapse =
        HgrpMap 4 (topologicalMappingConeCollapseToMappingCone
            diskBoundaryFourComplexHopfMap) ≫
          HgrpMap 4 diskBoundaryFourCofiberSuspensionIsoSphereFour.hom := by
    rw [← HgrpMap_comp, ← HgrpMap_comp,
      complexProjectivePlaneMappingConeIso_collapse_square]
  exact IsIso.of_isIso_fac_left h

/-- The canonical collapse of the literal pair `(CP², CP¹)` induces an isomorphism on fourth
relative integral homology. -/
theorem isIso_complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse :
    IsIso complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse := by
  let i := subIncl (Y := TopCat.of (ComplexProjectiveModel 2))
    complexProjectivePlaneProjectiveLine
  let j := subIncl (Y := TopCat.of (Sph 4)) sphereFourBasepointSet
  letI : IsIso (relJ 4 i) :=
    complexProjectivePlaneProjectiveLine_isIso_relJ_four
  letI : IsIso (relJ 4 j) :=
    isIso_relJ_singleton 2 (sphereBasepoint 4)
  letI : IsIso
      (HgrpMap 4 complexProjectivePlaneProjectiveLineCollapse) :=
    isIso_HgrpMap_complexProjectivePlaneProjectiveLineCollapse_four
  have h := relJ_naturality 4 i j
    complexProjectivePlaneProjectiveLineCollapsePairMap.subIncl_naturality
  change relJ 4 i ≫
      complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse =
    HgrpMap 4 complexProjectivePlaneProjectiveLineCollapse ≫ relJ 4 j at h
  exact IsIso.of_isIso_fac_left h

/-- Function-level form of the degree-four relative-homology collapse isomorphism. -/
theorem complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse_bijective :
    Function.Bijective
      complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse := by
  letI : IsIso complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse :=
    isIso_complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
  exact ConcreteCategory.bijective_of_isIso
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse

/-- The normalized projective-plane relative generator is sent to a generator of the point
pair: its target coordinate is `1` or `-1`, with the sign depending only on the maintained
orientation comparisons. -/
theorem complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse_generator_coordinate :
    sphereFourPointRelativeHomologyFourIsoInt.hom
          (complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
            complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator) =
        (1 : ℤ) ∨
      sphereFourPointRelativeHomologyFourIsoInt.hom
          (complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
            complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator) =
        (-1 : ℤ) := by
  let φ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.inv ≫
      complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse ≫
        sphereFourPointRelativeHomologyFourIsoInt.hom
  letI : IsIso complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse :=
    isIso_complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
  letI : IsIso φ := by
    dsimp only [φ]
    infer_instance
  have hφ : Function.Bijective φ :=
    ConcreteCategory.bijective_of_isIso φ
  have hsource :
      complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.inv (1 : ℤ) =
        complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator := by
    rw [← complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt_generator]
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply]
  have hφone :
      φ (1 : ℤ) =
        sphereFourPointRelativeHomologyFourIsoInt.hom
          (complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
            complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator) := by
    change sphereFourPointRelativeHomologyFourIsoInt.hom
        (complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
          (complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.inv (1 : ℤ))) = _
    rw [hsource]
  obtain ⟨z, hz⟩ := hφ.2 (1 : ℤ)
  have hmul : φ (1 : ℤ) * z = 1 := by
    calc
      φ (1 : ℤ) * z = z * φ (1 : ℤ) := mul_comm _ _
      _ = z • φ (1 : ℤ) := by rfl
      _ = φ (z • (1 : ℤ)) := by rw [map_zsmul]
      _ = φ z := by
        congr 1
        exact zsmul_one z
      _ = 1 := hz
  rw [hφone] at hmul
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul

/-- The projective-line collapse carries the normalized relative fourth-homology generator to
the maintained sphere generator, up to the unavoidable orientation sign. -/
theorem complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse_generator :
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
          complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator =
        sphereFourPointRelativeHomologyFourGenerator ∨
      complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
          complexProjectivePlaneProjectiveLineRelativeHomologyFourGenerator =
        -sphereFourPointRelativeHomologyFourGenerator := by
  rcases
      complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse_generator_coordinate
      with h | h
  · left
    apply (ConcreteCategory.bijective_of_isIso
      sphereFourPointRelativeHomologyFourIsoInt.hom).1
    rw [sphereFourPointRelativeHomologyFourIsoInt_generator]
    exact h
  · right
    apply (ConcreteCategory.bijective_of_isIso
      sphereFourPointRelativeHomologyFourIsoInt.hom).1
    rw [map_neg, sphereFourPointRelativeHomologyFourIsoInt_generator]
    exact h

end Submission
