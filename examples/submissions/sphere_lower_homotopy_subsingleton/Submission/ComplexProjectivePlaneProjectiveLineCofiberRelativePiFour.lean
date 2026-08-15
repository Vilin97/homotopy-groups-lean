/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCharacteristicRelativePiFour
import Submission.ComplexProjectivePlaneProjectiveLineCofiberComparison
import Submission.ComplexProjectivePlaneProjectiveLineCofiberHomology
import Submission.ComplexProjectivePlaneProjectiveLineCofiberTarget
import Submission.Hurewicz.CubicalCollapse
import Submission.Hurewicz.SimplexCubeOrientation
import Submission.Topology.HomotopyEquivMappingCone

/-!
# The projective-line cofiber theorem in relative pi-four

The geometric projective-line collapse, after precomposition with the characteristic four-cell,
is literally the maintained disk-to-sphere quotient.  Since the characteristic pair map is
already a relative `pi_4` isomorphism, cancellation reduces the projective-line collapse to one
concrete map of pairs

`(D⁴, ∂D⁴) → (S⁴, {basepoint})`.

We identify the disk pair with the mapping cone of the identity on its boundary, apply the
generic relative-homology theorem for cofiber collapse, and use relative Hurewicz naturality.
This proves that the projective-line collapse is bijective on relative `pi_4`, that relative
Hurewicz is an isomorphism for `(CP², CP¹)` in degree four, and that this group is infinite
cyclic.
-/

open CategoryTheory Topology MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- The standard disk-to-sphere quotient as a based map from the literal boundary pair to the
point pair of the metric four-sphere. -/
noncomputable def diskBoundaryFourCollapsePairMap :
    BasedPairMap diskBoundaryFourInDisk sphereFourBasepointSet
      diskBoundaryFourInDiskBasepoint sphereFourBasepointInSet where
  toContinuousMap := diskToSphere 4
  mapsTo' := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    change diskToSphere 4 (TopCat.diskBoundaryIncl 4 z) =
      sphereBasepoint 4
    exact diskToSphere_boundary 4 _
      (mem_sphere_zero_iff_norm.mp z.down.property)
  map_basepoint' := by
    change diskToSphere 4
        (TopCat.diskBoundaryIncl 4 diskBoundaryFourBasepoint) =
      sphereBasepoint 4
    exact diskToSphere_boundary 4 _
      (mem_sphere_zero_iff_norm.mp diskBoundaryFourBasepoint.down.property)

/-- The map on relative fourth homotopy induced by the disk-to-sphere quotient. -/
noncomputable def diskBoundaryFourRelativePiFourCollapseHom :
    π_rel 4 (TopCat.disk.{0} 4) diskBoundaryFourInDisk
        diskBoundaryFourInDiskBasepoint →*
      π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet :=
  RelHomotopyGroup.mapHom 2 diskBoundaryFourCollapsePairMap

/-- The projective-line collapse after the characteristic map is exactly the standard
disk-to-sphere quotient, as an equality of based maps of pairs. -/
theorem complexProjectivePlaneProjectiveLineCollapsePairMap_comp_characteristic :
    complexProjectivePlaneProjectiveLineCollapsePairMap.comp
        complexProjectivePlaneCharacteristicPairMap =
      diskBoundaryFourCollapsePairMap := by
  apply BasedPairMap.ext
  apply ContinuousMap.ext
  intro x
  change complexProjectivePlaneProjectiveLineCollapse
      (complexProjectivePlaneCharacteristic x) = diskToSphere 4 x
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm
        (complexProjectivePlaneCharacteristic x)) = diskToSphere 4 x
  rw [← complexProjectivePlaneCellHomeomorph_disk x,
    complexProjectivePlaneCellHomeomorph.symm_apply_apply,
    complexProjectivePlaneCellCollapse_disk_apply]

/-- On relative fourth homotopy, the projective-line collapse composed with the characteristic
map is the disk-to-sphere quotient homomorphism. -/
theorem complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom_comp_characteristic :
    complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom.comp
        (RelHomotopyGroup.mapHom 2
          complexProjectivePlaneCharacteristicPairMap) =
      diskBoundaryFourRelativePiFourCollapseHom := by
  change (RelHomotopyGroup.mapHom 2
      complexProjectivePlaneProjectiveLineCollapsePairMap).comp
        (RelHomotopyGroup.mapHom 2
          complexProjectivePlaneCharacteristicPairMap) =
    RelHomotopyGroup.mapHom 2 diskBoundaryFourCollapsePairMap
  rw [RelHomotopyGroup.mapHom_comp,
    complexProjectivePlaneProjectiveLineCollapsePairMap_comp_characteristic]

/-- Bijectivity of the canonical projective-line collapse on relative `pi_4` is equivalent to
bijectivity of the concrete disk-to-sphere quotient on relative `pi_4`. -/
theorem complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_disk :
    Function.Bijective
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ↔
      Function.Bijective diskBoundaryFourRelativePiFourCollapseHom := by
  let characteristic := RelHomotopyGroup.mapHom 2
    complexProjectivePlaneCharacteristicPairMap
  have hcharacteristic : Function.Bijective characteristic :=
    complexProjectivePlaneCharacteristicPairMap_relative_piFour_bijective
  have hcomp :
      (diskBoundaryFourRelativePiFourCollapseHom :
          π_rel 4 (TopCat.disk.{0} 4) diskBoundaryFourInDisk
              diskBoundaryFourInDiskBasepoint →
            π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet) =
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ∘
          characteristic := by
    funext x
    exact (DFunLike.congr_fun
      complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom_comp_characteristic
      x).symm
  calc
    Function.Bijective
          complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ↔
        Function.Bijective
          (complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ∘
            characteristic) :=
      (Function.Bijective.of_comp_iff
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom
        hcharacteristic).symm
    _ ↔ Function.Bijective diskBoundaryFourRelativePiFourCollapseHom := by
      rw [← hcomp]

/-! ## The remaining disk-quotient comparison through relative Hurewicz -/

/-- The literal boundary of the maintained four-disk is two-connected. -/
theorem isTwoConnected_diskBoundaryFourInDisk :
    IsNConnected 2 diskBoundaryFourInDisk := by
  let e : diskBoundaryFourInDisk ≃ₜ Sph 3 :=
    diskBoundaryInclFour_isEmbedding.toHomeomorph.symm.trans
      diskBoundaryFourHomeomorphSphereThree
  have hsphere : IsNConnected 2 (Sph 3) :=
    isNConnected_sphere_succ_succ 1
  constructor
  · exact ⟨e.symm (sphereBasepoint 3)⟩
  · exact e.symm.surjective.pathConnectedSpace e.symm.continuous
  · intro k hk x
    exact (HomotopyGroup.homeomorphEquiv
      (N := Fin (k + 1)) e x).subsingleton_congr.mpr
        (hsphere.subsingleton_pi k hk (e x))

/-- Relative Hurewicz is bijective in degree four for the literal disk-boundary pair. -/
theorem diskBoundaryFourRelativeHurewiczAdd_bijective :
    Function.Bijective
      (relativeHurewiczAdd 2 diskBoundaryFourInDisk
        diskBoundaryFourInDiskBasepoint) := by
  letI : ContractibleSpace (TopCat.disk.{0} 4) := contractibleSpace_disk 4
  exact IsNConnected.relativeHurewiczAdd_bijective_of_contractibleAmbient
    isTwoConnected_diskBoundaryFourInDisk
    diskBoundaryFourInDiskBasepoint

/-- The disk-to-sphere quotient on relative fourth homotopy, written additively. -/
noncomputable def diskBoundaryFourRelativePiFourCollapseAddHom :
    Additive
        (π_rel 4 (TopCat.disk.{0} 4) diskBoundaryFourInDisk
          diskBoundaryFourInDiskBasepoint) →+
      Additive
        (π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet) :=
  diskBoundaryFourRelativePiFourCollapseHom.toAdditive

/-- The map on fourth relative integral homology induced by the disk-to-sphere quotient. -/
noncomputable def diskBoundaryFourRelativeHomologyFourCollapse :
    HrelSet (Y := TopCat.of (TopCat.disk.{0} 4)) 4 diskBoundaryFourInDisk ⟶
      HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet :=
  diskBoundaryFourCollapsePairMap.hrelMap 4

/-! ### The disk quotient as a collapse of the identity mapping cone -/

/-- Identify the literal range of the boundary inclusion with the abstract boundary sphere. -/
noncomputable def diskBoundaryFourRangeIsoBoundary :
    TopCat.of diskBoundaryFourInDisk ≅ TopCat.diskBoundary.{0} 4 :=
  TopCat.isoOfHomeo diskBoundaryInclFour_isEmbedding.toHomeomorph.symm

@[reassoc]
theorem diskBoundaryFourRangeIsoBoundary_hom_comp_incl :
    diskBoundaryFourRangeIsoBoundary.hom ≫ TopCat.diskBoundaryIncl 4 =
      subIncl (Y := TopCat.of (TopCat.disk.{0} 4)) diskBoundaryFourInDisk := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact congrArg Subtype.val
    (diskBoundaryInclFour_isEmbedding.toHomeomorph.apply_symm_apply z)

/-- Send the four-disk, viewed as the cone on its boundary, into the mapping cone of the
identity of that boundary. -/
noncomputable def diskBoundaryFourToIdentityMappingCone :
    TopCat.disk.{0} 4 ⟶
      topologicalMappingCone (𝟙 (TopCat.diskBoundary.{0} 4)) :=
  diskBoundaryFourConeIsoDisk.inv ≫
    topologicalMappingConeConeIncl (𝟙 (TopCat.diskBoundary.{0} 4))

theorem diskBoundaryFour_subIncl_toIdentityMappingCone :
    subIncl (Y := TopCat.of (TopCat.disk.{0} 4)) diskBoundaryFourInDisk ≫
        diskBoundaryFourToIdentityMappingCone =
      diskBoundaryFourRangeIsoBoundary.hom ≫
        topologicalMappingConeIncl (𝟙 (TopCat.diskBoundary.{0} 4)) := by
  have hcone :
      subIncl (Y := TopCat.of (TopCat.disk.{0} 4)) diskBoundaryFourInDisk ≫
          diskBoundaryFourConeIsoDisk.inv =
        diskBoundaryFourRangeIsoBoundary.hom ≫
          topologicalConeBaseIncl (TopCat.diskBoundary.{0} 4) := by
    apply (cancel_mono diskBoundaryFourConeIsoDisk.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, diskBoundaryFourConeBaseIncl_isoDisk,
      diskBoundaryFourRangeIsoBoundary_hom_comp_incl]
  unfold diskBoundaryFourToIdentityMappingCone
  rw [← Category.assoc, hcone, Category.assoc,
    ← topologicalMappingCone_condition]
  simp

/-- The relative-homology map from the literal disk pair to the identity mapping-cone pair. -/
noncomputable def diskBoundaryFourIdentityMappingConeHrelMap :
    HrelSet (Y := TopCat.of (TopCat.disk.{0} 4)) 4 diskBoundaryFourInDisk ⟶
      Hrel 4
        (topologicalMappingConeIncl (𝟙 (TopCat.diskBoundary.{0} 4))) :=
  HrelMap 4
    (subIncl (Y := TopCat.of (TopCat.disk.{0} 4)) diskBoundaryFourInDisk)
    (topologicalMappingConeIncl (𝟙 (TopCat.diskBoundary.{0} 4)))
    diskBoundaryFour_subIncl_toIdentityMappingCone

/-- The literal disk pair and the identity mapping-cone pair have isomorphic relative
homology. -/
theorem isIso_diskBoundaryFourIdentityMappingConeHrelMap :
    IsIso diskBoundaryFourIdentityMappingConeHrelMap := by
  letI : Nonempty (TopCat.diskBoundary.{0} 4) :=
    ⟨diskBoundaryFourBasepoint⟩
  letI : ContractibleSpace (TopCat.disk.{0} 4) := contractibleSpace_disk 4
  letI : ContractibleSpace
      (topologicalMappingCone (𝟙 (TopCat.diskBoundary.{0} 4))) :=
    contractibleSpace_topologicalMappingCone_of_isIso
      (𝟙 (TopCat.diskBoundary.{0} 4))
  exact isIso_HrelMap_of_isIso_of_contractibleAmbient 4
    (subIncl (Y := TopCat.of (TopCat.disk.{0} 4)) diskBoundaryFourInDisk)
    (topologicalMappingConeIncl (𝟙 (TopCat.diskBoundary.{0} 4)))
    diskBoundaryFour_subIncl_toIdentityMappingCone

/-- Identify the tensor-unit point in the normalized suspension with the literal singleton
subspace of the four-sphere. -/
noncomputable def topCatTensorUnitIsoSphereFourBasepointSet :
    (𝟙_ TopCat.{0} : TopCat.{0}) ≅ TopCat.of sphereFourBasepointSet := by
  letI : Unique sphereFourBasepointSet := {
    default := sphereFourBasepointInSet
    uniq := fun z ↦ Subtype.ext (Set.mem_singleton_iff.mp z.property) }
  exact topCatTensorUnitIsoPUnit ≪≫
    TopCat.isoOfHomeo
      (Homeomorph.homeomorphOfUnique PUnit.{1} sphereFourBasepointSet)

theorem diskBoundaryFourSuspensionPoint_toSphere :
    topologicalMappingConeIncl
          (toUnit (TopCat.diskBoundary.{0} 4)) ≫
        diskBoundaryFourCofiberSuspensionIsoSphereFour.hom =
      topCatTensorUnitIsoSphereFourBasepointSet.hom ≫
        subIncl (Y := TopCat.of (Sph 4)) sphereFourBasepointSet := by
  have hsphere : diskBoundaryFourCofiberSuspensionIsoSphereFour.hom =
      diskBoundaryFourSuspensionToSphere := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact diskBoundaryFourSuspensionHomeomorphSphere_apply x
  rw [hsphere]
  change topologicalSuspensionPointIncl (TopCat.diskBoundary.{0} 4) ≫
      diskBoundaryFourSuspensionToSphere = _
  rw [diskBoundaryFourSuspensionPointIncl_toSphere]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  change sphereBasepoint 4 =
    ((topCatTensorUnitIsoSphereFourBasepointSet.hom u :
      sphereFourBasepointSet) : Sph 4)
  exact (Set.mem_singleton_iff.mp
    (topCatTensorUnitIsoSphereFourBasepointSet.hom u).property).symm

/-- Transport relative homology from the normalized suspension point pair to the maintained
literal point pair of the metric four-sphere. -/
noncomputable def diskBoundaryFourSuspensionSphereHrelMap :
    Hrel 4
        (topologicalMappingConeIncl
          (toUnit (TopCat.diskBoundary.{0} 4))) ⟶
      HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet :=
  HrelMap 4
    (topologicalMappingConeIncl
      (toUnit (TopCat.diskBoundary.{0} 4)))
    (subIncl (Y := TopCat.of (Sph 4)) sphereFourBasepointSet)
    diskBoundaryFourSuspensionPoint_toSphere

theorem isIso_diskBoundaryFourSuspensionSphereHrelMap :
    IsIso diskBoundaryFourSuspensionSphereHrelMap := by
  exact isIso_HrelMap_of_isIso 4
    (topologicalMappingConeIncl
      (toUnit (TopCat.diskBoundary.{0} 4)))
    (subIncl (Y := TopCat.of (Sph 4)) sphereFourBasepointSet)
    diskBoundaryFourSuspensionPoint_toSphere

/-- In the maintained coordinates, the cone inclusion followed by identity-cone collapse and
the suspension-to-sphere homeomorphism is exactly `diskToSphere`. -/
theorem diskBoundaryFour_identityMappingConeCollapse_toSphere :
    diskBoundaryFourToIdentityMappingCone ≫
          topologicalMappingConeCollapseToMappingCone
            (𝟙 (TopCat.diskBoundary.{0} 4)) ≫
        diskBoundaryFourCofiberSuspensionIsoSphereFour.hom =
      TopCat.ofHom (diskToSphere 4) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change diskBoundaryFourSuspensionHomeomorphSphere
      (topologicalMappingConeCollapseToMappingCone
        (𝟙 (TopCat.diskBoundary.{0} 4))
        (topologicalMappingConeConeIncl
          (𝟙 (TopCat.diskBoundary.{0} 4))
          (diskBoundaryFourConeIsoDisk.inv x))) =
    diskToSphere 4 x
  calc
    _ = diskBoundaryFourSuspensionHomeomorphSphere
          (topologicalMappingConeConeIncl
            (toUnit (TopCat.diskBoundary.{0} 4))
            (diskBoundaryFourConeIsoDisk.inv x)) := by
      congr 1
      exact ConcreteCategory.congr_hom
        (topologicalMappingConeConeIncl_collapseToMappingCone
          (𝟙 (TopCat.diskBoundary.{0} 4)))
        (diskBoundaryFourConeIsoDisk.inv x)
    _ = diskBoundaryFourSuspensionToSphere
          (topologicalMappingConeConeIncl
            (toUnit (TopCat.diskBoundary.{0} 4))
            (diskBoundaryFourConeIsoDisk.inv x)) :=
      diskBoundaryFourSuspensionHomeomorphSphere_apply _
    _ = diskToSphere 4
          (diskBoundaryFourConeIsoDisk.hom
            (diskBoundaryFourConeIsoDisk.inv x)) :=
      ConcreteCategory.congr_hom
        diskBoundaryFourSuspensionConeIncl_toSphere
        (diskBoundaryFourConeIsoDisk.inv x)
    _ = diskToSphere 4 x := by simp

/-- The mapping-cone factorization computes the maintained relative-homology map of the disk
quotient. -/
theorem diskBoundaryFourIdentityMappingConeHrelMap_comp_collapse_comp_sphere :
    diskBoundaryFourIdentityMappingConeHrelMap ≫
          mappingConeCollapseHrelMap
            (𝟙 (TopCat.diskBoundary.{0} 4)) 4 ≫
        diskBoundaryFourSuspensionSphereHrelMap =
      diskBoundaryFourRelativeHomologyFourCollapse := by
  unfold diskBoundaryFourIdentityMappingConeHrelMap
    mappingConeCollapseHrelMap diskBoundaryFourSuspensionSphereHrelMap
    diskBoundaryFourRelativeHomologyFourCollapse BasedPairMap.hrelMap
  rw [HrelMap_comp, HrelMap_comp]
  apply HrelMap_eq_of_maps_eq
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    letI : Subsingleton sphereFourBasepointSet :=
      ⟨fun a b ↦ Subtype.ext <|
        (Set.mem_singleton_iff.mp a.property).trans
          (Set.mem_singleton_iff.mp b.property).symm⟩
    exact Subsingleton.elim _ _
  · exact diskBoundaryFour_identityMappingConeCollapse_toSphere

/-- The standard quotient `(D⁴, ∂D⁴) → (S⁴, {basepoint})` is an isomorphism on fourth
relative integral homology. -/
theorem isIso_diskBoundaryFourRelativeHomologyFourCollapse :
    IsIso diskBoundaryFourRelativeHomologyFourCollapse := by
  letI : Nonempty (TopCat.diskBoundary.{0} 4) :=
    ⟨diskBoundaryFourBasepoint⟩
  letI : IsIso diskBoundaryFourIdentityMappingConeHrelMap :=
    isIso_diskBoundaryFourIdentityMappingConeHrelMap
  letI : IsIso
      (mappingConeCollapseHrelMap
        (𝟙 (TopCat.diskBoundary.{0} 4)) 4) :=
    isIso_mappingConeCollapseHrelMap
      (𝟙 (TopCat.diskBoundary.{0} 4)) 4
  letI : IsIso diskBoundaryFourSuspensionSphereHrelMap :=
    isIso_diskBoundaryFourSuspensionSphereHrelMap
  rw [← diskBoundaryFourIdentityMappingConeHrelMap_comp_collapse_comp_sphere]
  infer_instance

/-- Function-level form of the disk-quotient relative-homology isomorphism. -/
theorem diskBoundaryFourRelativeHomologyFourCollapse_bijective :
    Function.Bijective diskBoundaryFourRelativeHomologyFourCollapse := by
  letI : IsIso diskBoundaryFourRelativeHomologyFourCollapse :=
    isIso_diskBoundaryFourRelativeHomologyFourCollapse
  exact ConcreteCategory.bijective_of_isIso
    diskBoundaryFourRelativeHomologyFourCollapse

/-- The degree-four relative Hurewicz square commutes for the disk-to-sphere quotient. -/
theorem diskBoundaryFourCollapse_relativeHurewiczAdd_naturality
    (x : Additive
      (π_rel 4 (TopCat.disk.{0} 4) diskBoundaryFourInDisk
        diskBoundaryFourInDiskBasepoint)) :
    diskBoundaryFourRelativeHomologyFourCollapse
        (relativeHurewiczAdd 2 diskBoundaryFourInDisk
          diskBoundaryFourInDiskBasepoint x) =
      relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
        (diskBoundaryFourRelativePiFourCollapseAddHom x) :=
  relativeHurewicz_naturality 2 diskBoundaryFourCollapsePairMap x.toMul

/-- The concrete disk quotient is bijective on relative `pi_4` exactly when it is bijective on
relative fourth integral homology.  Both relative Hurewicz maps have been discharged. -/
theorem diskBoundaryFourRelativePiFourCollapse_bijective_iff_homology :
    Function.Bijective diskBoundaryFourRelativePiFourCollapseAddHom ↔
      Function.Bijective diskBoundaryFourRelativeHomologyFourCollapse := by
  let f := diskBoundaryFourRelativePiFourCollapseAddHom
  let hsource := relativeHurewiczAdd 2 diskBoundaryFourInDisk
    diskBoundaryFourInDiskBasepoint
  let htarget := relativeHurewiczAdd 2 sphereFourBasepointSet
    sphereFourBasepointInSet
  let hrel := diskBoundaryFourRelativeHomologyFourCollapse
  have hsourceBij : Function.Bijective hsource :=
    diskBoundaryFourRelativeHurewiczAdd_bijective
  have htargetBij : Function.Bijective htarget :=
    sphereFourPointRelativeHurewiczAdd_bijective
  have hcomm : (hrel ∘ hsource) = (htarget ∘ f) := by
    funext x
    exact diskBoundaryFourCollapse_relativeHurewiczAdd_naturality x
  calc
    Function.Bijective f ↔ Function.Bijective (htarget ∘ f) :=
      (Function.Bijective.of_comp_iff' htargetBij f).symm
    _ ↔ Function.Bijective (hrel ∘ hsource) := by rw [hcomm]
    _ ↔ Function.Bijective hrel :=
      Function.Bijective.of_comp_iff hrel hsourceBij

/-- Bijectivity of the canonical projective-line collapse is equivalent to the relative-homology
isomorphism for the standard disk-to-sphere quotient. -/
theorem
    complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_diskHomology :
    Function.Bijective
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ↔
      Function.Bijective diskBoundaryFourRelativeHomologyFourCollapse := by
  have htag :
      Function.Bijective diskBoundaryFourRelativePiFourCollapseHom ↔
        Function.Bijective diskBoundaryFourRelativePiFourCollapseAddHom := by
    change Function.Bijective diskBoundaryFourRelativePiFourCollapseHom ↔
      Function.Bijective
        (Additive.ofMul ∘ diskBoundaryFourRelativePiFourCollapseHom ∘
          Additive.toMul)
    exact ((Function.Bijective.of_comp_iff' Additive.ofMul.bijective _).trans
      (Function.Bijective.of_comp_iff _ Additive.toMul.bijective)).symm
  exact
    complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_disk.trans
      (htag.trans
        diskBoundaryFourRelativePiFourCollapse_bijective_iff_homology)

/-- The disk-to-sphere quotient is bijective on relative fourth homotopy, in additive form. -/
theorem diskBoundaryFourRelativePiFourCollapseAddHom_bijective :
    Function.Bijective diskBoundaryFourRelativePiFourCollapseAddHom :=
  diskBoundaryFourRelativePiFourCollapse_bijective_iff_homology.mpr
    diskBoundaryFourRelativeHomologyFourCollapse_bijective

/-- The disk-to-sphere quotient is bijective on relative fourth homotopy. -/
theorem diskBoundaryFourRelativePiFourCollapseHom_bijective :
    Function.Bijective diskBoundaryFourRelativePiFourCollapseHom := by
  have htag :
      Function.Bijective diskBoundaryFourRelativePiFourCollapseHom ↔
        Function.Bijective diskBoundaryFourRelativePiFourCollapseAddHom := by
    change Function.Bijective diskBoundaryFourRelativePiFourCollapseHom ↔
      Function.Bijective
        (Additive.ofMul ∘ diskBoundaryFourRelativePiFourCollapseHom ∘
          Additive.toMul)
    exact ((Function.Bijective.of_comp_iff' Additive.ofMul.bijective _).trans
      (Function.Bijective.of_comp_iff _ Additive.toMul.bijective)).symm
  exact htag.mpr diskBoundaryFourRelativePiFourCollapseAddHom_bijective

/-- **Projective-line cofiber theorem in relative `pi_4`.** Collapsing `CP¹` in `CP²`
induces a bijection from the relative fourth homotopy group to that of the point pair in
`S⁴`. -/
theorem complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective :
    Function.Bijective
      complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom :=
  complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_diskHomology.mpr
    diskBoundaryFourRelativeHomologyFourCollapse_bijective

/-- Additive form of the projective-line relative `pi_4` collapse bijection. -/
theorem complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom_bijective :
    Function.Bijective
      complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom := by
  have htag :
      Function.Bijective
          complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ↔
        Function.Bijective
          complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom := by
    change Function.Bijective
        complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ↔
      Function.Bijective
        (Additive.ofMul ∘
          complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom ∘
            Additive.toMul)
    exact ((Function.Bijective.of_comp_iff' Additive.ofMul.bijective _).trans
      (Function.Bijective.of_comp_iff _ Additive.toMul.bijective)).symm
  exact htag.mp
    complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective

/-- Relative Hurewicz is bijective in degree four for the literal pair `(CP², CP¹)`. -/
theorem complexProjectivePlaneProjectiveLineRelativeHurewiczAdd_bijective :
    Function.Bijective
      (relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint) := by
  let hsource :
      Additive
          (π_rel 4 (ComplexProjectiveModel 2)
            complexProjectivePlaneProjectiveLine
            complexProjectivePlaneProjectiveLineBasepoint) →
        (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneProjectiveLine : Type) :=
    relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
      complexProjectivePlaneProjectiveLineBasepoint
  let hrel :
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
          complexProjectivePlaneProjectiveLine : Type) →
        (HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet : Type) :=
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
  have hcompRaw :=
    complexProjectivePlaneProjectiveLineRelativePiFourCollapse_bijective_iff_hurewicz.mp
      complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom_bijective
  have hcomp : Function.Bijective
      (fun x : Additive
          (π_rel 4 (ComplexProjectiveModel 2)
            complexProjectivePlaneProjectiveLine
            complexProjectivePlaneProjectiveLineBasepoint) ↦
        hrel (hsource x)) := by
    simpa only [hrel, hsource] using hcompRaw
  have hrelBij : Function.Bijective hrel :=
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse_bijective
  exact (Function.Bijective.of_comp_iff' hrelBij hsource).mp hcomp

/-- Relative Hurewicz as an additive equivalence for `(CP², CP¹)` in degree four. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativeHurewiczAddEquiv :
    Additive
        (π_rel 4 (ComplexProjectiveModel 2)
          complexProjectivePlaneProjectiveLine
          complexProjectivePlaneProjectiveLineBasepoint) ≃+
      (HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
        complexProjectivePlaneProjectiveLine : Type) :=
  AddEquiv.ofBijective
    (relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
      complexProjectivePlaneProjectiveLineBasepoint)
    complexProjectivePlaneProjectiveLineRelativeHurewiczAdd_bijective

/-- The relative fourth homotopy group of `(CP², CP¹)` is infinite cyclic. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativePiFourAddEquivInt :
    Additive
        (π_rel 4 (ComplexProjectiveModel 2)
          complexProjectivePlaneProjectiveLine
          complexProjectivePlaneProjectiveLineBasepoint) ≃+ ℤ :=
  complexProjectivePlaneProjectiveLineRelativeHurewiczAddEquiv.trans
    complexProjectivePlaneProjectiveLineRelativeHomologyFourIsoInt.addCommGroupIsoToAddEquiv

end Submission
