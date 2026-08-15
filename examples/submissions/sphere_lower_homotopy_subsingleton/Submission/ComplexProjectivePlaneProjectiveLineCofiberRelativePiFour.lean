/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneCharacteristicRelativePiFour
import Submission.ComplexProjectivePlaneProjectiveLineCofiberComparison
import Submission.ComplexProjectivePlaneProjectiveLineCofiberTarget
import Submission.Hurewicz.CubicalCollapse
import Submission.Hurewicz.SimplexCubeOrientation

/-!
# Reducing the projective-line relative pi-four collapse to the disk quotient

The geometric projective-line collapse, after precomposition with the characteristic four-cell,
is literally the maintained disk-to-sphere quotient.  Since the characteristic pair map is
already a relative `pi_4` isomorphism, cancellation reduces the remaining projective-line
collapse question to one concrete map of pairs

`(D⁴, ∂D⁴) → (S⁴, {basepoint})`.
-/

open CategoryTheory Topology
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

/-- The remaining canonical projective-line collapse question is exactly the relative-homology
excision statement for the standard disk-to-sphere quotient. -/
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

end Submission
