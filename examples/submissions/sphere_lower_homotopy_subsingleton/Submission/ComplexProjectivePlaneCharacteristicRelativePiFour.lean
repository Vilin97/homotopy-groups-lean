/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.DiskPair
import Submission.ComplexProjectivePlaneProjectiveLineRelativePiFour
import Submission.HopfFibration

/-!
# The characteristic four-cell generates relative pi four of the projective pair

The characteristic map of the top four-cell defines a map of literal pairs

`(D⁴, ∂D⁴) → (CP², CP¹)`.

Its map on relative fourth homotopy groups is bijective.  Naturality of the boundary map reduces
this to the contractibility of the disk, the vanishing of the adjacent homotopy groups of `CP²`,
and the fact that the attaching map is the Hopf map in the maintained sphere coordinates.
-/

open CategoryTheory Topology
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- The boundary basepoint corresponding to the maintained basepoint of the metric
three-sphere. -/
noncomputable def diskBoundaryFourBasepoint : TopCat.diskBoundary.{0} 4 :=
  diskBoundaryFourHomeomorphSphereThree.symm (sphereBasepoint 3)

@[simp]
theorem diskBoundaryFourHomeomorphSphereThree_basepoint :
    diskBoundaryFourHomeomorphSphereThree diskBoundaryFourBasepoint =
      sphereBasepoint 3 :=
  diskBoundaryFourHomeomorphSphereThree.apply_symm_apply _

/-- The exact projective attaching map preserves the maintained basepoints. -/
@[simp]
theorem diskBoundaryFourComplexHopfMap_basepoint :
    diskBoundaryFourComplexHopfMap diskBoundaryFourBasepoint =
      complexProjectiveModelBasepoint 1 := by
  apply complexProjectiveLineHomeomorphSphere.injective
  calc
    complexProjectiveLineHomeomorphSphere
          (diskBoundaryFourComplexHopfMap diskBoundaryFourBasepoint) =
        hopfMap
          (diskBoundaryFourHomeomorphSphereThree diskBoundaryFourBasepoint) :=
      ConcreteCategory.congr_hom
        diskBoundaryFourComplexHopfMap_is_hopfMap diskBoundaryFourBasepoint
    _ = sphereBasepoint 2 := by
      rw [diskBoundaryFourHomeomorphSphereThree_basepoint,
        hopfMap_basepoint]
    _ = complexProjectiveLineHomeomorphSphere
          (complexProjectiveModelBasepoint 1) :=
      complexProjectiveLineHomeomorphSphere_basepoint.symm

/-- The boundary inclusion of the four-disk is a topological embedding. -/
theorem diskBoundaryInclFour_isEmbedding :
    IsEmbedding (TopCat.diskBoundaryIncl.{0} 4).hom :=
  ((TopCat.diskBoundaryIncl.{0} 4).hom.continuous.isClosedEmbedding
    ((TopCat.mono_iff_injective _).mp inferInstance)).isEmbedding

/-- The literal boundary subspace of the maintained four-disk. -/
def diskBoundaryFourInDisk : Set (TopCat.disk.{0} 4) :=
  Set.range (TopCat.diskBoundaryIncl.{0} 4).hom

/-- The maintained boundary point regarded as a point of the literal boundary subspace. -/
noncomputable def diskBoundaryFourInDiskBasepoint : diskBoundaryFourInDisk :=
  diskBoundaryInclFour_isEmbedding.toHomeomorph diskBoundaryFourBasepoint

@[simp]
theorem diskBoundaryFourInDiskBasepoint_coe :
    (diskBoundaryFourInDiskBasepoint : TopCat.disk.{0} 4) =
      TopCat.diskBoundaryIncl 4 diskBoundaryFourBasepoint :=
  rfl

/-- The characteristic four-cell as a based map from the literal disk pair to the literal
projective-line pair. -/
noncomputable def complexProjectivePlaneCharacteristicPairMap :
    BasedPairMap diskBoundaryFourInDisk complexProjectivePlaneProjectiveLine
      diskBoundaryFourInDiskBasepoint
      complexProjectivePlaneProjectiveLineBasepoint where
  toContinuousMap := complexProjectivePlaneCharacteristic.hom
  mapsTo' := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    exact ⟨diskBoundaryFourComplexHopfMap z,
      (ConcreteCategory.congr_hom
        complexProjectivePlaneCharacteristic_boundary z)⟩
  map_basepoint' := by
    change complexProjectivePlaneCharacteristic
        (TopCat.diskBoundaryIncl 4 diskBoundaryFourBasepoint) =
      (complexProjectivePlaneProjectiveLineBasepoint :
        ComplexProjectiveModel 2)
    calc
      complexProjectivePlaneCharacteristic
            (TopCat.diskBoundaryIncl 4 diskBoundaryFourBasepoint) =
          complexProjectivePlaneBottomIncl
            (diskBoundaryFourComplexHopfMap diskBoundaryFourBasepoint) :=
        (ConcreteCategory.congr_hom
          complexProjectivePlaneCharacteristic_boundary
          diskBoundaryFourBasepoint).symm
      _ = complexProjectivePlaneBottomIncl
            (complexProjectiveModelBasepoint 1) := by
        rw [diskBoundaryFourComplexHopfMap_basepoint]
      _ = complexProjectiveModelBasepoint 2 :=
        complexProjectivePlaneBottomIncl_basepoint
      _ = (complexProjectivePlaneProjectiveLineBasepoint :
          ComplexProjectiveModel 2) :=
        complexProjectivePlaneProjectiveLineBasepoint_coe.symm

/-- The exact projective attaching map induces a bijection on third homotopy groups. -/
theorem diskBoundaryFourComplexHopfMap_piThree_bijective :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 3)
        diskBoundaryFourComplexHopfMap.hom
        diskBoundaryFourComplexHopfMap_basepoint) := by
  apply HomotopyGroup.map_bijective_of_homeomorph_square
      diskBoundaryFourComplexHopfMap.hom hopfMap
      diskBoundaryFourHomeomorphSphereThree
      complexProjectiveLineHomeomorphSphere
      (by
        apply ContinuousMap.ext
        intro z
        exact ConcreteCategory.congr_hom
          diskBoundaryFourComplexHopfMap_is_hopfMap z)
      diskBoundaryFourComplexHopfMap_basepoint
      diskBoundaryFourHomeomorphSphereThree_basepoint
      hopfMap_basepoint
  change Function.Bijective hopfPiThreeHom
  exact hopfPiThreeHom_bijective hopfMap_isSerreFibration

/-- On the literal boundary subspaces, the characteristic pair map induces a bijection on
third homotopy groups. -/
theorem complexProjectivePlaneCharacteristicPairMap_subspace_piThree_bijective :
    Function.Bijective
      (HomotopyGroup.mapHom
        complexProjectivePlaneCharacteristicPairMap.subspaceMap
        complexProjectivePlaneCharacteristicPairMap.subspaceMap_basepoint :
        π_ 3 diskBoundaryFourInDisk diskBoundaryFourInDiskBasepoint →*
          π_ 3 complexProjectivePlaneProjectiveLine
            complexProjectivePlaneProjectiveLineBasepoint) := by
  apply (HomotopyGroup.map_bijective_iff_of_homeomorph_square
      diskBoundaryFourComplexHopfMap.hom
      complexProjectivePlaneCharacteristicPairMap.subspaceMap
      diskBoundaryInclFour_isEmbedding.toHomeomorph
      complexProjectivePlaneProjectiveLineHomeomorph
      (by
        apply ContinuousMap.ext
        intro z
        apply Subtype.ext
        exact ConcreteCategory.congr_hom
          complexProjectivePlaneCharacteristic_boundary z)
      diskBoundaryFourComplexHopfMap_basepoint
      rfl
      complexProjectivePlaneCharacteristicPairMap.subspaceMap_basepoint).mp
  exact diskBoundaryFourComplexHopfMap_piThree_bijective

/-- The relative-fourth-group boundary of the literal disk pair is bijective. -/
theorem diskBoundaryFourInDisk_relative_piFour_boundary_bijective :
    Function.Bijective
      (RelHomotopyGroup.bdHom 2 (TopCat.disk.{0} 4)
        diskBoundaryFourInDisk diskBoundaryFourInDiskBasepoint) := by
  letI : ContractibleSpace (TopCat.disk.{0} 4) := contractibleSpace_disk 4
  exact bijective_bd_of_subsingleton 2 diskBoundaryFourInDiskBasepoint
    (subsingleton_homotopyGroup_of_contractible _)
    (subsingleton_homotopyGroup_of_contractible _)

/-- The characteristic four-cell generates the relative fourth homotopy group of the literal
projective pair: its induced map `π₄(D⁴, ∂D⁴) → π₄(CP², CP¹)` is bijective. -/
theorem complexProjectivePlaneCharacteristicPairMap_relative_piFour_bijective :
    Function.Bijective
      (RelHomotopyGroup.mapHom 2 complexProjectivePlaneCharacteristicPairMap) := by
  exact RelHomotopyGroup.mapHom_bijective_of_bdHom_bijective 2
    complexProjectivePlaneCharacteristicPairMap
    diskBoundaryFourInDisk_relative_piFour_boundary_bijective
    (complexProjectivePlaneProjectiveLine_relative_piFour_boundary_bijective
      complexProjectivePlaneProjectiveLineBasepoint)
    complexProjectivePlaneCharacteristicPairMap_subspace_piThree_bijective

end Submission
