/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridians
import Submission.FiniteOrderedComplexConeRealization
import Submission.ForMathlib.HomotopyGroup.Contractible
import Submission.Topology.DiskBoundaryCone

/-!
# Topological meridian disks in the projective-plane trisection

Each integral three-triangle filling from the finite meridian certificate is literally a
simplicial cone on its triangular boundary.  The general finite-cone realization comparison
therefore identifies its realization with the exact closed two-disk and its boundary with the
exact metric circle.  The boundary inclusion into the corresponding pairwise interface factors
through this contractible disk.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The three finite cone pairs -/

def zeroFiveMeridianBoundaryFacets : Finset (Finset TrisectionVertex) :=
  {{1, 7}, {7, 12}, {12, 1}}

def zeroFiveMeridianDiskFacets : Finset (Finset TrisectionVertex) :=
  zeroFiveMeridianBoundaryFacets.image (fun edge ↦ insert 9 edge)

def fiveFourMeridianBoundaryFacets : Finset (Finset TrisectionVertex) :=
  {{7, 3}, {3, 12}, {12, 7}}

def fiveFourMeridianDiskFacets : Finset (Finset TrisectionVertex) :=
  fiveFourMeridianBoundaryFacets.image (fun edge ↦ insert 11 edge)

def fourZeroMeridianBoundaryFacets : Finset (Finset TrisectionVertex) :=
  {{3, 1}, {1, 12}, {12, 3}}

def fourZeroMeridianDiskFacets : Finset (Finset TrisectionVertex) :=
  fourZeroMeridianBoundaryFacets.image (fun edge ↦ insert 10 edge)

theorem zeroFiveMeridianDiskFacets_eq_orientedTriangleFacets :
    zeroFiveMeridianDiskFacets = orientedTriangleFacets zeroFiveMeridianDisk := by decide

theorem fiveFourMeridianDiskFacets_eq_orientedTriangleFacets :
    fiveFourMeridianDiskFacets = orientedTriangleFacets fiveFourMeridianDisk := by decide

theorem fourZeroMeridianDiskFacets_eq_orientedTriangleFacets :
    fourZeroMeridianDiskFacets = orientedTriangleFacets fourZeroMeridianDisk := by decide

theorem zeroFiveMeridianDiskFacets_le_pairwiseInterface :
    FacetFamilyLE zeroFiveMeridianDiskFacets (pairwiseInterfaceFacets 0 5) := by
  unfold FacetFamilyLE IsFace
  decide

theorem fiveFourMeridianDiskFacets_le_pairwiseInterface :
    FacetFamilyLE fiveFourMeridianDiskFacets (pairwiseInterfaceFacets 5 4) := by
  unfold FacetFamilyLE IsFace
  decide

theorem fourZeroMeridianDiskFacets_le_pairwiseInterface :
    FacetFamilyLE fourZeroMeridianDiskFacets (pairwiseInterfaceFacets 4 0) := by
  unfold FacetFamilyLE IsFace
  decide

theorem zeroFiveMeridianBoundaryFacets_le_centralInterface :
    FacetFamilyLE zeroFiveMeridianBoundaryFacets centralInterfaceFacets := by
  unfold FacetFamilyLE IsFace
  decide

theorem fiveFourMeridianBoundaryFacets_le_centralInterface :
    FacetFamilyLE fiveFourMeridianBoundaryFacets centralInterfaceFacets := by
  unfold FacetFamilyLE IsFace
  decide

theorem fourZeroMeridianBoundaryFacets_le_centralInterface :
    FacetFamilyLE fourZeroMeridianBoundaryFacets centralInterfaceFacets := by
  unfold FacetFamilyLE IsFace
  decide

/-! ## Exact circle boundaries -/

def zeroFiveMeridianVertices : Finset TrisectionVertex := {1, 7, 12}

def fiveFourMeridianVertices : Finset TrisectionVertex := {7, 3, 12}

def fourZeroMeridianVertices : Finset TrisectionVertex := {3, 1, 12}

theorem zeroFiveMeridianBoundaryFacets_eq_simplexBoundary :
    zeroFiveMeridianBoundaryFacets = simplexBoundaryFacets zeroFiveMeridianVertices := by decide

theorem fiveFourMeridianBoundaryFacets_eq_simplexBoundary :
    fiveFourMeridianBoundaryFacets = simplexBoundaryFacets fiveFourMeridianVertices := by decide

theorem fourZeroMeridianBoundaryFacets_eq_simplexBoundary :
    fourZeroMeridianBoundaryFacets = simplexBoundaryFacets fourZeroMeridianVertices := by decide

theorem zeroFiveMeridianVertices_card : zeroFiveMeridianVertices.card = 2 + 1 := by decide

theorem fiveFourMeridianVertices_card : fiveFourMeridianVertices.card = 2 + 1 := by decide

theorem fourZeroMeridianVertices_card : fourZeroMeridianVertices.card = 2 + 1 := by decide

noncomputable def zeroFiveMeridianBoundarySSetIsoBoundaryTwo :
    orderedSSet zeroFiveMeridianBoundaryFacets ≅ (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex zeroFiveMeridianBoundaryFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 zeroFiveMeridianVertices zeroFiveMeridianVertices_card

noncomputable def fiveFourMeridianBoundarySSetIsoBoundaryTwo :
    orderedSSet fiveFourMeridianBoundaryFacets ≅ (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex fiveFourMeridianBoundaryFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 fiveFourMeridianVertices fiveFourMeridianVertices_card

noncomputable def fourZeroMeridianBoundarySSetIsoBoundaryTwo :
    orderedSSet fourZeroMeridianBoundaryFacets ≅ (SSet.boundary 2 : SSet) :=
  SSet.Subcomplex.eqToIso
      (congrArg orderedSubcomplex fourZeroMeridianBoundaryFacets_eq_simplexBoundary) ≪≫
    simplexBoundarySSetIso 2 fourZeroMeridianVertices fourZeroMeridianVertices_card

noncomputable def zeroFiveMeridianBoundaryRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets) ≃ₜ SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso zeroFiveMeridianBoundarySSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

noncomputable def fiveFourMeridianBoundaryRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets) ≃ₜ SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso fiveFourMeridianBoundarySSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

noncomputable def fourZeroMeridianBoundaryRealizationHomeomorphSphereOne :
    SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets) ≃ₜ SphereSpace 1 :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso fourZeroMeridianBoundarySSetIsoBoundaryTwo)).trans
    (boundaryRealizationHomeomorphSphere 1)

noncomputable def zeroFiveMeridianBoundaryRealizationHomeomorphDiskBoundary :
    SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets) ≃ₜ
      TopCat.diskBoundary.{0} 2 :=
  zeroFiveMeridianBoundaryRealizationHomeomorphSphereOne.trans
    (diskBoundaryHomeoSph 1).symm

noncomputable def fiveFourMeridianBoundaryRealizationHomeomorphDiskBoundary :
    SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets) ≃ₜ
      TopCat.diskBoundary.{0} 2 :=
  fiveFourMeridianBoundaryRealizationHomeomorphSphereOne.trans
    (diskBoundaryHomeoSph 1).symm

noncomputable def fourZeroMeridianBoundaryRealizationHomeomorphDiskBoundary :
    SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets) ≃ₜ
      TopCat.diskBoundary.{0} 2 :=
  fourZeroMeridianBoundaryRealizationHomeomorphSphereOne.trans
    (diskBoundaryHomeoSph 1).symm

/-! ## Exact disk fillings -/

theorem zeroFiveMeridianBoundary_apex_not_mem :
    ∀ edge ∈ zeroFiveMeridianBoundaryFacets, 9 ∉ edge := by decide

theorem fiveFourMeridianBoundary_apex_not_mem :
    ∀ edge ∈ fiveFourMeridianBoundaryFacets, 11 ∉ edge := by decide

theorem fourZeroMeridianBoundary_apex_not_mem :
    ∀ edge ∈ fourZeroMeridianBoundaryFacets, 10 ∉ edge := by decide

theorem zeroFiveMeridianBoundary_nonempty :
    ∃ edge ∈ zeroFiveMeridianBoundaryFacets, edge.Nonempty := by decide

theorem fiveFourMeridianBoundary_nonempty :
    ∃ edge ∈ fiveFourMeridianBoundaryFacets, edge.Nonempty := by decide

theorem fourZeroMeridianBoundary_nonempty :
    ∃ edge ∈ fourZeroMeridianBoundaryFacets, edge.Nonempty := by decide

noncomputable def meridianDiskRealizationHomeomorphDisk
    (boundaryFacets : Finset (Finset TrisectionVertex)) (apex : TrisectionVertex)
    (hapex : ∀ edge ∈ boundaryFacets, apex ∉ edge)
    (hnonempty : ∃ edge ∈ boundaryFacets, edge.Nonempty)
    (boundaryHomeomorph :
      SSet.toTop.obj (orderedSSet boundaryFacets) ≃ₜ TopCat.diskBoundary.{0} 2) :
    SSet.toTop.obj
        (orderedSSet (boundaryFacets.image (fun edge ↦ insert apex edge))) ≃ₜ
      TopCat.disk.{0} 2 :=
  (conedOrderedRealizationHomeomorphTopologicalCone
      boundaryFacets apex hapex hnonempty).trans
    ((TopCat.homeoOfIso
      (topologicalConeIso (TopCat.isoOfHomeo boundaryHomeomorph))).trans
        (diskBoundarySuccConeHomeomorphDisk (n := 1)))

noncomputable def zeroFiveMeridianDiskRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets) ≃ₜ TopCat.disk.{0} 2 :=
  meridianDiskRealizationHomeomorphDisk zeroFiveMeridianBoundaryFacets 9
    zeroFiveMeridianBoundary_apex_not_mem zeroFiveMeridianBoundary_nonempty
    zeroFiveMeridianBoundaryRealizationHomeomorphDiskBoundary

noncomputable def fiveFourMeridianDiskRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets) ≃ₜ TopCat.disk.{0} 2 :=
  meridianDiskRealizationHomeomorphDisk fiveFourMeridianBoundaryFacets 11
    fiveFourMeridianBoundary_apex_not_mem fiveFourMeridianBoundary_nonempty
    fiveFourMeridianBoundaryRealizationHomeomorphDiskBoundary

noncomputable def fourZeroMeridianDiskRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets) ≃ₜ TopCat.disk.{0} 2 :=
  meridianDiskRealizationHomeomorphDisk fourZeroMeridianBoundaryFacets 10
    fourZeroMeridianBoundary_apex_not_mem fourZeroMeridianBoundary_nonempty
    fourZeroMeridianBoundaryRealizationHomeomorphDiskBoundary

/-! ## Factorization of the pairwise-interface inclusions -/

def zeroFiveMeridianDiskIncl :
    orderedSSet zeroFiveMeridianDiskFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 0 5) :=
  orderedSSetHomOfFacetFamilyLE zeroFiveMeridianDiskFacets_le_pairwiseInterface

def fiveFourMeridianDiskIncl :
    orderedSSet fiveFourMeridianDiskFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 5 4) :=
  orderedSSetHomOfFacetFamilyLE fiveFourMeridianDiskFacets_le_pairwiseInterface

def fourZeroMeridianDiskIncl :
    orderedSSet fourZeroMeridianDiskFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 4 0) :=
  orderedSSetHomOfFacetFamilyLE fourZeroMeridianDiskFacets_le_pairwiseInterface

def zeroFiveMeridianBoundaryInclPairwise :
    orderedSSet zeroFiveMeridianBoundaryFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 0 5) :=
  orderedSSetHomOfFacetFamilyLE
    (by
      unfold FacetFamilyLE IsFace
      decide)

def fiveFourMeridianBoundaryInclPairwise :
    orderedSSet fiveFourMeridianBoundaryFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 5 4) :=
  orderedSSetHomOfFacetFamilyLE
    (by
      unfold FacetFamilyLE IsFace
      decide)

def fourZeroMeridianBoundaryInclPairwise :
    orderedSSet fourZeroMeridianBoundaryFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 4 0) :=
  orderedSSetHomOfFacetFamilyLE
    (by
      unfold FacetFamilyLE IsFace
      decide)

theorem zeroFiveMeridianBoundaryInclPairwise_factor :
    orderedConeBaseIncl zeroFiveMeridianBoundaryFacets 9 ≫
        zeroFiveMeridianDiskIncl =
      zeroFiveMeridianBoundaryInclPairwise := by
  rfl

theorem fiveFourMeridianBoundaryInclPairwise_factor :
    orderedConeBaseIncl fiveFourMeridianBoundaryFacets 11 ≫
        fiveFourMeridianDiskIncl =
      fiveFourMeridianBoundaryInclPairwise := by
  rfl

theorem fourZeroMeridianBoundaryInclPairwise_factor :
    orderedConeBaseIncl fourZeroMeridianBoundaryFacets 10 ≫
        fourZeroMeridianDiskIncl =
      fourZeroMeridianBoundaryInclPairwise := by
  rfl

/-! ## Central-interface factorizations -/

/-- Every boundary triangle of a finite tetrahedral facet family is a face of that family. -/
theorem tetrahedralBoundaryTriangles_le
    (tetrahedra : Finset (Finset TrisectionVertex)) :
    FacetFamilyLE (tetrahedralBoundaryTriangles tetrahedra) tetrahedra := by
  intro triangle htriangle
  exact isFace_of_mem_facesOfCard (Finset.mem_filter.mp htriangle).1

/-- The common central interface is a subcomplex of every pairwise interface. -/
theorem centralInterfaceFacets_le_pairwiseInterface
    (a : TrisectionVertex) (ha : a ∈ trisectionApexes)
    (b : TrisectionVertex) (hb : b ∈ trisectionApexes) (hab : a ≠ b) :
    FacetFamilyLE centralInterfaceFacets (pairwiseInterfaceFacets a b) := by
  rw [← pairwiseInterface_boundary_eq_central a ha b hb hab]
  exact tetrahedralBoundaryTriangles_le _

def zeroFiveCentralInterfaceInclPairwise :
    orderedSSet centralInterfaceFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 0 5) :=
  orderedSSetHomOfFacetFamilyLE
    (centralInterfaceFacets_le_pairwiseInterface 0 (by decide) 5 (by decide) (by decide))

def fiveFourCentralInterfaceInclPairwise :
    orderedSSet centralInterfaceFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 5 4) :=
  orderedSSetHomOfFacetFamilyLE
    (centralInterfaceFacets_le_pairwiseInterface 5 (by decide) 4 (by decide) (by decide))

def fourZeroCentralInterfaceInclPairwise :
    orderedSSet centralInterfaceFacets ⟶
      orderedSSet (pairwiseInterfaceFacets 4 0) :=
  orderedSSetHomOfFacetFamilyLE
    (centralInterfaceFacets_le_pairwiseInterface 4 (by decide) 0 (by decide) (by decide))

def zeroFiveMeridianBoundaryInclCentral :
    orderedSSet zeroFiveMeridianBoundaryFacets ⟶
      orderedSSet centralInterfaceFacets :=
  orderedSSetHomOfFacetFamilyLE zeroFiveMeridianBoundaryFacets_le_centralInterface

def fiveFourMeridianBoundaryInclCentral :
    orderedSSet fiveFourMeridianBoundaryFacets ⟶
      orderedSSet centralInterfaceFacets :=
  orderedSSetHomOfFacetFamilyLE fiveFourMeridianBoundaryFacets_le_centralInterface

def fourZeroMeridianBoundaryInclCentral :
    orderedSSet fourZeroMeridianBoundaryFacets ⟶
      orderedSSet centralInterfaceFacets :=
  orderedSSetHomOfFacetFamilyLE fourZeroMeridianBoundaryFacets_le_centralInterface

theorem zeroFiveMeridianBoundaryInclPairwise_factor_central :
    zeroFiveMeridianBoundaryInclCentral ≫
        zeroFiveCentralInterfaceInclPairwise =
      zeroFiveMeridianBoundaryInclPairwise := by
  rfl

theorem fiveFourMeridianBoundaryInclPairwise_factor_central :
    fiveFourMeridianBoundaryInclCentral ≫
        fiveFourCentralInterfaceInclPairwise =
      fiveFourMeridianBoundaryInclPairwise := by
  rfl

theorem fourZeroMeridianBoundaryInclPairwise_factor_central :
    fourZeroMeridianBoundaryInclCentral ≫
        fourZeroCentralInterfaceInclPairwise =
      fourZeroMeridianBoundaryInclPairwise := by
  rfl

/-! ## Nullhomotopies of the three meridian inclusions -/

/-- The realized zero-five meridian circle is nullhomotopic in its pairwise interface. -/
theorem zeroFiveMeridianBoundaryInclPairwise_nullhomotopic :
    (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom.Nullhomotopic := by
  let f : C(SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl zeroFiveMeridianBoundaryFacets 9)).hom
  let g : C(SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5))) :=
    (SSet.toTop.map zeroFiveMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← zeroFiveMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets)) :=
    zeroFiveMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  exact ((id_nullhomotopic
    (SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets))).comp_left f).comp_right g

/-- The realized five-four meridian circle is nullhomotopic in its pairwise interface. -/
theorem fiveFourMeridianBoundaryInclPairwise_nullhomotopic :
    (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom.Nullhomotopic := by
  let f : C(SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl fiveFourMeridianBoundaryFacets 11)).hom
  let g : C(SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4))) :=
    (SSet.toTop.map fiveFourMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← fiveFourMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets)) :=
    fiveFourMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  exact ((id_nullhomotopic
    (SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets))).comp_left f).comp_right g

/-- The realized four-zero meridian circle is nullhomotopic in its pairwise interface. -/
theorem fourZeroMeridianBoundaryInclPairwise_nullhomotopic :
    (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom.Nullhomotopic := by
  let f : C(SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl fourZeroMeridianBoundaryFacets 10)).hom
  let g : C(SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0))) :=
    (SSet.toTop.map fourZeroMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← fourZeroMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets)) :=
    fourZeroMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  exact ((id_nullhomotopic
    (SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets))).comp_left f).comp_right g

/-- The zero-five meridian's route through the central interface is nullhomotopic in the
zero-five pairwise interface. -/
theorem zeroFiveMeridianViaCentralInclPairwise_nullhomotopic :
    (SSet.toTop.map
      (zeroFiveMeridianBoundaryInclCentral ≫
        zeroFiveCentralInterfaceInclPairwise)).hom.Nullhomotopic := by
  rw [zeroFiveMeridianBoundaryInclPairwise_factor_central]
  exact zeroFiveMeridianBoundaryInclPairwise_nullhomotopic

/-- The five-four meridian's route through the central interface is nullhomotopic in the
five-four pairwise interface. -/
theorem fiveFourMeridianViaCentralInclPairwise_nullhomotopic :
    (SSet.toTop.map
      (fiveFourMeridianBoundaryInclCentral ≫
        fiveFourCentralInterfaceInclPairwise)).hom.Nullhomotopic := by
  rw [fiveFourMeridianBoundaryInclPairwise_factor_central]
  exact fiveFourMeridianBoundaryInclPairwise_nullhomotopic

/-- The four-zero meridian's route through the central interface is nullhomotopic in the
four-zero pairwise interface. -/
theorem fourZeroMeridianViaCentralInclPairwise_nullhomotopic :
    (SSet.toTop.map
      (fourZeroMeridianBoundaryInclCentral ≫
        fourZeroCentralInterfaceInclPairwise)).hom.Nullhomotopic := by
  rw [fourZeroMeridianBoundaryInclPairwise_factor_central]
  exact fourZeroMeridianBoundaryInclPairwise_nullhomotopic

/-! ## The induced fundamental-group maps are trivial -/

/-- The realized zero-five meridian circle maps trivially on fundamental groups into its
pairwise interface, at every basepoint. -/
theorem zeroFiveMeridianBoundaryInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom rfl q = 1 := by
  let f : C(SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl zeroFiveMeridianBoundaryFacets 9)).hom
  let g : C(SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5))) :=
    (SSet.toTop.map zeroFiveMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← zeroFiveMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets)) :=
    zeroFiveMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet zeroFiveMeridianDiskFacets)) (f x)) :=
    subsingleton_homotopyGroup_of_contractible (f x)
  calc
    HomotopyGroup.map (g.comp f) _ q =
        HomotopyGroup.map g rfl (HomotopyGroup.map f rfl q) :=
      (HomotopyGroup.map_comp_apply g rfl f rfl q).symm
    _ = HomotopyGroup.map g rfl 1 := by
      rw [show HomotopyGroup.map f rfl q = 1 from Subsingleton.elim _ _]
    _ = 1 := HomotopyGroup.map_one g rfl

/-- Bundled form of triviality for the zero-five meridian's induced fundamental-group map. -/
theorem zeroFiveMeridianBoundaryInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom x)
        (SSet.toTop.map zeroFiveMeridianBoundaryInclPairwise).hom rfl = 1 := by
  ext q
  exact zeroFiveMeridianBoundaryInclPairwise_piOne_trivial x q

/-- The realized five-four meridian circle maps trivially on fundamental groups into its
pairwise interface, at every basepoint. -/
theorem fiveFourMeridianBoundaryInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom rfl q = 1 := by
  let f : C(SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl fiveFourMeridianBoundaryFacets 11)).hom
  let g : C(SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4))) :=
    (SSet.toTop.map fiveFourMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← fiveFourMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets)) :=
    fiveFourMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet fiveFourMeridianDiskFacets)) (f x)) :=
    subsingleton_homotopyGroup_of_contractible (f x)
  calc
    HomotopyGroup.map (g.comp f) _ q =
        HomotopyGroup.map g rfl (HomotopyGroup.map f rfl q) :=
      (HomotopyGroup.map_comp_apply g rfl f rfl q).symm
    _ = HomotopyGroup.map g rfl 1 := by
      rw [show HomotopyGroup.map f rfl q = 1 from Subsingleton.elim _ _]
    _ = 1 := HomotopyGroup.map_one g rfl

/-- Bundled form of triviality for the five-four meridian's induced fundamental-group map. -/
theorem fiveFourMeridianBoundaryInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom x)
        (SSet.toTop.map fiveFourMeridianBoundaryInclPairwise).hom rfl = 1 := by
  ext q
  exact fiveFourMeridianBoundaryInclPairwise_piOne_trivial x q

/-- The realized four-zero meridian circle maps trivially on fundamental groups into its
pairwise interface, at every basepoint. -/
theorem fourZeroMeridianBoundaryInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom rfl q = 1 := by
  let f : C(SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets),
      SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets)) :=
    (SSet.toTop.map
      (orderedConeBaseIncl fourZeroMeridianBoundaryFacets 10)).hom
  let g : C(SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets),
      SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0))) :=
    (SSet.toTop.map fourZeroMeridianDiskIncl).hom
  have hmap : (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom =
      g.comp f := by
    rw [← fourZeroMeridianBoundaryInclPairwise_factor, Functor.map_comp]
    rfl
  rw [hmap]
  letI : ContractibleSpace (TopCat.disk.{0} 2) := contractibleSpace_disk 2
  letI : ContractibleSpace
      (SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets)) :=
    fourZeroMeridianDiskRealizationHomeomorphDisk.contractibleSpace
  letI : Subsingleton
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet fourZeroMeridianDiskFacets)) (f x)) :=
    subsingleton_homotopyGroup_of_contractible (f x)
  calc
    HomotopyGroup.map (g.comp f) _ q =
        HomotopyGroup.map g rfl (HomotopyGroup.map f rfl q) :=
      (HomotopyGroup.map_comp_apply g rfl f rfl q).symm
    _ = HomotopyGroup.map g rfl 1 := by
      rw [show HomotopyGroup.map f rfl q = 1 from Subsingleton.elim _ _]
    _ = 1 := HomotopyGroup.map_one g rfl

/-- Bundled form of triviality for the four-zero meridian's induced fundamental-group map. -/
theorem fourZeroMeridianBoundaryInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom x)
        (SSet.toTop.map fourZeroMeridianBoundaryInclPairwise).hom rfl = 1 := by
  ext q
  exact fourZeroMeridianBoundaryInclPairwise_piOne_trivial x q

/-! ## The central-to-pairwise composites on fundamental groups -/

/-- The zero-five meridian map through the central interface is pointwise trivial on
fundamental groups. -/
theorem zeroFiveMeridianViaCentralInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom rfl q = 1 := by
  rw [zeroFiveMeridianBoundaryInclPairwise_factor_central]
  exact zeroFiveMeridianBoundaryInclPairwise_piOne_trivial x q

/-- Bundled triviality of the zero-five meridian map through the central interface. -/
theorem zeroFiveMeridianViaCentralInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet zeroFiveMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom x)
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom rfl = 1 := by
  ext q
  exact zeroFiveMeridianViaCentralInclPairwise_piOne_trivial x q

/-- The five-four meridian map through the central interface is pointwise trivial on
fundamental groups. -/
theorem fiveFourMeridianViaCentralInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom rfl q = 1 := by
  rw [fiveFourMeridianBoundaryInclPairwise_factor_central]
  exact fiveFourMeridianBoundaryInclPairwise_piOne_trivial x q

/-- Bundled triviality of the five-four meridian map through the central interface. -/
theorem fiveFourMeridianViaCentralInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet fiveFourMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom x)
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom rfl = 1 := by
  ext q
  exact fiveFourMeridianViaCentralInclPairwise_piOne_trivial x q

/-- The four-zero meridian map through the central interface is pointwise trivial on
fundamental groups. -/
theorem fourZeroMeridianViaCentralInclPairwise_piOne_trivial
    (x : SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets))
    (q : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets)) x) :
    HomotopyGroup.map
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom rfl q = 1 := by
  rw [fourZeroMeridianBoundaryInclPairwise_factor_central]
  exact fourZeroMeridianBoundaryInclPairwise_piOne_trivial x q

/-- Bundled triviality of the four-zero meridian map through the central interface. -/
theorem fourZeroMeridianViaCentralInclPairwise_piOne_mapHom_eq_one
    (x : SSet.toTop.obj (orderedSSet fourZeroMeridianBoundaryFacets)) :
    HomotopyGroup.mapHom (N := Fin 1) (x := x)
        (y := (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom x)
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom rfl = 1 := by
  ext q
  exact fourZeroMeridianViaCentralInclPairwise_piOne_trivial x q

end Submission.ComplexProjectivePlaneTriangulation
