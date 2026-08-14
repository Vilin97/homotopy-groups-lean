/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.DiskBoundaryCone
import Submission.FiniteOrderedComplexConeRealization
import Submission.ComplexProjectivePlaneTrisectionInterfaceCertificate

/-!
# A controlled three-ball in the projective-plane trisection interface
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def zeroFiveInterfaceBallTwoConeSSetIso :
    orderedSSet
        (zeroFiveInterfaceBallTwoBaseFacets.image (fun facet ↦ insert 9 facet)) ≅
      orderedSSet zeroFiveInterfaceBallTwoFacets :=
  SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
    zeroFiveInterfaceBallTwo_isCone)

/-- The realized cone base included into the realized ten-tetrahedron interface ball. -/
def zeroFiveInterfaceBallTwoBaseIncl :
    orderedSSet zeroFiveInterfaceBallTwoBaseFacets ⟶
      orderedSSet zeroFiveInterfaceBallTwoFacets :=
  orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9 ≫
    zeroFiveInterfaceBallTwoConeSSetIso.hom

noncomputable def zeroFiveInterfaceBallTwoRealizationHomeomorphTopologicalCone :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoFacets) ≃ₜ
      topologicalCone
        (SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) :=
  (TopCat.homeoOfIso
      (SSet.toTop.mapIso zeroFiveInterfaceBallTwoConeSSetIso).symm).trans
    (conedOrderedRealizationHomeomorphTopologicalCone
      zeroFiveInterfaceBallTwoBaseFacets 9
        zeroFiveInterfaceBallTwoBase_apex_not_mem
        zeroFiveInterfaceBallTwoBase_nonempty)

theorem zeroFiveInterfaceBallTwoRealizationHomeomorphTopologicalCone_base
    (x : SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) :
    zeroFiveInterfaceBallTwoRealizationHomeomorphTopologicalCone
        (SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl x) =
      topologicalConeBaseIncl
        (SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) x := by
  let q := zeroFiveInterfaceBallTwoConeSSetIso
  have hcancel :
      SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl ≫
          (SSet.toTop.mapIso q).inv =
        SSet.toTop.map
          (orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9) := by
    rw [zeroFiveInterfaceBallTwoBaseIncl, Functor.map_comp]
    change
      (SSet.toTop.map
          (orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9) ≫
        SSet.toTop.map q.hom) ≫ SSet.toTop.map q.inv =
      SSet.toTop.map
        (orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9)
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Iso.hom_inv_id, Category.comp_id]
  change conedOrderedRealizationHomeomorphTopologicalCone
      zeroFiveInterfaceBallTwoBaseFacets 9
      zeroFiveInterfaceBallTwoBase_apex_not_mem
      zeroFiveInterfaceBallTwoBase_nonempty
      ((TopCat.homeoOfIso (SSet.toTop.mapIso q).symm)
        (SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl x)) = _
  rw [show
      (TopCat.homeoOfIso (SSet.toTop.mapIso q).symm)
          (SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl x) =
        SSet.toTop.map
          (orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9) x by
    have h := ConcreteCategory.congr_hom hcancel x
    change (SSet.toTop.mapIso q).inv
        (SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl x) =
      SSet.toTop.map
        (orderedConeBaseIncl zeroFiveInterfaceBallTwoBaseFacets 9) x
    simpa only [ConcreteCategory.comp_apply] using h]
  exact conedOrderedRealizationHomeomorphTopologicalCone_base
    zeroFiveInterfaceBallTwoBaseFacets 9
      zeroFiveInterfaceBallTwoBase_apex_not_mem
      zeroFiveInterfaceBallTwoBase_nonempty x

noncomputable def zeroFiveInterfaceBallTwoRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoFacets) ≃ₜ
      TopCat.disk.{0} 3 :=
  zeroFiveInterfaceBallTwoRealizationHomeomorphTopologicalCone.trans
    ((TopCat.homeoOfIso (topologicalConeIso
      (TopCat.isoOfHomeo
        zeroFiveInterfaceBallTwoBaseRealizationHomeomorphDiskBoundary))).trans
      (diskBoundarySuccConeHomeomorphDisk (n := 2)))

theorem zeroFiveInterfaceBallTwoRealizationHomeomorphDisk_base
    (x : SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) :
    zeroFiveInterfaceBallTwoRealizationHomeomorphDisk
        (SSet.toTop.map zeroFiveInterfaceBallTwoBaseIncl x) =
      TopCat.diskBoundaryIncl 3
        (zeroFiveInterfaceBallTwoBaseRealizationHomeomorphDiskBoundary x) := by
  let e := TopCat.isoOfHomeo
    zeroFiveInterfaceBallTwoBaseRealizationHomeomorphDiskBoundary
  rw [zeroFiveInterfaceBallTwoRealizationHomeomorphDisk,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    zeroFiveInterfaceBallTwoRealizationHomeomorphTopologicalCone_base]
  have hcone := ConcreteCategory.congr_hom
    (topologicalConeBaseIncl_iso_hom e) x
  have hdisk := ConcreteCategory.congr_hom
    (diskBoundarySuccConeBaseIncl_isoDisk (n := 2)) (e.hom x)
  rw [show
      (TopCat.homeoOfIso (topologicalConeIso e))
          (topologicalConeBaseIncl
            (SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) x) =
        topologicalConeBaseIncl (TopCat.diskBoundary 3) (e.hom x) by
    change (topologicalConeIso e).hom
        (topologicalConeBaseIncl
          (SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets)) x) =
      topologicalConeBaseIncl (TopCat.diskBoundary 3) (e.hom x)
    simpa only [ConcreteCategory.comp_apply] using hcone]
  change (diskBoundarySuccConeIsoDisk (n := 2)).hom
      (topologicalConeBaseIncl (TopCat.diskBoundary 3) (e.hom x)) =
    TopCat.diskBoundaryIncl 3 (e.hom x)
  simpa only [ConcreteCategory.comp_apply, Nat.reduceAdd] using hdisk


end Submission.ComplexProjectivePlaneTriangulation

