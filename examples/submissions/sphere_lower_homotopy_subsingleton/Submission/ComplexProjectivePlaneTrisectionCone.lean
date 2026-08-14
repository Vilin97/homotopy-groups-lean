/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlanePuppe
import Submission.ComplexProjectivePlaneTrisectionBistellar

/-!
# Topological cones on the projective-plane trisection bases

The bistellar certificates identify each realized trisection base with the exact metric
three-sphere.  Transporting the topological cone across those homeomorphisms identifies its
abstract cone with the exact four-disk.  The comparison also sends the cone's base inclusion to
the standard disk-boundary inclusion.
-/

noncomputable section

open CategoryTheory

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The realized trisection base at apex `0`, identified with the exact four-disk boundary. -/
def trisectionPieceZeroBaseRealizationIsoDiskBoundary :
    SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 0)) ≅
      TopCat.diskBoundary.{0} 4 :=
  TopCat.isoOfHomeo
    (trisectionPieceZeroBaseRealizationHomeomorphSphere.trans
      diskBoundaryFourHomeomorphSphereThree.symm)

/-- The topological cone on the realized trisection base at apex `0` is the exact four-disk. -/
def trisectionPieceZeroBaseTopologicalConeIsoDisk :
    topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 0))) ≅
      TopCat.disk.{0} 4 :=
  topologicalConeIso trisectionPieceZeroBaseRealizationIsoDiskBoundary ≪≫
    diskBoundaryFourConeIsoDisk

/-- The apex-`0` cone comparison restricts to the chosen base-to-boundary comparison. -/
@[reassoc]
theorem trisectionPieceZeroBaseTopologicalConeIsoDisk_hom_baseIncl :
    topologicalConeBaseIncl
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 0))) ≫
        trisectionPieceZeroBaseTopologicalConeIsoDisk.hom =
      trisectionPieceZeroBaseRealizationIsoDiskBoundary.hom ≫
        TopCat.diskBoundaryIncl 4 := by
  rw [trisectionPieceZeroBaseTopologicalConeIsoDisk, Iso.trans_hom,
    topologicalConeBaseIncl_iso_hom_assoc,
    diskBoundaryFourConeBaseIncl_isoDisk]

/-- The realized trisection base at apex `5`, identified with the exact four-disk boundary. -/
def trisectionPieceFiveBaseRealizationIsoDiskBoundary :
    SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 5)) ≅
      TopCat.diskBoundary.{0} 4 :=
  TopCat.isoOfHomeo
    (trisectionPieceFiveBaseRealizationHomeomorphSphere.trans
      diskBoundaryFourHomeomorphSphereThree.symm)

/-- The topological cone on the realized trisection base at apex `5` is the exact four-disk. -/
def trisectionPieceFiveBaseTopologicalConeIsoDisk :
    topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 5))) ≅
      TopCat.disk.{0} 4 :=
  topologicalConeIso trisectionPieceFiveBaseRealizationIsoDiskBoundary ≪≫
    diskBoundaryFourConeIsoDisk

/-- The apex-`5` cone comparison restricts to the chosen base-to-boundary comparison. -/
@[reassoc]
theorem trisectionPieceFiveBaseTopologicalConeIsoDisk_hom_baseIncl :
    topologicalConeBaseIncl
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 5))) ≫
        trisectionPieceFiveBaseTopologicalConeIsoDisk.hom =
      trisectionPieceFiveBaseRealizationIsoDiskBoundary.hom ≫
        TopCat.diskBoundaryIncl 4 := by
  rw [trisectionPieceFiveBaseTopologicalConeIsoDisk, Iso.trans_hom,
    topologicalConeBaseIncl_iso_hom_assoc,
    diskBoundaryFourConeBaseIncl_isoDisk]

/-- The realized trisection base at apex `4`, identified with the exact four-disk boundary. -/
def trisectionPieceFourBaseRealizationIsoDiskBoundary :
    SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 4)) ≅
      TopCat.diskBoundary.{0} 4 :=
  TopCat.isoOfHomeo
    (trisectionPieceFourBaseRealizationHomeomorphSphere.trans
      diskBoundaryFourHomeomorphSphereThree.symm)

/-- The topological cone on the realized trisection base at apex `4` is the exact four-disk. -/
def trisectionPieceFourBaseTopologicalConeIsoDisk :
    topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 4))) ≅
      TopCat.disk.{0} 4 :=
  topologicalConeIso trisectionPieceFourBaseRealizationIsoDiskBoundary ≪≫
    diskBoundaryFourConeIsoDisk

/-- The apex-`4` cone comparison restricts to the chosen base-to-boundary comparison. -/
@[reassoc]
theorem trisectionPieceFourBaseTopologicalConeIsoDisk_hom_baseIncl :
    topologicalConeBaseIncl
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 4))) ≫
        trisectionPieceFourBaseTopologicalConeIsoDisk.hom =
      trisectionPieceFourBaseRealizationIsoDiskBoundary.hom ≫
        TopCat.diskBoundaryIncl 4 := by
  rw [trisectionPieceFourBaseTopologicalConeIsoDisk, Iso.trans_hom,
    topologicalConeBaseIncl_iso_hom_assoc,
    diskBoundaryFourConeBaseIncl_isoDisk]

end Submission.ComplexProjectivePlaneTriangulation
