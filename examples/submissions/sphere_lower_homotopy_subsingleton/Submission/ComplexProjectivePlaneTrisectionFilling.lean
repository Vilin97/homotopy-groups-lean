/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexConeRealization
import Submission.ComplexProjectivePlaneTrisectionCone

/-!
# Exact four-disks for the trisection pieces and explicit fillings

The general finite-cone comparison identifies each 26-facet trisection piece with the abstract
topological cone on its certified three-sphere base.  The existing cone-to-disk comparison then
shows that every original piece is an exact closed four-disk.  Transporting across the certified
four-dimensional bistellar sequences gives the same exact disk model for all three explicit
14-facet fillings.

## Main results

* `trisectionPieceZeroRealizationHomeomorphDisk` and its two rotated analogues;
* `trisectionPieceZeroBistellarBallResultRealizationHomeomorphDisk` and its two rotated analogues.
-/

noncomputable section

set_option maxRecDepth 100000

open CategoryTheory

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- No facet of a trisection cone base contains the erased cone apex. -/
theorem trisectionPieceBaseFacets_apex_not_mem (a : TrisectionVertex) :
    ∀ facet ∈ trisectionPieceBaseFacets a, a ∉ facet := by
  intro facet hfacet
  obtain ⟨simplex, _, rfl⟩ := Finset.mem_image.mp hfacet
  simp

/-- The base at apex `0` contains a nonempty tetrahedral facet. -/
theorem trisectionPieceZeroBaseFacets_nonempty :
    ∃ facet ∈ trisectionPieceBaseFacets 0, facet.Nonempty := by
  exact ⟨{1, 2, 3, 8}, by decide, by decide⟩

/-- The base at apex `5` contains a nonempty tetrahedral facet. -/
theorem trisectionPieceFiveBaseFacets_nonempty :
    ∃ facet ∈ trisectionPieceBaseFacets 5, facet.Nonempty := by
  exact ⟨{1, 2, 3, 8}, by decide, by decide⟩

/-- The base at apex `4` contains a nonempty tetrahedral facet. -/
theorem trisectionPieceFourBaseFacets_nonempty :
    ∃ facet ∈ trisectionPieceBaseFacets 4, facet.Nonempty := by
  exact ⟨{1, 2, 3, 7}, by decide, by decide⟩

/-- The original finite trisection piece at apex `0` realizes as the abstract cone on its
realized base. -/
noncomputable def trisectionPieceZeroRealizationHomeomorphTopologicalCone :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 0)) ≃ₜ
      topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 0))) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      (trisectionPieceFacets_isCone 0 (by decide))))).symm).trans
    (conedOrderedRealizationHomeomorphTopologicalCone
      (trisectionPieceBaseFacets 0) 0
        (trisectionPieceBaseFacets_apex_not_mem 0)
        trisectionPieceZeroBaseFacets_nonempty)

/-- The original 26-facet trisection piece at apex `0` realizes as the exact four-disk. -/
noncomputable def trisectionPieceZeroRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 0)) ≃ₜ
      TopCat.disk.{0} 4 :=
  trisectionPieceZeroRealizationHomeomorphTopologicalCone.trans
    (TopCat.homeoOfIso trisectionPieceZeroBaseTopologicalConeIsoDisk)

/-- The explicit 14-facet filling at apex `0` realizes as the exact four-disk. -/
noncomputable def trisectionPieceZeroBistellarBallResultRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet trisectionPieceZeroBistellarBallResult) ≃ₜ
      TopCat.disk.{0} 4 :=
  (TopCat.homeoOfIso trisectionPieceZeroBistellarBallRealizationIso.symm).trans
    trisectionPieceZeroRealizationHomeomorphDisk

/-- The original finite trisection piece at apex `5` realizes as the abstract cone on its
realized base. -/
noncomputable def trisectionPieceFiveRealizationHomeomorphTopologicalCone :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 5)) ≃ₜ
      topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 5))) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      (trisectionPieceFacets_isCone 5 (by decide))))).symm).trans
    (conedOrderedRealizationHomeomorphTopologicalCone
      (trisectionPieceBaseFacets 5) 5
        (trisectionPieceBaseFacets_apex_not_mem 5)
        trisectionPieceFiveBaseFacets_nonempty)

/-- The original 26-facet trisection piece at apex `5` realizes as the exact four-disk. -/
noncomputable def trisectionPieceFiveRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 5)) ≃ₜ
      TopCat.disk.{0} 4 :=
  trisectionPieceFiveRealizationHomeomorphTopologicalCone.trans
    (TopCat.homeoOfIso trisectionPieceFiveBaseTopologicalConeIsoDisk)

/-- The explicit 14-facet filling at apex `5` realizes as the exact four-disk. -/
noncomputable def trisectionPieceFiveBistellarBallResultRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet trisectionPieceFiveBistellarBallResult) ≃ₜ
      TopCat.disk.{0} 4 :=
  (TopCat.homeoOfIso trisectionPieceFiveBistellarBallRealizationIso.symm).trans
    trisectionPieceFiveRealizationHomeomorphDisk

/-- The original finite trisection piece at apex `4` realizes as the abstract cone on its
realized base. -/
noncomputable def trisectionPieceFourRealizationHomeomorphTopologicalCone :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 4)) ≃ₜ
      topologicalCone
        (SSet.toTop.obj (orderedSSet (trisectionPieceBaseFacets 4))) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.Subcomplex.eqToIso (congrArg orderedSubcomplex
      (trisectionPieceFacets_isCone 4 (by decide))))).symm).trans
    (conedOrderedRealizationHomeomorphTopologicalCone
      (trisectionPieceBaseFacets 4) 4
        (trisectionPieceBaseFacets_apex_not_mem 4)
        trisectionPieceFourBaseFacets_nonempty)

/-- The original 26-facet trisection piece at apex `4` realizes as the exact four-disk. -/
noncomputable def trisectionPieceFourRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet (trisectionPieceFacets 4)) ≃ₜ
      TopCat.disk.{0} 4 :=
  trisectionPieceFourRealizationHomeomorphTopologicalCone.trans
    (TopCat.homeoOfIso trisectionPieceFourBaseTopologicalConeIsoDisk)

/-- The explicit 14-facet filling at apex `4` realizes as the exact four-disk. -/
noncomputable def trisectionPieceFourBistellarBallResultRealizationHomeomorphDisk :
    SSet.toTop.obj (orderedSSet trisectionPieceFourBistellarBallResult) ≃ₜ
      TopCat.disk.{0} 4 :=
  (TopCat.homeoOfIso trisectionPieceFourBistellarBallRealizationIso.symm).trans
    trisectionPieceFourRealizationHomeomorphDisk

end Submission.ComplexProjectivePlaneTriangulation
