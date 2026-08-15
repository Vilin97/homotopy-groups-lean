/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneProjectiveLineCofiberHomotopy
import Submission.Hurewicz.RelativeAdditivity

/-!
# Comparing the projective-line pair with its cofiber

The geometric collapse `CP² → S⁴` is a canonical based map from the literal pair
`(CP², CP¹)` to the point pair `(S⁴, {basepoint})`.  This file packages the induced maps on
fourth relative homotopy and homology and records the naturality square for the relative
Hurewicz homomorphism.
-/

open CategoryTheory
open scoped Topology Topology.Homotopy TopCat

noncomputable section

namespace Submission

/-- The maintained point subspace of the metric four-sphere. -/
def sphereFourBasepointSet : Set (Sph 4) :=
  {sphereBasepoint 4}

/-- The maintained sphere basepoint regarded as a point of its singleton subspace. -/
def sphereFourBasepointInSet : sphereFourBasepointSet :=
  ⟨sphereBasepoint 4, rfl⟩

/-- The geometric projective-line collapse preserves the maintained basepoints. -/
@[simp]
theorem complexProjectivePlaneProjectiveLineCollapse_basepoint :
    complexProjectivePlaneProjectiveLineCollapse
        (complexProjectiveModelBasepoint 2) =
      sphereBasepoint 4 := by
  change complexProjectivePlaneCellCollapse
      (complexProjectivePlaneCellHomeomorph.symm
        (complexProjectiveModelBasepoint 2)) =
    sphereBasepoint 4
  rw [← complexProjectivePlaneCellHomeomorph_basepoint,
    complexProjectivePlaneCellHomeomorph.symm_apply_apply]
  exact complexProjectivePlaneCellCollapse_basepoint

/-- The geometric collapse as a based map from the literal projective-line pair to the
point pair of `S⁴`. -/
noncomputable def complexProjectivePlaneProjectiveLineCollapsePairMap :
    BasedPairMap complexProjectivePlaneProjectiveLine sphereFourBasepointSet
      complexProjectivePlaneProjectiveLineBasepoint sphereFourBasepointInSet where
  toContinuousMap := complexProjectivePlaneProjectiveLineCollapse.hom
  mapsTo' := by
    intro x hx
    change complexProjectivePlaneProjectiveLineCollapse x = sphereBasepoint 4
    have hbase :
        complexProjectiveModelBasepoint 2 ∈
          complexProjectivePlaneProjectiveLine := by
      rw [← complexProjectivePlaneProjectiveLineBasepoint_coe]
      exact complexProjectivePlaneProjectiveLineBasepoint.property
    calc
      complexProjectivePlaneProjectiveLineCollapse x =
          complexProjectivePlaneProjectiveLineCollapse
            (complexProjectiveModelBasepoint 2) :=
        (complexProjectivePlaneProjectiveLineCollapse_eq_iff x
          (complexProjectiveModelBasepoint 2)).2 (Or.inr ⟨hx, hbase⟩)
      _ = sphereBasepoint 4 :=
        complexProjectivePlaneProjectiveLineCollapse_basepoint
  map_basepoint' := by
    simpa only [sphereFourBasepointInSet,
      complexProjectivePlaneProjectiveLineBasepoint_coe] using
        complexProjectivePlaneProjectiveLineCollapse_basepoint

/-- The map on fourth relative homotopy induced by collapsing the projective line. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom :
    π_rel 4 (ComplexProjectiveModel 2) complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint →*
      π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet :=
  RelHomotopyGroup.mapHom 2
    complexProjectivePlaneProjectiveLineCollapsePairMap

/-- The collapse map on fourth relative homotopy, written additively. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom :
    Additive
        (π_rel 4 (ComplexProjectiveModel 2) complexProjectivePlaneProjectiveLine
          complexProjectivePlaneProjectiveLineBasepoint) →+
      Additive (π_rel 4 (Sph 4) sphereFourBasepointSet sphereFourBasepointInSet) :=
  complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom.toAdditive

/-- The map on fourth relative integral homology induced by collapsing the projective line. -/
noncomputable def complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse :
    HrelSet (Y := TopCat.of (ComplexProjectiveModel 2)) 4
        complexProjectivePlaneProjectiveLine ⟶
      HrelSet (Y := TopCat.of (Sph 4)) 4 sphereFourBasepointSet :=
  complexProjectivePlaneProjectiveLineCollapsePairMap.hrelMap 4

/-- The degree-four relative Hurewicz comparison commutes with the canonical projective-line
collapse. -/
theorem complexProjectivePlaneProjectiveLineCollapse_relativeHurewicz_naturality
    (x : π_rel 4 (ComplexProjectiveModel 2)
      complexProjectivePlaneProjectiveLine
      complexProjectivePlaneProjectiveLineBasepoint) :
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
        (relativeHurewicz 2 complexProjectivePlaneProjectiveLine
          complexProjectivePlaneProjectiveLineBasepoint x) =
      relativeHurewicz 2 sphereFourBasepointSet sphereFourBasepointInSet
        (complexProjectivePlaneProjectiveLineRelativePiFourCollapseHom x) := by
  exact relativeHurewicz_naturality 2
    complexProjectivePlaneProjectiveLineCollapsePairMap x

/-- Additive form of the degree-four relative Hurewicz naturality square. -/
theorem complexProjectivePlaneProjectiveLineCollapse_relativeHurewiczAdd_naturality
    (x : Additive
      (π_rel 4 (ComplexProjectiveModel 2)
        complexProjectivePlaneProjectiveLine
        complexProjectivePlaneProjectiveLineBasepoint)) :
    complexProjectivePlaneProjectiveLineRelativeHomologyFourCollapse
        (relativeHurewiczAdd 2 complexProjectivePlaneProjectiveLine
          complexProjectivePlaneProjectiveLineBasepoint x) =
      relativeHurewiczAdd 2 sphereFourBasepointSet sphereFourBasepointInSet
        (complexProjectivePlaneProjectiveLineRelativePiFourCollapseAddHom x) := by
  exact complexProjectivePlaneProjectiveLineCollapse_relativeHurewicz_naturality x.toMul

end Submission
