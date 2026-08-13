/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlanePuppe
import Submission.SuspendedHopfMap
import Submission.Topology.SuspensionComparison

/-!
# Comparing the exact projective attaching map with the suspended Hopf map

This file transports the suspension of the exact four-cell attaching map through the explicit
boundary-sphere and projective-line-sphere coordinates. The resulting square identifies it
with the quotient-model suspension of the concrete Hopf map.
-/

open CategoryTheory
open scoped Topology TopCat

noncomputable section

namespace Submission

noncomputable local instance : Nonempty (TopCat.diskBoundary.{0} 4) :=
  ⟨diskBoundaryFourHomeomorphSphereThree.symm (sphereBasepoint 3)⟩

/-- The mapping-cone suspension of `∂D⁴`, expressed as the quotient suspension of `S³`. -/
noncomputable def diskBoundaryFourSuspensionIsoHopfSource :
    topologicalSuspension (TopCat.diskBoundary.{0} 4) ≅
      TopCat.of (Susp (Sph 3)) :=
  (topologicalSuspensionIsoSusp (TopCat.diskBoundary 4)).trans
    (TopCat.isoOfHomeo
      (Susp.mapHomeomorph diskBoundaryFourHomeomorphSphereThree))

/-- The mapping-cone suspension of `CP¹`, expressed as the quotient suspension of `S²`. -/
noncomputable def complexProjectiveLineSuspensionIsoHopfTarget :
    topologicalSuspension (TopCat.of (ComplexProjectiveModel 1)) ≅
      TopCat.of (Susp (Sph 2)) :=
  (topologicalSuspensionIsoSusp
      (TopCat.of (ComplexProjectiveModel 1))).trans
    (TopCat.isoOfHomeo
      (Susp.mapHomeomorph complexProjectiveLineHomeomorphSphere))

/-- Suspending the exact attaching-map square gives the raw quotient-suspension Hopf square. -/
theorem exactHopfSuspension_raw_square :
    TopCat.ofHom (Susp.map diskBoundaryFourComplexHopfMap.hom) ≫
        TopCat.ofHom (Susp.map
          (complexProjectiveLineHomeomorphSphere :
            C(ComplexProjectiveModel 1, Sph 2))) =
      TopCat.ofHom (Susp.map
          (diskBoundaryFourHomeomorphSphereThree :
            C(TopCat.diskBoundary 4, Sph 3))) ≫
        hopfSuspensionTopCat := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  induction q using Susp.ind with
  | h p =>
      rcases p with ⟨t, z⟩
      simp only [ConcreteCategory.comp_apply]
      change Susp.mk
          (t, complexProjectiveLineHomeomorphSphere
            (diskBoundaryFourComplexHopfMap z)) =
        Susp.mk (t, hopfMap (diskBoundaryFourHomeomorphSphereThree z))
      exact congrArg (fun y ↦ (Susp.mk (t, y) : Susp (Sph 2)))
        (ConcreteCategory.congr_hom
          diskBoundaryFourComplexHopfMap_is_hopfMap z)

/-- In mapping-cone suspension coordinates, the exact projective attaching map suspends to the
raw quotient-model suspension of the concrete Hopf map. -/
theorem exactHopfSuspension_comparison :
    topologicalSuspensionMap (TopCat.diskBoundary 4)
          diskBoundaryFourComplexHopfMap ≫
        complexProjectiveLineSuspensionIsoHopfTarget.hom =
      diskBoundaryFourSuspensionIsoHopfSource.hom ≫
        hopfSuspensionTopCat := by
  rw [complexProjectiveLineSuspensionIsoHopfTarget,
    diskBoundaryFourSuspensionIsoHopfSource, Iso.trans_hom,
    Iso.trans_hom]
  change (topologicalSuspensionMap (TopCat.diskBoundary 4)
          diskBoundaryFourComplexHopfMap ≫
        topologicalSuspensionToSusp
          (TopCat.of (ComplexProjectiveModel 1))) ≫
      TopCat.ofHom (Susp.map
        (complexProjectiveLineHomeomorphSphere :
          C(ComplexProjectiveModel 1, Sph 2))) =
    (topologicalSuspensionToSusp (TopCat.diskBoundary 4) ≫
      TopCat.ofHom (Susp.map
        (diskBoundaryFourHomeomorphSphereThree :
          C(TopCat.diskBoundary 4, Sph 3)))) ≫
      hopfSuspensionTopCat
  rw [topologicalSuspensionToSusp_natural]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ topologicalSuspensionToSusp
      (TopCat.diskBoundary 4) ≫ q) exactHopfSuspension_raw_square

/-- The mapping cone of the suspended exact attaching map, before changing sphere coordinates. -/
noncomputable abbrev exactHopfSuspensionMappingCone : TopCat.{0} :=
  topologicalMappingCone
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)

/-- Changing the suspension coordinates identifies the mapping cone of the exact attaching map
with the raw suspended-Hopf mapping cone. -/
noncomputable def exactHopfSuspensionMappingConeIso :
    exactHopfSuspensionMappingCone ≅ hopfSuspensionMappingCone :=
  topologicalMappingConeIso
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

/-- The same coordinate change, followed by the chosen suspension-sphere coordinates, identifies
the exact suspended attaching cone with the concrete suspended-Hopf cone. -/
noncomputable def exactHopfSuspensionMappingConeIsoConcrete :
    exactHopfSuspensionMappingCone ≅ suspendedHopfMappingCone :=
  exactHopfSuspensionMappingConeIso.trans hopfSuspensionMappingConeIso

@[reassoc]
theorem exactHopfSuspensionMappingConeIso_hom_incl :
    topologicalMappingConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫
        exactHopfSuspensionMappingConeIso.hom =
      complexProjectiveLineSuspensionIsoHopfTarget.hom ≫
        topologicalMappingConeIncl hopfSuspensionTopCat := by
  exact topologicalMappingConeIncl_map
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

@[reassoc]
theorem exactHopfSuspensionMappingConeIso_hom_coneIncl :
    topologicalMappingConeConeIncl
          (topologicalSuspensionMap (TopCat.diskBoundary 4)
            diskBoundaryFourComplexHopfMap) ≫
        exactHopfSuspensionMappingConeIso.hom =
      topologicalConeMap diskBoundaryFourSuspensionIsoHopfSource.hom ≫
        topologicalMappingConeConeIncl hopfSuspensionTopCat := by
  exact topologicalMappingConeConeIncl_map
    (topologicalSuspensionMap (TopCat.diskBoundary 4)
      diskBoundaryFourComplexHopfMap)
    hopfSuspensionTopCat diskBoundaryFourSuspensionIsoHopfSource.hom
    complexProjectiveLineSuspensionIsoHopfTarget.hom
    exactHopfSuspension_comparison

end Submission
