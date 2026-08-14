/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionFilling
import Submission.Cohomology.DiskPair

/-!
# Bistellar certificate for a projective-plane trisection interface

The two-dimensional base of the ten-tetrahedron cone component in the zero-five interface is
reduced by three verified bistellar moves to the boundary of a tetrahedron. Consequently its
ordered realization is a two-sphere, hence the boundary of the three-disk.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def zeroFiveInterfaceBallTwoBaseBistellarMoves :
    List (BistellarMoveData TrisectionVertex) :=
  [⟨{3}, {2, 6, 12}⟩,
    ⟨{2}, {6, 7, 12}⟩,
    ⟨{6}, {1, 7, 12}⟩]

theorem zeroFiveInterfaceBallTwoBaseBistellarMoves_valid :
    IsValidBistellarMoveSequence zeroFiveInterfaceBallTwoBaseFacets 2
      zeroFiveInterfaceBallTwoBaseBistellarMoves := by decide

theorem zeroFiveInterfaceBallTwoBase_bistellar_result :
    applyBistellarMoves zeroFiveInterfaceBallTwoBaseFacets
        zeroFiveInterfaceBallTwoBaseBistellarMoves =
      simplexBoundaryFacets {1, 7, 8, 12} := by decide

theorem zeroFiveInterfaceBallTwoBase_isBistellarTwoSphere :
    IsBistellarSphere zeroFiveInterfaceBallTwoBaseFacets 2 :=
  ⟨zeroFiveInterfaceBallTwoBaseBistellarMoves, {1, 7, 8, 12}, by decide,
    zeroFiveInterfaceBallTwoBaseBistellarMoves_valid,
    zeroFiveInterfaceBallTwoBase_bistellar_result⟩

noncomputable def zeroFiveInterfaceBallTwoBaseRealizationHomeomorphSphere :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets) ≃ₜ
      SphereSpace 2 :=
  zeroFiveInterfaceBallTwoBase_isBistellarTwoSphere
    |>.nonempty_realizationHomeomorphSphere.some

noncomputable def zeroFiveInterfaceBallTwoBaseRealizationHomeomorphDiskBoundary :
    SSet.toTop.obj (orderedSSet zeroFiveInterfaceBallTwoBaseFacets) ≃ₜ
      TopCat.diskBoundary.{0} 3 :=
  zeroFiveInterfaceBallTwoBaseRealizationHomeomorphSphere.trans
    (diskBoundaryHomeoSph 2).symm

theorem zeroFiveInterfaceBallTwoBase_apex_not_mem :
    ∀ facet ∈ zeroFiveInterfaceBallTwoBaseFacets, 9 ∉ facet := by decide

theorem zeroFiveInterfaceBallTwoBase_nonempty :
    ∃ facet ∈ zeroFiveInterfaceBallTwoBaseFacets, facet.Nonempty := by decide

end Submission.ComplexProjectivePlaneTriangulation

