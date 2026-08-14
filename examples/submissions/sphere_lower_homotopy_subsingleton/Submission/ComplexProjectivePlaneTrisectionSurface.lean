/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisection
import Submission.Cohomology.FiniteOrderedComplexSurface

/-!
# Surface certificates in the projective-plane trisection

The central interface and the triangle family underlying the ten-tetrahedron cone are checked as
closed combinatorial surfaces with coherent orientations.  Their Euler equations give
combinatorial orientable genera one and zero respectively.  These remain finite certificates; no
topological surface-classification or realization homeomorphism is asserted here.
-/

namespace Submission

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- A coherent orientation of the fourteen central triangles. -/
def centralInterfaceOrientation : List (OrientedTriangle TrisectionVertex) :=
  [⟨1, 2, 3⟩, ⟨1, 8, 2⟩, ⟨1, 3, 7⟩, ⟨1, 7, 6⟩, ⟨1, 6, 12⟩,
    ⟨1, 12, 8⟩, ⟨2, 12, 3⟩, ⟨2, 6, 7⟩, ⟨2, 8, 6⟩, ⟨2, 7, 12⟩,
    ⟨3, 6, 8⟩, ⟨3, 12, 6⟩, ⟨3, 8, 7⟩, ⟨7, 8, 12⟩]

/-- The central triangle family is a connected closed combinatorial surface: it is pure,
two triangles meet every edge, and every vertex link is a connected cycle. -/
theorem centralInterface_isClosedCombinatorialSurface :
    IsClosedCombinatorialSurface centralInterfaceFacets := by
  unfold IsClosedCombinatorialSurface IsCycleGraph IsConnectedGraph
  decide

/-- The displayed central orientation uses every triangle once and cancels every directed edge. -/
theorem centralInterfaceOrientation_isCoherent :
    IsCoherentOrientation centralInterfaceFacets centralInterfaceOrientation := by
  unfold IsCoherentOrientation
  decide

/-- The central combinatorial surface has Euler characteristic zero. -/
theorem centralInterface_eulerCharacteristic :
    surfaceEulerCharacteristic centralInterfaceFacets = 0 := by decide

/-- The central surface has the full executable orientable-genus-one certificate. -/
theorem centralInterface_hasCombinatorialOrientableGenusOne :
    HasCombinatorialOrientableGenus centralInterfaceFacets 1 := by
  refine ⟨centralInterface_isClosedCombinatorialSurface,
    centralInterfaceOrientation, centralInterfaceOrientation_isCoherent, ?_⟩
  decide

/-- The central one-skeleton is neighborly: every pair of its seven vertices is an edge. -/
theorem centralInterface_oneSkeleton_complete :
    facesOfCard centralInterfaceFacets 2 = centralInterfaceVertices.powersetCard 2 := by decide

/-- A coherent orientation of the ten-triangle cone base. -/
def zeroFiveInterfaceBallTwoBaseOrientation :
    List (OrientedTriangle TrisectionVertex) :=
  [⟨1, 6, 7⟩, ⟨2, 7, 6⟩, ⟨1, 7, 8⟩, ⟨2, 6, 3⟩, ⟨1, 12, 6⟩,
    ⟨3, 6, 12⟩, ⟨2, 3, 12⟩, ⟨2, 12, 7⟩, ⟨7, 12, 8⟩, ⟨1, 8, 12⟩]

/-- The cone-base triangle family is a connected closed combinatorial surface. -/
theorem zeroFiveInterfaceBallTwoBase_isClosedCombinatorialSurface :
    IsClosedCombinatorialSurface zeroFiveInterfaceBallTwoBaseFacets := by
  unfold IsClosedCombinatorialSurface IsCycleGraph IsConnectedGraph
  decide

/-- The displayed cone-base orientation uses every triangle once and cancels every directed edge. -/
theorem zeroFiveInterfaceBallTwoBaseOrientation_isCoherent :
    IsCoherentOrientation zeroFiveInterfaceBallTwoBaseFacets
      zeroFiveInterfaceBallTwoBaseOrientation := by
  unfold IsCoherentOrientation
  decide

/-- The cone-base combinatorial surface has Euler characteristic two. -/
theorem zeroFiveInterfaceBallTwoBase_eulerCharacteristic :
    surfaceEulerCharacteristic zeroFiveInterfaceBallTwoBaseFacets = 2 := by decide

/-- The cone base has the full executable orientable-genus-zero certificate. -/
theorem zeroFiveInterfaceBallTwoBase_hasCombinatorialOrientableGenusZero :
    HasCombinatorialOrientableGenus zeroFiveInterfaceBallTwoBaseFacets 0 := by
  refine ⟨zeroFiveInterfaceBallTwoBase_isClosedCombinatorialSurface,
    zeroFiveInterfaceBallTwoBaseOrientation,
    zeroFiveInterfaceBallTwoBaseOrientation_isCoherent, ?_⟩
  decide

end ComplexProjectivePlaneTriangulation

end Submission
