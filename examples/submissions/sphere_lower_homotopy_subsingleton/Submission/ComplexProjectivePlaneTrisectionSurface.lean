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
set_option maxHeartbeats 4000000

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

/-- Coherent orientations for all nine vertex links of the 26-tetrahedron base at apex `0`.
Entries outside that base's vertex set are empty. -/
def trisectionPieceZeroBaseLinkOrientations :
    TrisectionVertex → List (OrientedTriangle TrisectionVertex) :=
  ![
    [],
    [⟨2, 3, 8⟩, ⟨2, 10, 3⟩, ⟨2, 8, 10⟩, ⟨3, 6, 7⟩, ⟨3, 10, 6⟩,
      ⟨3, 7, 8⟩, ⟨6, 9, 7⟩, ⟨6, 12, 9⟩, ⟨6, 10, 12⟩, ⟨7, 9, 8⟩,
      ⟨8, 9, 12⟩, ⟨8, 12, 10⟩],
    [⟨1, 3, 8⟩, ⟨1, 10, 3⟩, ⟨1, 8, 10⟩, ⟨3, 6, 8⟩, ⟨3, 9, 6⟩,
      ⟨3, 12, 9⟩, ⟨3, 10, 12⟩, ⟨6, 7, 8⟩, ⟨6, 9, 7⟩, ⟨7, 10, 8⟩,
      ⟨7, 9, 12⟩, ⟨7, 12, 10⟩],
    [⟨1, 2, 8⟩, ⟨1, 10, 2⟩, ⟨1, 7, 6⟩, ⟨1, 6, 10⟩, ⟨1, 8, 7⟩,
      ⟨2, 6, 8⟩, ⟨2, 9, 6⟩, ⟨2, 12, 9⟩, ⟨2, 10, 12⟩, ⟨6, 7, 8⟩,
      ⟨6, 9, 12⟩, ⟨6, 12, 10⟩],
    [],
    [],
    [⟨1, 3, 7⟩, ⟨1, 10, 3⟩, ⟨1, 7, 9⟩, ⟨1, 9, 12⟩, ⟨1, 12, 10⟩,
      ⟨2, 8, 3⟩, ⟨2, 3, 9⟩, ⟨2, 7, 8⟩, ⟨2, 9, 7⟩, ⟨3, 8, 7⟩,
      ⟨3, 12, 9⟩, ⟨3, 10, 12⟩],
    [⟨1, 3, 6⟩, ⟨1, 8, 3⟩, ⟨1, 6, 9⟩, ⟨1, 9, 8⟩, ⟨2, 6, 8⟩,
      ⟨2, 9, 6⟩, ⟨2, 8, 10⟩, ⟨2, 12, 9⟩, ⟨2, 10, 12⟩, ⟨3, 8, 6⟩,
      ⟨8, 9, 12⟩, ⟨8, 12, 10⟩],
    [⟨1, 2, 3⟩, ⟨1, 10, 2⟩, ⟨1, 3, 7⟩, ⟨1, 7, 9⟩, ⟨1, 9, 12⟩,
      ⟨1, 12, 10⟩, ⟨2, 6, 3⟩, ⟨2, 7, 6⟩, ⟨2, 10, 7⟩, ⟨3, 6, 7⟩,
      ⟨7, 12, 9⟩, ⟨7, 10, 12⟩],
    [⟨1, 6, 7⟩, ⟨1, 12, 6⟩, ⟨1, 7, 8⟩, ⟨1, 8, 12⟩, ⟨2, 6, 3⟩,
      ⟨2, 3, 12⟩, ⟨2, 7, 6⟩, ⟨2, 12, 7⟩, ⟨3, 6, 12⟩, ⟨7, 12, 8⟩],
    [⟨1, 2, 3⟩, ⟨1, 8, 2⟩, ⟨1, 3, 6⟩, ⟨1, 6, 12⟩, ⟨1, 12, 8⟩,
      ⟨2, 12, 3⟩, ⟨2, 8, 7⟩, ⟨2, 7, 12⟩, ⟨3, 12, 6⟩, ⟨7, 8, 12⟩],
    [],
    [⟨1, 6, 9⟩, ⟨1, 10, 6⟩, ⟨1, 9, 8⟩, ⟨1, 8, 10⟩, ⟨2, 9, 3⟩,
      ⟨2, 3, 10⟩, ⟨2, 7, 9⟩, ⟨2, 10, 7⟩, ⟨3, 9, 6⟩, ⟨3, 6, 10⟩,
      ⟨7, 8, 9⟩, ⟨7, 10, 8⟩]
  ]

/-- The 26-tetrahedron base at apex `0` is pure and connected, every triangle has incidence two,
and all nine vertex links carry explicit closed orientable genus-zero certificates. -/
theorem trisectionPieceZeroBase_hasCombinatorialGenusZeroVertexLinks :
    HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 0)
      trisectionPieceZeroBaseLinkOrientations := by
  unfold HasCombinatorialGenusZeroVertexLinks
  decide

/-- Apply the order-three vertex rotation to an oriented triangle. -/
def rotateOrientedTriangle (triangle : OrientedTriangle TrisectionVertex) :
    OrientedTriangle TrisectionVertex :=
  ⟨trisectionRotationFun triangle.first, trisectionRotationFun triangle.second,
    trisectionRotationFun triangle.third⟩

/-- Transport a family of vertex-link orientations once around the trisection symmetry. -/
def rotateLinkOrientationFamily
    (orientations : TrisectionVertex → List (OrientedTriangle TrisectionVertex)) :
    TrisectionVertex → List (OrientedTriangle TrisectionVertex) :=
  fun v ↦ (orientations (trisectionRotationFun (trisectionRotationFun v))).map
    rotateOrientedTriangle

/-- Link orientations for the base at apex `5`, obtained by one rotation from the base at `0`. -/
def trisectionPieceFiveBaseLinkOrientations :
    TrisectionVertex → List (OrientedTriangle TrisectionVertex) :=
  rotateLinkOrientationFamily trisectionPieceZeroBaseLinkOrientations

/-- Link orientations for the base at apex `4`, obtained by two rotations from the base at `0`. -/
def trisectionPieceFourBaseLinkOrientations :
    TrisectionVertex → List (OrientedTriangle TrisectionVertex) :=
  rotateLinkOrientationFamily trisectionPieceFiveBaseLinkOrientations

/-- The vertex rotation cyclically relabels the three 26-tetrahedron bases. -/
theorem trisectionRotation_pieceBaseFacets :
    (trisectionPieceBaseFacets 0).map
        (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceBaseFacets 5 ∧
      (trisectionPieceBaseFacets 5).map
          (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceBaseFacets 4 ∧
      (trisectionPieceBaseFacets 4).map
          (Finset.mapEmbedding trisectionRotationEmbedding).toEmbedding =
        trisectionPieceBaseFacets 0 := by decide

/-- The rotated 26-tetrahedron base at apex `5` has genus-zero certificates on every vertex link. -/
theorem trisectionPieceFiveBase_hasCombinatorialGenusZeroVertexLinks :
    HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 5)
      trisectionPieceFiveBaseLinkOrientations := by
  unfold HasCombinatorialGenusZeroVertexLinks
  decide

/-- The twice-rotated base at apex `4` has genus-zero certificates on every vertex link. -/
theorem trisectionPieceFourBase_hasCombinatorialGenusZeroVertexLinks :
    HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 4)
      trisectionPieceFourBaseLinkOrientations := by
  unfold HasCombinatorialGenusZeroVertexLinks
  decide

/-- All three trisection-piece bases carry the explicit local genus-zero certificates. -/
theorem trisectionPieceBases_haveCombinatorialGenusZeroVertexLinks :
    HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 0)
        trisectionPieceZeroBaseLinkOrientations ∧
      HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 5)
        trisectionPieceFiveBaseLinkOrientations ∧
      HasCombinatorialGenusZeroVertexLinks (trisectionPieceBaseFacets 4)
        trisectionPieceFourBaseLinkOrientations :=
  ⟨trisectionPieceZeroBase_hasCombinatorialGenusZeroVertexLinks,
    trisectionPieceFiveBase_hasCombinatorialGenusZeroVertexLinks,
    trisectionPieceFourBase_hasCombinatorialGenusZeroVertexLinks⟩

end ComplexProjectivePlaneTriangulation

end Submission
