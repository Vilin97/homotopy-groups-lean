/-
The proof below and the `Submission` modules it imports are adapted from
Vilin97/lean-eval-pi-succ-sphere at commit
1be6cb9b42874415a34defee070f4aa07d6e3193. The copied modules retain their
Apache-2.0 license and attribution headers.
-/
import ChallengeDeps
import Submission.DiagonalInduction
import Submission.DisplayedLowerConnectivity
import Submission.IndependentResults
import Submission.DisplayedCircleFrontier
import Submission.FoundationBenchmarks
import Submission.HigherSphereFoundations
import Submission.Hurewicz.AbsoluteIsomorphism
import Submission.Hurewicz.AbsoluteSurjectivity
import Submission.Hurewicz.ConnectedPair
import Submission.Hurewicz.CubicalShell
import Submission.Hurewicz.CubeFundamentalClass
import Submission.Hurewicz.DeformationClass
import Submission.Hurewicz.FirstHomology
import Submission.Hurewicz.NormalizedBoundary
import Submission.Hurewicz.NormalizedSimplex
import Submission.Hurewicz.RelativeAdditivity
import Submission.Hurewicz.RelativeBoundary
import Submission.Hurewicz.RelativeMap
import Submission.Hurewicz.RelativeSimplicialDescent
import Submission.Hurewicz.RelativeSimplex
import Submission.Hurewicz.RelativeSurjectivity
import Submission.Hurewicz.SimplexCubeClass
import Submission.Hurewicz.SimplexCubeOrientation
import Submission.Hurewicz.SimplexHorn
import Submission.Hurewicz.SimplicialAddition
import Submission.Hurewicz.SimplicialDescent
import Submission.Hurewicz.SimplicialRelation
import Submission.Hurewicz.SimplicialRelationAt
import Submission.Hurewicz.SimplicialIndexShift
import Submission.Hurewicz.SimplicialTelescope
import Submission.Hurewicz.SingularKan
import Submission.Hurewicz.SphereDiagonal
import Submission.Hurewicz.SphereLoopBridge
import Submission.Hurewicz.StickBoundary
import Submission.Hurewicz.StickSphere
import Submission.Lean4TwentyResults
import Submission.MetricSpherePiOne
import Submission.ReducedSuspensionGroup
import Submission.RealProjectiveSpace
import Submission.Model.SphereConnected
import Submission.SphereApproximation
import Submission.SphereDegreeClassification
import Submission.SphereGenerator
import Submission.SphereHomologicalDegree
import Submission.SphereReducedSuspension
import Submission.SphereSuspensionExcision
import Submission.SphereSuspensionHomologyExcision
import Submission.SphereSuspensionHurewicz
import Submission.SphereSuspension
import Submission.SphereSuspensionPointed

open HomotopyGroups
open scoped Topology

namespace Submission

theorem sphere_lower_homotopy_subsingleton (n k : ℕ) (hk : k < n) :
    Subsingleton
      (HomotopyGroup.Pi k (SphereSpace n) (sphereBasepoint n)) := by
  exact subsingleton_homotopyGroup_sphere_of_lt k n hk (sphereBasepoint n)

end Submission
