/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneMinimalHopfBallInteriorBoundaryCollapse
import Submission.ComplexProjectivePlaneMinimalHopfCollapsedAttachingCoordinates
import Submission.SphereHomologicalDegree

/-!
# Comparing the finite Hopf and collapsed attaching maps in metric-sphere coordinates

The attaching-domain comparison is transported through the maintained homeomorphisms from both
finite domain realizations to the exact metric three-sphere.  It becomes a self-homotopy-
equivalence of `S³`, and precomposing the finite Hopf sphere map by this equivalence makes it
homotopic to the collapsed projective-plane attaching sphere map.

This result compares the two certified finite maps without asserting that their chosen domain
coordinates have degree `+1`, or that either coordinate formula is literally the quadratic Hopf
map.
-/

noncomputable section

open CategoryTheory Simplicial TopCat
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

set_option maxRecDepth 100000

/-- The certified attaching-domain comparison, transported to a self-homotopy-equivalence of
the exact metric three-sphere. -/
noncomputable def minimalHopfAttachingDomainSphereHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (SphereSpace 3) (SphereSpace 3) :=
  minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree.symm.toHomotopyEquiv.trans
    (minimalHopfAttachingDomainComparisonHomotopyEquiv.trans
      minimalHopfDomainRealizationHomeomorphSphereThree.toHomotopyEquiv)

/-- After the certified self-equivalence of the metric domain sphere, the finite Hopf sphere
map is homotopic to the collapsed projective-plane attaching sphere map. -/
noncomputable def minimalHopfAttachingSphereMapHomotopyFiniteHopf :
    ContinuousMap.Homotopy
      (minimalHopfSphereCoordinateTopCat.hom.comp
        minimalHopfAttachingDomainSphereHomotopyEquiv.toFun)
      minimalHopfProjectivePlaneTargetAttachingSphereMap.hom := by
  let H :=
    (ContinuousMap.Homotopy.refl
      (⟨minimalHopfTargetRealizationHomeomorphSphereTwo,
        minimalHopfTargetRealizationHomeomorphSphereTwo.continuous⟩ : C(_, _))).comp
      (minimalHopfAttachingMapHomotopyFiniteHopf.compContinuousMap
        (⟨minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree.symm,
          minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree.symm.continuous⟩ :
            C(_, _)))
  apply H.cast
  · apply ContinuousMap.ext
    intro x
    change minimalHopfTargetRealizationHomeomorphSphereTwo
        (minimalHopfRealizationMap
          (minimalHopfAttachingDomainComparison
            (minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree.symm x))) =
      minimalHopfTargetRealizationHomeomorphSphereTwo
        (minimalHopfRealizationMap
          (minimalHopfDomainRealizationHomeomorphSphereThree.symm
            (minimalHopfDomainRealizationHomeomorphSphereThree
              (minimalHopfAttachingDomainComparisonHomotopyEquiv.toFun
                (minimalHopfProjectivePlaneInteriorBoundaryRealizationHomeomorphSphereThree.symm x)))))
    rw [minimalHopfAttachingDomainComparisonHomotopyEquiv_toFun,
      Homeomorph.symm_apply_apply]
  · apply ContinuousMap.ext
    intro x
    rfl

/-- Proposition-valued form of the metric-sphere attaching comparison. -/
theorem minimalHopfProjectivePlaneTargetAttachingSphereMap_homotopic_finiteHopf :
    (minimalHopfSphereCoordinateTopCat.hom.comp
        minimalHopfAttachingDomainSphereHomotopyEquiv.toFun).Homotopic
      minimalHopfProjectivePlaneTargetAttachingSphereMap.hom :=
  ⟨minimalHopfAttachingSphereMapHomotopyFiniteHopf⟩

/-- The unresolved coordinate change has degree `+1` or `-1`; proving which sign occurs is a
separate orientation comparison. -/
theorem minimalHopfAttachingDomainSphereHomologicalDegree :
    sphereHomologicalDegree 2
          (TopCat.ofHom minimalHopfAttachingDomainSphereHomotopyEquiv.toFun) = 1 ∨
      sphereHomologicalDegree 2
          (TopCat.ofHom minimalHopfAttachingDomainSphereHomotopyEquiv.toFun) = -1 :=
  sphereHomologicalDegree_eq_one_or_neg_one_of_homotopyInverse 2
    (TopCat.ofHom minimalHopfAttachingDomainSphereHomotopyEquiv.toFun)
    (TopCat.ofHom minimalHopfAttachingDomainSphereHomotopyEquiv.invFun)
    (Classical.choice minimalHopfAttachingDomainSphereHomotopyEquiv.left_inv)

end Submission.ComplexProjectivePlaneTriangulation
