/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfMappingCone
import Submission.Topology.PuppeComparison

/-!
# The Hopf mapping cone in the Puppe sequence

The bottom sphere of the Hopf mapping cone is detected by its normalized degree-two mod-two
cohomology class and is therefore not nullhomotopic.  Homotopy coexactness translates this into
a no-retraction theorem for the cofiber collapse.  This is deliberately the retraction direction
`collapse ≫ r ~ id` on the mapping cone, distinct from a section
`r ≫ collapse ~ id` on the suspension.
-/

open CategoryTheory
open scoped Topology TopCat

noncomputable section

namespace Submission

/-- The Hopf cofiber collapse has no homotopy retraction.  Equivalently, the Hopf mapping cone
cannot be recovered up to homotopy from its top-cell quotient. -/
theorem not_exists_hopfMappingConeCollapse_homotopy_retraction :
    ¬ ∃ r : topologicalSuspension (TopCat.of (Sph 3)) ⟶ hopfMappingCone,
      Nonempty (TopCat.Homotopy
        (topologicalMappingConeCollapse hopfTopCat ≫ r)
        (𝟙 hopfMappingCone)) := by
  intro h
  apply hopfMappingConeIncl_not_nullhomotopic
  exact
    (exists_topologicalMappingConeCollapse_homotopy_retraction_iff_incl_nullhomotopic
      hopfTopCat).mp h

end Submission
