/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.Pair
import Submission.Cohomology.Sphere
import Submission.Topology.MappingCone

/-!
# Relative cohomology of a cone

Since a topological cone is contractible, the long exact sequence of its base pair identifies
positive relative cone cohomology with shifted cohomology of the base.  The vanishing form below
is the part needed for low-degree mapping-cone calculations.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable (R : Type) [CommRing R]

/-- If degree-`k` cohomology of the base vanishes, degree-`k+1` relative cohomology of its cone
vanishes. -/
theorem isZero_HrelCoh_coneBaseIncl_of_subsingleton_Hsing
    (A : TopCat.{0}) (k : ℕ) [Subsingleton (Hsing k A R)] :
    IsZero (HrelCoh (topologicalConeBaseIncl A) (AddCommGrpCat.of R) (k + 1)) := by
  exact isZero_HrelCoh_of_isZero_subspace_of_isZero_space
    (topologicalConeBaseIncl A) (AddCommGrpCat.of R) k
    (isZero_dualHomology_of_subsingleton_Hsing R k)
    (isZero_dualHomology_of_contractible R (k + 1) (by omega))

/-- Relative cohomology of `(Cone Sⁿ, Sⁿ)` vanishes in degree `k+1` away from degree one
and the shifted top degree. -/
theorem isZero_HrelCoh_cone_sphere (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (HrelCoh (topologicalConeBaseIncl (TopCat.of (Sph n)))
      (AddCommGrpCat.of R) (k + 1)) := by
  letI : Subsingleton (Hsing k (TopCat.of (Sph n)) R) :=
    subsingleton_Hsing_sphere R k n hk hkn
  exact isZero_HrelCoh_coneBaseIncl_of_subsingleton_Hsing R
    (TopCat.of (Sph n)) k

end Submission
