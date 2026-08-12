/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.ConnectedPair
import Submission.SphereSuspensionHomologyExcision

/-!
# Hurewicz-range homology of the sphere suspension pairs

The two cap/overlap pairs used by sphere suspension excision are already proved `m`-connected.
The bounded singular-simplex compression theorem therefore kills their relative homology through
degree `m`.  Homological excision transports the same vanishing to the target pair consisting of
the sphere and its upper cap.

Together with the top-degree computations in `Submission.SphereSuspensionHomologyExcision`, this
identifies the complete first-nonzero relative-homology pattern needed by a future natural
relative Hurewicz comparison.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

noncomputable section

namespace Submission

/-- The standard sphere basepoint regarded as a point of the overlap inside the upper cap. -/
noncomputable def sphCapOverlapInUpperBase (m : ℕ) : sphCapOverlapInUpper m :=
  ⟨sphUpperCapBase m, sphereBasepoint_mem_sphLowerCap m⟩

/-- Relative homology of the lower-cap/overlap pair vanishes through its full connectivity
range. -/
theorem isZero_sphLowerCap_overlap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (sphLowerCap m)) k (sphCapOverlapInLower m)) :=
  (isNConnectedPair_sphLowerCap_overlap m hm).isZero_relativeHomology
    ⟨(sphCapOverlapBase m).1, (sphCapOverlapBase m).2⟩ k hk

/-- Relative homology of the upper-cap/overlap pair vanishes through its full connectivity
range. -/
theorem isZero_sphUpperCap_overlap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (sphUpperCap m)) k (sphCapOverlapInUpper m)) :=
  (isNConnectedPair_sphUpperCap_overlap m hm).isZero_relativeHomology
    ⟨(sphCapOverlapInUpperBase m).1, (sphCapOverlapInUpperBase m).2⟩ k hk

/-- Homological excision transports lower-cap connectivity to the target sphere/upper-cap pair:
its relative homology also vanishes through degree `m`. -/
theorem isZero_sphSphere_upperCap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (Sph (m + 1))) k (sphUpperCap m)) := by
  letI := isIso_sphereCapInclusionHrelMap m k
  exact IsZero.of_iso (isZero_sphLowerCap_overlap_relativeHomology m k hm hk)
    (asIso (sphereCapInclusionHrelMap m k)).symm

end Submission
