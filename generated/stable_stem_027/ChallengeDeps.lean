import Mathlib

open scoped Topology

namespace HomotopyGroups.StableStems

/-- The unit metric sphere modeling `S^n`. -/
abbrev StableSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first coordinate vector gives the basepoint used for every modeled sphere. -/
noncomputable def stableSphereBasepoint (n : ℕ) : StableSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [StableSphere]⟩



end HomotopyGroups.StableStems
