/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.HopfFibration

/-!
# Higher homotopy equivalences induced by the Hopf fibration

Because the fibre of the exact Hopf map is a circle, its homotopy groups vanish above degree
one.  The fibration long exact sequence therefore identifies the homotopy groups of `S^3` and
`S^2` in every degree at least three.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- The homomorphism on homotopy in degree `k+3` induced by the exact Hopf map. -/
noncomputable def hopfPiHigherHom (k : ℕ) :
    π_ (k + 3) (Sph 3) (sphereBasepoint 3) →*
      π_ (k + 3) (Sph 2) (sphereBasepoint 2) :=
  pStarAbsHom hopfFiberBasepoint (k + 2)

@[simp]
theorem hopfPiHigherHom_apply (k : ℕ)
    (x : π_ (k + 3) (Sph 3) (sphereBasepoint 3)) :
    hopfPiHigherHom k x = pStarAbs hopfFiberBasepoint (k + 3) x := by
  exact pStarAbsHom_apply hopfFiberBasepoint (k + 2) x

/-- In every degree at least three, the exact Hopf map induces a bijection on homotopy groups. -/
theorem hopfPiHigherHom_bijective (k : ℕ) :
    Function.Bijective (hopfPiHigherHom k) := by
  have h := bijective_pStarAbs_of_subsingleton_fibre hopfFiberBasepoint
    hopfMap_isSerreFibration (k + 2)
    (hopfFiber_higher_homotopy_subsingleton (k + 1))
    (hopfFiber_higher_homotopy_subsingleton k)
  have heq : (⇑(hopfPiHigherHom k)) = pStarAbs hopfFiberBasepoint (k + 3) := by
    funext x
    exact hopfPiHigherHom_apply k x
  rw [heq]
  exact h

/-- The exact Hopf map identifies `pi_(k+3)(S^3)` with `pi_(k+3)(S^2)`. -/
noncomputable def hopfPiHigherEquiv (k : ℕ) :
    π_ (k + 3) (Sph 3) (sphereBasepoint 3) ≃*
      π_ (k + 3) (Sph 2) (sphereBasepoint 2) :=
  MulEquiv.ofBijective (hopfPiHigherHom k) (hopfPiHigherHom_bijective k)

/-- Any computation of `pi_(k+3)(S^3)` transports across the Hopf fibration to the
corresponding group of `S^2`. -/
theorem sphereTwo_higher_mulEquiv_of_sphereThree
    (k : ℕ) (G : Type*) [Group G]
    (h : Nonempty (π_ (k + 3) (Sph 3) (sphereBasepoint 3) ≃* G)) :
    Nonempty (π_ (k + 3) (Sph 2) (sphereBasepoint 2) ≃* G) := by
  obtain ⟨e⟩ := h
  exact ⟨(hopfPiHigherEquiv k).symm.trans e⟩

/-- The previously constructed third-homotopy equivalence is the degree-three instance of the
uniform higher Hopf equivalence, up to equality of bundled equivalences. -/
theorem hopfPiHigherEquiv_zero_eq :
    hopfPiHigherEquiv 0 = hopfPiThreeEquiv hopfMap_isSerreFibration := by
  ext x
  rfl

end Submission
