/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.SphereCompl

/-!
# Homotopies of maps into a sphere

This file packages the radial-projection argument used by the piecewise-affine sphere
approximation.  A continuous homotopy through nonzero vectors in the ambient Euclidean space
projects to a homotopy in the sphere.  When its endpoints and its values on the cube boundary
are unit vectors, radial projection fixes them, so the resulting homotopy is a based generalized
loop homotopy.

The second result gives the frequently used close-maps criterion: two based maps into a unit
sphere which stay at ambient distance less than one are homotopic relative to the cube boundary
by the normalized straight-line homotopy.

## Main results

* `Submission.genLoopHomotopic_of_radialHomotopy` — radial projection of a nowhere-vanishing
  ambient homotopy gives a based sphere homotopy;
* `Submission.genLoopHomotopic_of_dist_lt_one` — uniformly close based sphere maps are based
  homotopic.
-/

open scoped unitInterval Topology Topology.Homotopy

namespace Submission

section RadialHomotopy

variable {N : Type*} {n : ℕ} {x : Sph n}

/-- Radial projection of a nowhere-vanishing ambient homotopy gives a homotopy of generalized
loops in the unit sphere.  The explicit endpoint and boundary hypotheses make this lemma useful
for approximation constructions whose intermediate maps do not themselves land in the sphere.
-/
theorem genLoopHomotopic_of_radialHomotopy
    (f g : Ω^ N (Sph n) x)
    (H : C(I × I^N, EuclideanSpace ℝ (Fin (n + 1))))
    (hHne : ∀ p, H p ≠ 0)
    (hzero : ∀ y, radialProj (H (0, y)) =
      ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))))
    (hone : ∀ y, radialProj (H (1, y)) =
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))))
    (hboundary : ∀ s y, y ∈ Cube.boundary N →
      radialProj (H (s, y)) =
        ((x : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))) :
    _root_.GenLoop.Homotopic f g := by
  refine ⟨⟨⟨⟨fun st =>
      ⟨radialProj (H st), mem_sphere_zero_iff_norm.mpr (norm_radialProj (hHne st))⟩,
      Continuous.subtype_mk (continuous_radialProj H.continuous hHne) _⟩,
    fun y => ?_, fun y => ?_⟩, fun s y hy => ?_⟩⟩
  · refine Subtype.ext ?_
    change radialProj (H (0, y)) = _
    exact hzero y
  · refine Subtype.ext ?_
    change radialProj (H (1, y)) = _
    exact hone y
  · refine Subtype.ext ?_
    change radialProj (H (s, y)) = _
    rw [hboundary s y hy]
    exact congrArg Subtype.val ((_root_.GenLoop.boundary f y hy).symm)

end RadialHomotopy

section CloseMaps

variable {N : Type*} {n : ℕ} {x : Sph n}

/-- The straight-line homotopy in the ambient Euclidean space between two sphere-valued
generalized loops. -/
noncomputable def sphereLinearHomotopyAmbient (f g : Ω^ N (Sph n) x) :
    C(I × I^N, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun p := (1 - (p.1 : ℝ)) •
      ((f p.2 : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) +
    (p.1 : ℝ) • ((g p.2 : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
  continuous_toFun := by
    have ht : Continuous fun p : I × I^N => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).smul
      (continuous_subtype_val.comp (f.1.continuous.comp continuous_snd))).add
      (ht.smul (continuous_subtype_val.comp (g.1.continuous.comp continuous_snd)))

@[simp]
theorem sphereLinearHomotopyAmbient_apply (f g : Ω^ N (Sph n) x) (t : I) (y : I^N) :
    sphereLinearHomotopyAmbient f g (t, y) =
      (1 - (t : ℝ)) • ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) +
        (t : ℝ) • ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) :=
  rfl

@[simp]
theorem sphereLinearHomotopyAmbient_zero (f g : Ω^ N (Sph n) x) (y : I^N) :
    sphereLinearHomotopyAmbient f g (0, y) =
      ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp

@[simp]
theorem sphereLinearHomotopyAmbient_one (f g : Ω^ N (Sph n) x) (y : I^N) :
    sphereLinearHomotopyAmbient f g (1, y) =
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp

/-- The ambient straight-line homotopy between unit vectors at distance less than one never
passes through the origin. -/
theorem sphereLinearHomotopyAmbient_ne_zero (f g : Ω^ N (Sph n) x)
    (hfg : ∀ y, dist
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
      ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) < 1) :
    ∀ p, sphereLinearHomotopyAmbient f g p ≠ 0 := by
  rintro ⟨t, y⟩ hzero
  have hdist : dist (sphereLinearHomotopyAmbient f g (t, y))
      ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) < 1 := by
    rw [dist_eq_norm]
    have hrw : sphereLinearHomotopyAmbient f g (t, y) -
          ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) =
        (t : ℝ) • (((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) -
          ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))) := by
      rw [sphereLinearHomotopyAmbient_apply, smul_sub, sub_smul, one_smul]
      abel
    rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    calc
      (t : ℝ) * ‖((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) -
          ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))‖
          ≤ 1 * ‖((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) -
            ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
        mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg _)
      _ = dist
          ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
          ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) := by
        rw [one_mul, dist_eq_norm]
      _ < 1 := hfg y
  rw [hzero, dist_zero_left, norm_coe_sph] at hdist
  exact (lt_irrefl 1 hdist)

/-- **Close based maps into a sphere are based homotopic.**  If the underlying unit vectors are
pointwise less than distance one apart, radial projection of their straight-line interpolation
is a homotopy relative to the cube boundary. -/
theorem genLoopHomotopic_of_dist_lt_one (f g : Ω^ N (Sph n) x)
    (hfg : ∀ y, dist
      ((g y : Sph n) : EuclideanSpace ℝ (Fin (n + 1)))
      ((f y : Sph n) : EuclideanSpace ℝ (Fin (n + 1))) < 1) :
    _root_.GenLoop.Homotopic f g := by
  apply genLoopHomotopic_of_radialHomotopy f g (sphereLinearHomotopyAmbient f g)
      (sphereLinearHomotopyAmbient_ne_zero f g hfg)
  · intro y
    rw [sphereLinearHomotopyAmbient_zero,
      radialProj_of_norm_eq_one (norm_coe_sph (f y))]
  · intro y
    rw [sphereLinearHomotopyAmbient_one,
      radialProj_of_norm_eq_one (norm_coe_sph (g y))]
  · intro s y hy
    rw [sphereLinearHomotopyAmbient_apply]
    rw [_root_.GenLoop.boundary f y hy, _root_.GenLoop.boundary g y hy, ← add_smul]
    norm_num
    exact radialProj_of_norm_eq_one (norm_coe_sph x)

end CloseMaps

end Submission
