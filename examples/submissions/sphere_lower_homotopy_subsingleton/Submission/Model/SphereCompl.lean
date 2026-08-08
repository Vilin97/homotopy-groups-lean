/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ForMathlib.HomotopyGroup.Contractible
import Submission.ForMathlib.HomotopyGroup.Map
import Submission.Model.Sphere

/-!
# The complement of a point in `Sⁿ`

The sphere with one point `v` removed is contractible: sliding a point `x ≠ v` along the straight
segment towards the antipode `-v` and projecting radially back to the sphere never meets `v`.
Consequently a based generalized loop in `Sⁿ` which misses some point `v` different from the
basepoint is nullhomotopic, so it is trivial in every homotopy group.

This is the first half of the proof that `π_k(Sⁿ) = 0` for `k < n`; the second half produces, from
an arbitrary generalized loop, a homotopic one which is not surjective.

## Main definitions

* `Submission.radialProj` — radial projection `y ↦ y / ‖y‖` onto the unit sphere;
* `Submission.antipodeSeg` — the straight segment `t ↦ (1 - t) • x - t • v` from `x` to `-v`.

## Main results

* `Submission.contractibleSpace_sphere_compl` — `Sⁿ` minus a point is contractible;
* `Submission.homotopyGroup_eq_one_of_not_surjective` — a based generalized loop in `Sⁿ` avoiding
  a point other than the basepoint is trivial in `π_N(Sⁿ)`.
-/

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

/-! ### Radial projection onto the unit sphere -/

section RadialProj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection of a nonzero vector onto the unit sphere. -/
noncomputable def radialProj (y : E) : E := ‖y‖⁻¹ • y

/-- The radial projection of a nonzero vector is a unit vector. -/
theorem norm_radialProj {y : E} (hy : y ≠ 0) : ‖radialProj y‖ = 1 := by
  rw [radialProj, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- A unit vector is its own radial projection. -/
theorem radialProj_of_norm_eq_one {y : E} (hy : ‖y‖ = 1) : radialProj y = y := by
  rw [radialProj, hy, inv_one, one_smul]

/-- Undoing the radial projection: a nonzero vector is `‖y‖` times its radial projection. -/
theorem smul_norm_radialProj {y : E} (hy : y ≠ 0) : ‖y‖ • radialProj y = y :=
  smul_inv_smul₀ (norm_ne_zero_iff.mpr hy) y

/-- Radial projection is continuous along any continuous nowhere-vanishing family. -/
theorem continuous_radialProj {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f)
    (h0 : ∀ p, f p ≠ 0) : Continuous fun p => radialProj (f p) :=
  (hf.norm.inv₀ fun p => norm_ne_zero_iff.mpr (h0 p)).smul hf

end RadialProj

/-! ### The segment towards the antipode -/

section AntipodeSeg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The straight segment from `x` to the antipode `-v`, parametrized by `t ∈ [0, 1]`. -/
noncomputable def antipodeSeg (v x : E) (t : ℝ) : E := (1 - t) • x - t • v

/-- The segment towards the antipode starts at `x`. -/
@[simp]
theorem antipodeSeg_zero (v x : E) : antipodeSeg v x 0 = x := by
  simp [antipodeSeg]

/-- The segment towards the antipode ends at `-v`. -/
@[simp]
theorem antipodeSeg_one (v x : E) : antipodeSeg v x 1 = -v := by
  simp [antipodeSeg]

/-- The segment from a unit vector `x ≠ v` to the antipode of the unit vector `v` never passes
through the origin: at the only time when the two terms could cancel, namely `t = 1/2`, they are
`x/2` and `v/2`. -/
theorem antipodeSeg_ne_zero {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (hxv : x ≠ v) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : antipodeSeg v x t ≠ 0 := by
  intro h
  rw [antipodeSeg, sub_eq_zero] at h
  have hn : |1 - t| = |t| := by
    have h' := congrArg norm h
    rwa [norm_smul, norm_smul, hx, hv, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at h'
  rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0] at hn
  refine hxv (smul_right_injective E (r := 1 - t) (ne_of_gt (by linarith)) ?_)
  show (1 - t) • x = (1 - t) • v
  rw [h, hn]

/-- The radial projection of the segment towards the antipode of `v` never returns to `v`. -/
theorem radialProj_antipodeSeg_ne {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (hxv : x ≠ v) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : radialProj (antipodeSeg v x t) ≠ v := by
  intro h
  have hy0 : antipodeSeg v x t ≠ 0 := antipodeSeg_ne_zero hv hx hxv ht0 ht1
  have hnpos : 0 < ‖antipodeSeg v x t‖ := norm_pos_iff.mpr hy0
  have hyv : antipodeSeg v x t = ‖antipodeSeg v x t‖ • v :=
    (smul_norm_radialProj hy0).symm.trans
      (congrArg (fun w => ‖antipodeSeg v x t‖ • w) h)
  have hx' : (1 - t) • x = (‖antipodeSeg v x t‖ + t) • v := by
    rw [add_smul]
    exact sub_eq_iff_eq_add.mp hyv
  have hn : |1 - t| = |‖antipodeSeg v x t‖ + t| := by
    have h' := congrArg norm hx'
    rwa [norm_smul, norm_smul, hx, hv, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at h'
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hn
  refine hxv (smul_right_injective E (r := 1 - t) (ne_of_gt (by linarith)) ?_)
  show (1 - t) • x = (1 - t) • v
  rw [hx', hn]

end AntipodeSeg

/-! ### `Sⁿ` minus a point is contractible -/

section SphereCompl

variable {n : ℕ}

/-- The norm of a point of `Sⁿ`, viewed in `ℝ^{n+1}`, is one. -/
theorem norm_coe_sph (x : Sph n) : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

/-- Two points of `Sⁿ` are distinct as soon as their underlying vectors are. -/
theorem coe_ne_coe_of_ne {x v : Sph n} (h : x ≠ v) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ (v : EuclideanSpace ℝ (Fin (n + 1))) :=
  fun hc => h (Subtype.ext hc)

/-- The point of `Sⁿ ∖ {v}` reached from `x` at time `t` while sliding towards the antipode
of `v`. -/
noncomputable def sphContract (v : Sph n) (t : I) (x : {z : Sph n // z ≠ v}) :
    {z : Sph n // z ≠ v} :=
  ⟨⟨radialProj (antipodeSeg (v : EuclideanSpace ℝ (Fin (n + 1)))
      (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ)),
    mem_sphere_zero_iff_norm.mpr
      (norm_radialProj (antipodeSeg_ne_zero (norm_coe_sph v) (norm_coe_sph x.1)
        (coe_ne_coe_of_ne x.2) t.2.1 t.2.2))⟩,
    fun hc => radialProj_antipodeSeg_ne (norm_coe_sph v) (norm_coe_sph x.1)
      (coe_ne_coe_of_ne x.2) t.2.1 t.2.2 (congrArg Subtype.val hc)⟩

/-- The contraction of `Sⁿ ∖ {v}` is jointly continuous in the time and the point. -/
theorem continuous_sphContract (v : Sph n) :
    Continuous fun p : I × {z : Sph n // z ≠ v} => sphContract v p.1 p.2 := by
  refine Continuous.subtype_mk (Continuous.subtype_mk (continuous_radialProj ?_ ?_) _) _
  · unfold antipodeSeg
    fun_prop
  · exact fun p => antipodeSeg_ne_zero (norm_coe_sph v) (norm_coe_sph p.2.1)
      (coe_ne_coe_of_ne p.2.2) p.1.2.1 p.1.2.2

/-- At time `0` the contraction of `Sⁿ ∖ {v}` is the identity. -/
@[simp]
theorem sphContract_zero (v : Sph n) (x : {z : Sph n // z ≠ v}) : sphContract v 0 x = x := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [sphContract]
  simpa using radialProj_of_norm_eq_one (norm_coe_sph x.1)

/-- The antipode of `v`, as a point of `Sⁿ ∖ {v}`. -/
noncomputable def sphAntipode (v : Sph n) : {z : Sph n // z ≠ v} :=
  ⟨⟨-(v : EuclideanSpace ℝ (Fin (n + 1))),
      mem_sphere_zero_iff_norm.mpr (by rw [norm_neg, norm_coe_sph])⟩,
    fun hc => by
      have h : -(v : EuclideanSpace ℝ (Fin (n + 1))) = (v : EuclideanSpace ℝ (Fin (n + 1))) :=
        congrArg Subtype.val hc
      have h0 : (v : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
        have : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
          rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel _
        simpa using this
      have := norm_coe_sph v
      rw [h0, norm_zero] at this
      exact zero_ne_one this⟩

/-- At time `1` the contraction of `Sⁿ ∖ {v}` is constant at the antipode of `v`. -/
@[simp]
theorem sphContract_one (v : Sph n) (x : {z : Sph n // z ≠ v}) :
    sphContract v 1 x = sphAntipode v := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [sphContract, sphAntipode]
  simpa using radialProj_of_norm_eq_one (E := EuclideanSpace ℝ (Fin (n + 1)))
    (y := -(v : EuclideanSpace ℝ (Fin (n + 1)))) (by rw [norm_neg, norm_coe_sph])

/-- **`Sⁿ` minus a point is contractible.** -/
instance contractibleSpace_sphere_compl (n : ℕ) (v : Sph n) :
    ContractibleSpace {z : Sph n // z ≠ v} := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨sphAntipode v, ⟨⟨⟨fun p => sphContract v p.1 p.2, continuous_sphContract v⟩,
    fun x => ?_, fun x => ?_⟩⟩⟩
  · exact sphContract_zero v x
  · exact sphContract_one v x

end SphereCompl

/-! ### A non-surjective generalized loop is nullhomotopic -/

/-- A based generalized loop in `Sⁿ` which misses a point `v` other than the basepoint represents
the identity of `π_N(Sⁿ)`: it factors through the contractible space `Sⁿ ∖ {v}`. -/
theorem homotopyGroup_eq_one_of_not_surjective {N : Type*} [DecidableEq N] [Nonempty N]
    (n : ℕ) (x : Sph n) (f : Ω^ N (Sph n) x) (v : Sph n) (hv : v ≠ x)
    (hf : ∀ y, f y ≠ v) :
    (⟦f⟧ : HomotopyGroup N (Sph n) x) = (1 : HomotopyGroup N (Sph n) x) := by
  let x' : {z : Sph n // z ≠ v} := ⟨x, hv.symm⟩
  let g : Ω^ N {z : Sph n // z ≠ v} x' :=
    ⟨⟨fun t => ⟨f t, hf t⟩, Continuous.subtype_mk f.1.continuous _⟩,
      fun t ht => Subtype.ext (_root_.GenLoop.boundary f t ht)⟩
  let incl : C({z : Sph n // z ≠ v}, Sph n) := ⟨Subtype.val, continuous_subtype_val⟩
  have hsub : Subsingleton (HomotopyGroup N {z : Sph n // z ≠ v} x') :=
    subsingleton_homotopyGroup_of_contractible x'
  have hgf : GenLoop.map incl (rfl : incl x' = x) g = f := _root_.GenLoop.ext _ _ fun t => rfl
  have h2 := congrArg (HomotopyGroup.map incl (rfl : incl x' = x))
    (hsub.elim (⟦g⟧ : HomotopyGroup N {z : Sph n // z ≠ v} x') 1)
  rwa [HomotopyGroup.map_mk, hgf, HomotopyGroup.map_one] at h2

end Submission
