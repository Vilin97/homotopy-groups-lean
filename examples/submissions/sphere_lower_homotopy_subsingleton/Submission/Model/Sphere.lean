/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The sphere `Sⁿ`

This file introduces the notation `Submission.Sph n` for the `n`-sphere in the model used by the
benchmark statement, namely the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`, and records its
basic topological properties. It also sets up `Submission.snocLp`, the identification
`ℝ^m × ℝ ≅ ℝ^{m+1}` obtained by appending a last coordinate, which is how we split off the
suspension direction.

## Main results

* `Submission.snocLp` — appending a last coordinate, with its norm, continuity and injectivity;
* `Submission.SphereSpace`, `Submission.sphereBasepoint` — challenge-independent names for the
  exact metric model and its distinguished first-coordinate point;
* `Submission.instNonemptySph` — `Sⁿ` is nonempty;
* `Submission.instCompactSpaceSph` — `Sⁿ` is compact;
* `Submission.instPathConnectedSpaceSphSucc` — `S^{n+1}` is path connected;
* `Submission.pathConnectedSpace_sph` — `Sⁿ` is path connected for `1 ≤ n`;
* `Submission.sphZeroHomeoBool` — `S⁰` is homeomorphic to `Bool`.
-/

namespace Submission

open Metric

section SnocLp

variable {m : ℕ}

/-- Append a real number as the last coordinate of a Euclidean vector; this is the identification
`ℝ^m × ℝ ≅ ℝ^{m+1}`. -/
noncomputable def snocLp (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp v) a)

@[simp]
theorem snocLp_castSucc (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) (i : Fin m) :
    snocLp v a i.castSucc = v i := by
  simp [snocLp]

@[simp]
theorem snocLp_last (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    snocLp v a (Fin.last m) = a := by
  simp [snocLp]

theorem snocLp_injective :
    Function.Injective (fun p : EuclideanSpace ℝ (Fin m) × ℝ => snocLp p.1 p.2) := by
  rintro ⟨v, a⟩ ⟨w, b⟩ h
  simp only at h
  refine Prod.ext (PiLp.ext fun i => ?_) ?_
  · simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y i.castSucc) h
  · simpa using congrArg (fun y : EuclideanSpace ℝ (Fin (m + 1)) => y (Fin.last m)) h

theorem snocLp_eq_iff {v w : EuclideanSpace ℝ (Fin m)} {a b : ℝ} :
    snocLp v a = snocLp w b ↔ v = w ∧ a = b := by
  constructor
  · intro h
    have h' := snocLp_injective (a₁ := (v, a)) (a₂ := (w, b)) h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem continuous_snocLp :
    Continuous fun p : EuclideanSpace ℝ (Fin m) × ℝ => snocLp p.1 p.2 := by
  have hg : Continuous fun p : EuclideanSpace ℝ (Fin m) × ℝ =>
      (Fin.snoc (WithLp.ofLp p.1) p.2 : Fin (m + 1) → ℝ) := by
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last => simpa using continuous_snd
    | cast j =>
      simpa using (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) j).comp' continuous_fst
  exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)) hg

/-- Every Euclidean vector is the extension of its first coordinates by its last coordinate. -/
theorem eq_snocLp (z : EuclideanSpace ℝ (Fin (m + 1))) :
    z = snocLp (WithLp.toLp 2 fun i : Fin m => z i.castSucc) (z (Fin.last m)) := by
  refine PiLp.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => rw [snocLp_last]
  | cast j => rw [snocLp_castSucc]

/-- Two nonnegative reals with equal squares are equal. -/
theorem eq_of_sq_eq_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

theorem norm_snocLp_sq (v : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    ‖snocLp v a‖ ^ 2 = ‖v‖ ^ 2 + a ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-- If the square of a norm is `1`, the norm is `1`. -/
theorem norm_eq_one_of_norm_sq_eq_one {E : Type*} [NormedAddCommGroup E] {y : E}
    (h : ‖y‖ ^ 2 = 1) : ‖y‖ = 1 := by
  have h1 : (‖y‖ - 1) * (‖y‖ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · linarith [norm_nonneg y]

end SnocLp

/-- The `n`-sphere, in the model used by the benchmark statement: the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))`. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Challenge-independent spelling of the exact metric-sphere model. -/
abbrev SphereSpace (n : ℕ) := Sph n

/-- The first coordinate vector, used as the distinguished point of the metric sphere. -/
noncomputable def sphereBasepoint (n : ℕ) : SphereSpace n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

instance instNonemptySph (n : ℕ) : Nonempty (Sph n) :=
  ⟨⟨EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), by simp⟩⟩

instance instCompactSpaceSph (n : ℕ) : CompactSpace (Sph n) :=
  inferInstanceAs (CompactSpace (Metric.sphere _ _))

/-- The rank of `ℝ^{n+2}` is at least two. -/
theorem one_lt_rank_euclideanSpace (n : ℕ) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
  have h : Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 2 : ℕ) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    simp
  rw [h]
  exact_mod_cast Nat.one_lt_succ_succ n

instance instPathConnectedSpaceSphSucc (n : ℕ) : PathConnectedSpace (Sph (n + 1)) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (one_lt_rank_euclideanSpace n) 0 zero_le_one)

/-- For `n ≥ 1` the sphere `Sⁿ` is path connected. -/
theorem pathConnectedSpace_sph {n : ℕ} (hn : 1 ≤ n) : PathConnectedSpace (Sph n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  infer_instance

section Zero

/-- The two points of `S⁰`, indexed by `Bool`. -/
noncomputable def sphZeroOfBool (b : Bool) : Sph 0 :=
  ⟨EuclideanSpace.single (0 : Fin (0 + 1)) (if b then (1 : ℝ) else -1), by
    rcases b with _ | _ <;> simp⟩

theorem sphZeroOfBool_val_apply (b : Bool) (i : Fin (0 + 1)) :
    (sphZeroOfBool b).1 i = if b then (1 : ℝ) else -1 := by
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  simp [sphZeroOfBool]

/-- Every point of `S⁰` is one of the two points `sphZeroOfBool b`. -/
theorem sphZeroOfBool_surjective : Function.Surjective sphZeroOfBool := by
  rintro ⟨x, hx⟩
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs,
    sq_abs, Real.sqrt_eq_one] at hx
  have hx' : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hx' with h | h
  · refine ⟨true, Subtype.ext (PiLp.ext fun i => ?_)⟩
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rw [sphZeroOfBool_val_apply, if_pos rfl]
    linarith
  · refine ⟨false, Subtype.ext (PiLp.ext fun i => ?_)⟩
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rw [sphZeroOfBool_val_apply, if_neg (by simp)]
    linarith

theorem sphZeroOfBool_injective : Function.Injective sphZeroOfBool := by
  intro a b hab
  have h : (sphZeroOfBool a).1 0 = (sphZeroOfBool b).1 0 := by rw [hab]
  rw [sphZeroOfBool_val_apply, sphZeroOfBool_val_apply] at h
  rcases a with _ | _ <;> rcases b with _ | _ <;> first | rfl | (norm_num at h)

/-- `S⁰` is a two-point discrete space: it is homeomorphic to `Bool`. -/
noncomputable def sphZeroHomeoBool : Sph 0 ≃ₜ Bool :=
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective sphZeroOfBool ⟨sphZeroOfBool_injective, sphZeroOfBool_surjective⟩)
    continuous_of_discreteTopology).symm

instance instDiscreteTopologySphZero : DiscreteTopology (Sph 0) :=
  sphZeroHomeoBool.symm.discreteTopology

end Zero

end Submission
