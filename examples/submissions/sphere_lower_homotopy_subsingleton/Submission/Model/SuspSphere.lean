/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Model.Sphere
import Submission.Model.Suspension

/-!
# The suspension of `Sⁿ` is `S^{n+1}`

We construct an explicit homeomorphism `Susp (Sph n) ≃ₜ Sph (n + 1)`.

The map used is the algebraic parametrisation of the meridian circle
`(t, x) ↦ (2√(t(1-t)) • x, 2t - 1) ∈ ℝ^{n+1} × ℝ ≅ ℝ^{n+2}`,
which avoids trigonometric functions: it lands in the unit sphere because
`4t(1-t) + (2t-1)^2 = 1`, it is constant on `{0} × Sⁿ` (value the south pole `(0, -1)`) and on
`{1} × Sⁿ` (value the north pole `(0, 1)`), and the induced map on the suspension is a continuous
bijection from a compact space to a Hausdorff space.

## Main definitions

* `Submission.snocLp` — appending a real number as the last coordinate of a Euclidean vector;
* `Submission.suspSphHomeo` — the homeomorphism `Susp (Sph n) ≃ₜ Sph (n + 1)`.
-/

namespace Submission

open Metric unitInterval

variable {n : ℕ}

/-! ### The meridian coefficient -/

/-- The coefficient `2√(t(1-t))` scaling the equatorial sphere at height `2t - 1`. -/
noncomputable def merCoeff (t : ℝ) : ℝ := 2 * Real.sqrt (t * (1 - t))

theorem merCoeff_nonneg (t : ℝ) : 0 ≤ merCoeff t := by
  rw [merCoeff]; positivity

theorem continuous_merCoeff : Continuous merCoeff := by
  unfold merCoeff; fun_prop

theorem merCoeff_sq {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : merCoeff t ^ 2 = 4 * (t * (1 - t)) := by
  have h : 0 ≤ t * (1 - t) := mul_nonneg h₀ (by linarith)
  rw [merCoeff, mul_pow, Real.sq_sqrt h]
  norm_num

theorem merCoeff_eq_zero_iff {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    merCoeff t = 0 ↔ t = 0 ∨ t = 1 := by
  have h : 0 ≤ t * (1 - t) := mul_nonneg h₀ (by linarith)
  rw [merCoeff, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, Real.sqrt_eq_zero h, mul_eq_zero]
  constructor
  · rintro (h' | h')
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> simp

theorem merCoeff_zero : merCoeff 0 = 0 := by simp [merCoeff]

theorem merCoeff_one : merCoeff 1 = 0 := by simp [merCoeff]

/-! ### The suspension map -/

/-- The map `I × Sⁿ → ℝ^{n+2}` used to identify the suspension of `Sⁿ` with `S^{n+1}`. -/
noncomputable def suspSphFun (p : I × Sph n) : EuclideanSpace ℝ (Fin (n + 1 + 1)) :=
  snocLp (merCoeff (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))) (2 * (p.1 : ℝ) - 1)

theorem norm_suspSphFun (p : I × Sph n) : ‖suspSphFun p‖ = 1 := by
  obtain ⟨⟨t, ht₀, ht₁⟩, ⟨x, hx⟩⟩ := p
  rw [mem_sphere_zero_iff_norm] at hx
  refine norm_eq_one_of_norm_sq_eq_one ?_
  rw [suspSphFun, norm_snocLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only at hx ht₀ ht₁ ⊢
  rw [hx, merCoeff_sq ht₀ ht₁]
  ring

/-- The map `I × Sⁿ → S^{n+1}`. -/
noncomputable def suspSphMap (n : ℕ) : C(I × Sph n, Sph (n + 1)) where
  toFun p := ⟨suspSphFun p, mem_sphere_zero_iff_norm.mpr (norm_suspSphFun p)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_snocLp.comp (Continuous.prodMk ?_ ?_)) _
    · exact (Continuous.smul
        (continuous_merCoeff.comp (continuous_subtype_val.comp continuous_fst))
        (continuous_subtype_val.comp continuous_snd))
    · fun_prop

theorem suspSphMap_apply (p : I × Sph n) : ((suspSphMap n p : Sph (n + 1)) : _) = suspSphFun p :=
  rfl

theorem suspSphMap_zero (x y : Sph n) : suspSphMap n (0, x) = suspSphMap n (0, y) := by
  refine Subtype.ext ?_
  simp only [suspSphMap_apply, suspSphFun, Set.Icc.coe_zero, merCoeff_zero, zero_smul]

theorem suspSphMap_one (x y : Sph n) : suspSphMap n (1, x) = suspSphMap n (1, y) := by
  refine Subtype.ext ?_
  simp only [suspSphMap_apply, suspSphFun, Set.Icc.coe_one, merCoeff_one, zero_smul]

/-- The continuous map `Susp Sⁿ → S^{n+1}` induced by `suspSphMap`. -/
noncomputable def suspSphLift (n : ℕ) : C(Susp (Sph n), Sph (n + 1)) :=
  Susp.lift (suspSphMap n) suspSphMap_zero suspSphMap_one

theorem suspSphLift_mk (p : I × Sph n) : suspSphLift n (Susp.mk p) = suspSphMap n p := rfl

/-! ### Bijectivity -/

theorem suspSphLift_injective : Function.Injective (suspSphLift n) := by
  refine fun a b hab => ?_
  induction a using Susp.ind with
  | h p =>
    induction b using Susp.ind with
    | h q =>
      obtain ⟨⟨t, ht₀, ht₁⟩, x⟩ := p
      obtain ⟨⟨s, hs₀, hs₁⟩, y⟩ := q
      rw [suspSphLift_mk, suspSphLift_mk, Subtype.ext_iff, suspSphMap_apply, suspSphMap_apply,
        suspSphFun, suspSphFun, snocLp_eq_iff] at hab
      obtain ⟨hv, ha⟩ := hab
      simp only at hv ha ht₀ ht₁ hs₀ hs₁
      have hts : t = s := by linarith
      subst hts
      by_cases hc : merCoeff t = 0
      · rcases (merCoeff_eq_zero_iff ht₀ ht₁).mp hc with rfl | rfl
        · exact Susp.mk_eq_mk_of_rel (Or.inr (Or.inl ⟨Subtype.ext rfl, Subtype.ext rfl⟩))
        · exact Susp.mk_eq_mk_of_rel (Or.inr (Or.inr ⟨Subtype.ext rfl, Subtype.ext rfl⟩))
      · have : (x : EuclideanSpace ℝ (Fin (n + 1))) = (y : EuclideanSpace ℝ (Fin (n + 1))) :=
          smul_right_injective _ hc hv
        exact congrArg Susp.mk (Prod.ext rfl (Subtype.ext this))

theorem suspSphLift_surjective : Function.Surjective (suspSphLift n) := by
  rintro ⟨z, hz'⟩
  have hz : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, z (Fin.last (n + 1)) = a := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin (n + 1)),
      WithLp.toLp 2 (fun i : Fin (n + 1) => z i.castSucc) = w := ⟨_, rfl⟩
  have hzsnoc : z = snocLp w a := by
    refine PiLp.ext fun i => ?_
    induction i using Fin.lastCases with
    | last => rw [snocLp_last, ha]
    | cast j => rw [snocLp_castSucc, ← hw]
  have hsum : ‖w‖ ^ 2 + a ^ 2 = 1 := by
    rw [← norm_snocLp_sq, ← hzsnoc, hz, one_pow]
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have ha₁ : a ^ 2 ≤ 1 := by nlinarith
  have ha₀ : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have ha₂ : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  obtain ⟨t, htval⟩ : ∃ t : I, (t : ℝ) = (a + 1) / 2 :=
    ⟨⟨(a + 1) / 2, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩, rfl⟩
  have ht₀ : (0 : ℝ) ≤ (t : ℝ) := by rw [htval]; linarith
  have ht₁ : (t : ℝ) ≤ 1 := by rw [htval]; linarith
  have hcw : merCoeff (t : ℝ) = ‖w‖ := by
    have h1 : merCoeff (t : ℝ) ^ 2 = ‖w‖ ^ 2 := by
      rw [merCoeff_sq ht₀ ht₁, htval]; nlinarith
    have h3 : (merCoeff (t : ℝ) - ‖w‖) * (merCoeff (t : ℝ) + ‖w‖) = 0 := by nlinarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · have h4 : merCoeff (t : ℝ) = 0 := le_antisymm (by linarith) (merCoeff_nonneg _)
      have h5 : ‖w‖ = 0 := by linarith [merCoeff_nonneg (t : ℝ)]
      rw [h4, h5]
  have hlast : 2 * (t : ℝ) - 1 = a := by rw [htval]; ring
  by_cases hw0 : ‖w‖ = 0
  · obtain ⟨x⟩ := instNonemptySph n
    have key : suspSphFun (t, x) = z := by
      simp only [suspSphFun]
      rw [hcw, hlast, hzsnoc, hw0, zero_smul, norm_eq_zero.mp hw0]
    exact ⟨Susp.mk (t, x), Subtype.ext key⟩
  · have hx : ‖(‖w‖⁻¹ • w)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0]
    refine ⟨Susp.mk (t, ⟨‖w‖⁻¹ • w, mem_sphere_zero_iff_norm.mpr hx⟩), Subtype.ext ?_⟩
    show suspSphFun (t, ⟨‖w‖⁻¹ • w, mem_sphere_zero_iff_norm.mpr hx⟩) = z
    simp only [suspSphFun]
    rw [hcw, hlast, hzsnoc, smul_smul, mul_inv_cancel₀ hw0, one_smul]

theorem suspSphLift_bijective : Function.Bijective (suspSphLift n) :=
  ⟨suspSphLift_injective, suspSphLift_surjective⟩

/-- **The suspension of the `n`-sphere is the `(n+1)`-sphere.** -/
noncomputable def suspSphHomeo (n : ℕ) : Susp (Sph n) ≃ₜ Sph (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (suspSphLift n) suspSphLift_bijective) (suspSphLift n).continuous

@[simp]
theorem suspSphHomeo_apply (q : Susp (Sph n)) : suspSphHomeo n q = suspSphLift n q := rfl

end Submission
