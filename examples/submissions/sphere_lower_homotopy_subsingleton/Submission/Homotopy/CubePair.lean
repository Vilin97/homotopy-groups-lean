/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.MulAction
import Submission.Homotopy.Fibration
import Submission.WhiteheadTheorem.Shapes.Cube

/-!
# Lifting along the cube–jar inclusion

Let `⊔I^(k+1)` be `Cube.boundaryJar (k+1)`, the boundary of the cube `I^(k+1)` with the interior
of its top face removed. The key geometric input for the long exact sequence of a Serre fibration
is that a Serre fibration has the lifting property along the inclusion `⊔I^(k+1) ↪ I^(k+1)`.

Classically one proves this by exhibiting a homeomorphism of pairs
`(I^(k+1), ⊔I^(k+1)) ≃ (I^k × I, I^k × {0})`. We use a cheaper substitute: the inclusion
`⊔I^(k+1) ↪ I^(k+1)` is a *retract*, in the arrow category, of `I^k × {0} ↪ I^k × I`, and lifting
properties are inherited by retracts of arrows.

The retraction data is completely explicit. Identify `I × I^k` with the cube `[-1,1]^k × [-1,1]`
and look at the pencil of rays emanating from the apex `(0, 3)` sitting above it. Every such ray
that meets the cube enters through the top face and leaves through the jar; parametrising the ray
through the point `u` of the top face by the scale factor `s ∈ [1, t u]`, where `t u` is the
parameter of the exit point, gives coordinates `(u, s)` on the cube in which the jar is the graph
of `t`. Shearing by `t` turns the jar into a face, at the cost of no longer being surjective —
which is exactly the freedom that a retract of arrows allows.

## Main definitions

* `Submission.HasRLPAlong p ι` — `p` has the lifting property along `ι`.
* `Submission.botIncl A` — the inclusion of `A` as the bottom `{0} × A` of `I × A`.
* `Submission.CubeJar.jarSet k` — the jar `{0} × I^k ∪ I × ∂I^k` inside `I × I^k`.
* `Submission.homotopyJarSet k` — the "homotopy jar" `(I × ⊔I^(k+1)) ∪ (∂I × I^(k+1))`.

## Main results

* `Submission.HasRLPAlong.of_retract` — lifting properties pass to retracts of arrows.
* `Submission.IsSerreFibration.hasRLPAlong_jarIncl` — a Serre fibration lifts along
  `jarSet k ↪ I × I^k`.
* `Submission.IsSerreFibration.hasRLPAlong_boundaryJarIncl` — a Serre fibration lifts along
  `⊔I^(k+1) ↪ I^(k+1)`.
* `Submission.IsSerreFibration.hasRLPAlong_homotopyJarIncl` — a Serre fibration lifts along
  `homotopyJarSet k ↪ I × I^(k+1)`; this is the version used to prove injectivity of `p_*`.
-/

noncomputable section

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

section RLP

variable {A A' X X' B E : Type*} [TopologicalSpace A] [TopologicalSpace A']
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace B] [TopologicalSpace E]

/-- `p : C(E, B)` has the *relative lifting property* along `ι : C(A, X)` if every commutative
square with left leg `ι` and right leg `p` admits a diagonal filler. -/
def HasRLPAlong (p : C(E, B)) (ι : C(A, X)) : Prop :=
  ∀ (f : C(X, B)) (g : C(A, E)), (∀ a, p (g a) = f (ι a)) →
    ∃ G : C(X, E), (∀ a, G (ι a) = g a) ∧ ∀ x, p (G x) = f x

/-- The inclusion of `A` as the bottom `{0} × A` of the cylinder `I × A`. -/
def botIncl (A : Type*) [TopologicalSpace A] : C(A, I × A) :=
  ⟨fun a => (0, a), continuous_const.prodMk continuous_id⟩

@[simp]
theorem botIncl_apply (a : A) : botIncl A a = (0, a) := rfl

/-- The homotopy lifting property is the lifting property along the bottom of the cylinder. -/
theorem HasHLP.hasRLPAlong_botIncl {p : C(E, B)} (h : HasHLP p A) :
    HasRLPAlong p (botIncl A) := fun f g hg => h g f fun a => (hg a).symm

/-- Lifting properties are inherited by retracts in the arrow category. -/
theorem HasRLPAlong.of_retract {p : C(E, B)} {ι : C(A, X)} {ι' : C(A', X')}
    (S : C(X, X')) (R : C(X', X)) (s : C(A, A')) (r : C(A', A))
    (hS : ∀ a, S (ι a) = ι' (s a)) (hR : ∀ a', R (ι' a') = ι (r a'))
    (hRS : ∀ x, R (S x) = x) (hrs : ∀ a, r (s a) = a) (h : HasRLPAlong p ι') :
    HasRLPAlong p ι := by
  intro f g hg
  obtain ⟨G, hG₁, hG₂⟩ := h (f.comp R) (g.comp r) (fun a' => by
    simp only [ContinuousMap.comp_apply, hR a']
    exact hg (r a'))
  refine ⟨G.comp S, fun a => ?_, fun x => ?_⟩
  · simp only [ContinuousMap.comp_apply, hS a, hG₁ (s a), hrs a]
  · simpa [hRS x] using hG₂ (S x)

end RLP

namespace CubeJar

variable {k : ℕ}

/-! ### Coordinates -/

/-- The affine rescaling of the cube `I^k` onto `[-1,1]^k`. -/
def cen (y : I^ Fin k) : Fin k → ℝ := fun i => 2 * (y i : ℝ) - 1

theorem continuous_cen : Continuous (cen : (I^ Fin k) → Fin k → ℝ) :=
  continuous_pi fun i =>
    ((continuous_subtype_val.comp (continuous_apply i)).const_smul (2 : ℝ)).sub continuous_const

theorem abs_cen_le_one (y : I^ Fin k) (i : Fin k) : |cen y i| ≤ 1 := by
  have h := (y i).2
  rw [Set.mem_Icc] at h
  rw [abs_le]
  constructor <;> simp only [cen] <;> linarith [h.1, h.2]

theorem norm_cen_le_one (y : I^ Fin k) : ‖cen y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs]; exact abs_cen_le_one y i

theorem abs_le_norm (v : Fin k → ℝ) (i : Fin k) : |v i| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i

/-- On a vector of nonzero sup norm the sup norm is attained at some coordinate. -/
theorem exists_abs_eq_norm {v : Fin k → ℝ} (hv : ‖v‖ ≠ 0) : ∃ i, |v i| = ‖v‖ := by
  have hne : Nonempty (Fin k) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv (le_antisymm ((pi_norm_le_iff_of_nonneg le_rfl).2 fun i => isEmptyElim i)
      (norm_nonneg v))
  obtain ⟨i, hi⟩ := Finite.exists_max fun j : Fin k => |v j|
  refine ⟨i, le_antisymm (abs_le_norm v i) ?_⟩
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]; exact hi j

/-- A point of the cube lies on the boundary exactly when its rescaling has sup norm `1`. -/
theorem mem_boundary_iff_norm_cen (y : I^ Fin k) : y ∈ (∂I^k) ↔ ‖cen y‖ = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    refine le_antisymm (norm_cen_le_one y) ?_
    have habs : |cen y i| = 1 := by
      simp only [cen]
      rcases hi with hi | hi
      · rw [← Set.Icc.coe_eq_zero] at hi
        rw [hi]; norm_num
      · rw [← Set.Icc.coe_eq_one] at hi
        rw [hi]; norm_num
    exact habs ▸ abs_le_norm (cen y) i
  · intro h
    obtain ⟨i, hi⟩ := exists_abs_eq_norm (v := cen y) (by rw [h]; norm_num)
    rw [h] at hi
    simp only [cen] at hi
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hi with h1 | h1
    · exact ⟨i, Or.inr (Set.Icc.coe_eq_one.1 (by linarith))⟩
    · exact ⟨i, Or.inl (Set.Icc.coe_eq_zero.1 (by linarith))⟩

/-! ### The radial scale -/

/-- `mfun u = max ‖u‖ 2⁻¹`, the denominator of the radial scale. -/
def mfun (u : Fin k → ℝ) : ℝ := max ‖u‖ 2⁻¹

/-- The radial scale `tfun u = 1 / max ‖u‖ 2⁻¹`: it equals `1/‖u‖` when `‖u‖ ≥ 1/2` and `2`
otherwise, and is the parameter at which the ray from the apex through `u` exits the cube. -/
def tfun (u : Fin k → ℝ) : ℝ := (mfun u)⁻¹

theorem inv_two_le_mfun (u : Fin k → ℝ) : (2:ℝ)⁻¹ ≤ mfun u := le_max_right _ _

theorem mfun_pos (u : Fin k → ℝ) : 0 < mfun u :=
  lt_of_lt_of_le (by norm_num) (inv_two_le_mfun u)

theorem norm_le_mfun (u : Fin k → ℝ) : ‖u‖ ≤ mfun u := le_max_left _ _

theorem mfun_le_one {u : Fin k → ℝ} (h : ‖u‖ ≤ 1) : mfun u ≤ 1 := max_le h (by norm_num)

theorem tfun_pos (u : Fin k → ℝ) : 0 < tfun u := inv_pos.2 (mfun_pos u)

theorem tfun_le_two (u : Fin k → ℝ) : tfun u ≤ 2 := by
  have h := inv_anti₀ (by norm_num : (0:ℝ) < 2⁻¹) (inv_two_le_mfun u)
  rw [inv_inv] at h
  exact h

theorem one_le_tfun {u : Fin k → ℝ} (h : ‖u‖ ≤ 1) : 1 ≤ tfun u :=
  (one_le_inv₀ (mfun_pos u)).2 (mfun_le_one h)

theorem tfun_mul_norm_le_one (u : Fin k → ℝ) : tfun u * ‖u‖ ≤ 1 := by
  rw [tfun, inv_mul_eq_div, div_le_one (mfun_pos u)]
  exact norm_le_mfun u

/-- When the sup norm is at most `1/2` the exit parameter is `2`: the ray leaves through the
bottom face. -/
theorem tfun_eq_two {u : Fin k → ℝ} (h : ‖u‖ ≤ 2⁻¹) : tfun u = 2 := by
  rw [tfun, mfun, max_eq_right h, inv_inv]

/-- When the sup norm is at least `1/2` the ray leaves through the side, at parameter `1/‖u‖`. -/
theorem tfun_mul_norm_eq_one {u : Fin k → ℝ} (h : (2:ℝ)⁻¹ ≤ ‖u‖) : tfun u * ‖u‖ = 1 := by
  have hpos : 0 < ‖u‖ := lt_of_lt_of_le (by norm_num) h
  rw [tfun, mfun, max_eq_left h, inv_mul_cancel₀ hpos.ne']

theorem continuous_tfun : Continuous (tfun : (Fin k → ℝ) → ℝ) :=
  (continuous_norm.max continuous_const).inv₀ fun u => (mfun_pos u).ne'

/-! ### The retraction data -/

/-- The direction of the point `z` of `I × I^k`, i.e. the point of the top face lying on the
ray from the apex through `z`. -/
def dir (z : I × (I^ Fin k)) : Fin k → ℝ := (2 - (z.1 : ℝ))⁻¹ • cen z.2

theorem one_le_two_sub (t : I) : 1 ≤ 2 - (t : ℝ) := by
  have h := t.2; rw [Set.mem_Icc] at h; linarith [h.2]

theorem two_sub_le_two (t : I) : 2 - (t : ℝ) ≤ 2 := by
  have h := t.2; rw [Set.mem_Icc] at h; linarith [h.1]

theorem two_sub_pos (t : I) : 0 < 2 - (t : ℝ) := lt_of_lt_of_le zero_lt_one (one_le_two_sub t)

theorem norm_dir (z : I × (I^ Fin k)) : ‖dir z‖ = ‖cen z.2‖ / (2 - (z.1 : ℝ)) := by
  rw [dir, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (two_sub_pos z.1))]
  ring

theorem norm_dir_le_one (z : I × (I^ Fin k)) : ‖dir z‖ ≤ 1 := by
  rw [norm_dir, div_le_one (two_sub_pos z.1)]
  exact le_trans (norm_cen_le_one z.2) (one_le_two_sub z.1)

theorem continuous_dir : Continuous (dir : I × (I^ Fin k) → Fin k → ℝ) := by
  have h1 : Continuous fun z : I × (I^ Fin k) => (2 - (z.1 : ℝ))⁻¹ :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).inv₀
      fun z => (two_sub_pos z.1).ne'
  exact h1.smul (continuous_cen.comp continuous_snd)

theorem inv_two_le_inv_two_sub (t : I) : (2:ℝ)⁻¹ ≤ (2 - (t : ℝ))⁻¹ :=
  inv_anti₀ (two_sub_pos t) (two_sub_le_two t)

theorem norm_dir_le_inv_two_sub (z : I × (I^ Fin k)) : ‖dir z‖ ≤ (2 - (z.1 : ℝ))⁻¹ := by
  rw [norm_dir, div_le_iff₀ (two_sub_pos z.1), inv_mul_cancel₀ (two_sub_pos z.1).ne']
  exact norm_cen_le_one z.2

/-- The key inequality: the ray parameter of `z` never exceeds the exit parameter. -/
theorem two_sub_le_tfun_dir (z : I × (I^ Fin k)) : 2 - (z.1 : ℝ) ≤ tfun (dir z) := by
  have hm : mfun (dir z) ≤ (2 - (z.1 : ℝ))⁻¹ :=
    max_le (norm_dir_le_inv_two_sub z) (inv_two_le_inv_two_sub z.1)
  calc 2 - (z.1 : ℝ) = ((2 - (z.1 : ℝ))⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ tfun (dir z) := inv_anti₀ (mfun_pos _) hm

/-! ### The map `S` -/

theorem Sfst_mem (z : I × (I^ Fin k)) : (z.1 : ℝ) + tfun (dir z) - 2 ∈ I := by
  have h := z.1.2
  rw [Set.mem_Icc] at h ⊢
  refine ⟨by linarith [two_sub_le_tfun_dir z], ?_⟩
  linarith [tfun_le_two (dir z), h.2]

theorem Ssnd_mem (z : I × (I^ Fin k)) (i : Fin k) : (dir z i + 1) / 2 ∈ I := by
  have h : |dir z i| ≤ 1 := le_trans (abs_le_norm _ i) (norm_dir_le_one z)
  rw [abs_le] at h
  rw [Set.mem_Icc]
  constructor <;> linarith [h.1, h.2]

/-- The embedding of `I × I^k` into itself that shears the jar onto the bottom face. -/
def Smap (z : I × (I^ Fin k)) : I × (I^ Fin k) :=
  (⟨(z.1 : ℝ) + tfun (dir z) - 2, Sfst_mem z⟩, fun i => ⟨(dir z i + 1) / 2, Ssnd_mem z i⟩)

theorem continuous_Smap : Continuous (Smap : I × (I^ Fin k) → I × (I^ Fin k)) := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _)
    (continuous_pi fun i => Continuous.subtype_mk ?_ _)
  · exact ((continuous_subtype_val.comp continuous_fst).add
      (continuous_tfun.comp continuous_dir)).sub continuous_const
  · exact (((continuous_apply i).comp continuous_dir).add continuous_const).div_const 2

theorem cen_Smap_snd (z : I × (I^ Fin k)) : cen (Smap z).2 = dir z := by
  funext i
  simp only [cen, Smap]
  ring

/-! ### The map `R` -/

/-- The scale factor used by the retraction `Rmap`. -/
def rScale (z : I × (I^ Fin k)) : ℝ := max 1 (tfun (cen z.2) - (z.1 : ℝ))

theorem one_le_rScale (z : I × (I^ Fin k)) : 1 ≤ rScale z := le_max_left _ _

theorem rScale_pos (z : I × (I^ Fin k)) : 0 < rScale z :=
  lt_of_lt_of_le zero_lt_one (one_le_rScale z)

theorem rScale_le_tfun (z : I × (I^ Fin k)) : rScale z ≤ tfun (cen z.2) := by
  have h := z.1.2
  rw [Set.mem_Icc] at h
  exact max_le (one_le_tfun (norm_cen_le_one z.2)) (by linarith [h.1])

theorem rScale_le_two (z : I × (I^ Fin k)) : rScale z ≤ 2 :=
  le_trans (rScale_le_tfun z) (tfun_le_two _)

theorem continuous_rScale : Continuous (rScale : I × (I^ Fin k) → ℝ) :=
  continuous_const.max
    ((continuous_tfun.comp (continuous_cen.comp continuous_snd)).sub
      (continuous_subtype_val.comp continuous_fst))

theorem Rfst_mem (z : I × (I^ Fin k)) : 2 - rScale z ∈ I := by
  rw [Set.mem_Icc]
  exact ⟨by linarith [rScale_le_two z], by linarith [one_le_rScale z]⟩

theorem Rsnd_mem (z : I × (I^ Fin k)) (i : Fin k) : (rScale z * cen z.2 i + 1) / 2 ∈ I := by
  have h1 : |rScale z * cen z.2 i| ≤ 1 := by
    rw [abs_mul, abs_of_pos (rScale_pos z)]
    calc rScale z * |cen z.2 i| ≤ tfun (cen z.2) * ‖cen z.2‖ :=
          mul_le_mul (rScale_le_tfun z) (abs_le_norm _ i) (abs_nonneg _) (tfun_pos _).le
      _ ≤ 1 := tfun_mul_norm_le_one _
  rw [abs_le] at h1
  rw [Set.mem_Icc]
  constructor <;> linarith [h1.1, h1.2]

/-- The retraction of `I × I^k` onto the image of `Smap`. -/
def Rmap (z : I × (I^ Fin k)) : I × (I^ Fin k) :=
  (⟨2 - rScale z, Rfst_mem z⟩, fun i => ⟨(rScale z * cen z.2 i + 1) / 2, Rsnd_mem z i⟩)

theorem continuous_Rmap : Continuous (Rmap : I × (I^ Fin k) → I × (I^ Fin k)) := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _)
    (continuous_pi fun i => Continuous.subtype_mk ?_ _)
  · exact continuous_const.sub continuous_rScale
  · exact ((continuous_rScale.mul
      ((continuous_apply i).comp (continuous_cen.comp continuous_snd))).add
      continuous_const).div_const 2

/-! ### `Rmap` retracts `Smap` -/

theorem rScale_Smap (z : I × (I^ Fin k)) : rScale (Smap z) = 2 - (z.1 : ℝ) := by
  have h1 : ((Smap z).1 : ℝ) = (z.1 : ℝ) + tfun (dir z) - 2 := rfl
  rw [rScale, cen_Smap_snd, h1,
    max_eq_right (by linarith [one_le_two_sub z.1] :
      (1:ℝ) ≤ tfun (dir z) - ((z.1 : ℝ) + tfun (dir z) - 2))]
  ring

theorem Rmap_Smap (z : I × (I^ Fin k)) : Rmap (Smap z) = z := by
  refine Prod.ext ?_ ?_
  · exact Subtype.ext (by simp only [Rmap, rScale_Smap]; ring)
  · funext i
    refine Subtype.ext ?_
    have hd : dir z i = cen z.2 i / (2 - (z.1 : ℝ)) := by
      simp only [dir, Pi.smul_apply, smul_eq_mul]; ring
    simp only [Rmap, rScale_Smap, cen_Smap_snd, hd]
    rw [mul_div_cancel₀ _ (two_sub_pos z.1).ne']
    simp only [cen]
    ring

/-! ### The jar -/

/-- The jar of the cylinder `I × I^k`: the bottom face together with the sides. -/
def jarSet (k : ℕ) : Set (I × (I^ Fin k)) := {z | z.1 = 0 ∨ z.2 ∈ (∂I^k)}

theorem tfun_dir_of_mem_jar {z : I × (I^ Fin k)} (hz : z ∈ jarSet k) :
    tfun (dir z) = 2 - (z.1 : ℝ) := by
  rcases hz with hz | hz
  · have hz' : (z.1 : ℝ) = 0 := Set.Icc.coe_eq_zero.2 hz
    rw [tfun_eq_two, hz']
    · ring
    · rw [norm_dir, hz', div_le_iff₀ (by norm_num)]
      linarith [norm_cen_le_one z.2]
  · have hn : ‖cen z.2‖ = 1 := (mem_boundary_iff_norm_cen z.2).1 hz
    have hdn : ‖dir z‖ = (2 - (z.1 : ℝ))⁻¹ := by
      rw [norm_dir, hn, inv_eq_one_div]
    rw [tfun, mfun, hdn, max_eq_left (inv_two_le_inv_two_sub z.1), inv_inv]

theorem Smap_mem_bot {z : I × (I^ Fin k)} (hz : z ∈ jarSet k) : (Smap z).1 = 0 := by
  refine Set.Icc.coe_eq_zero.1 ?_
  show (z.1 : ℝ) + tfun (dir z) - 2 = 0
  rw [tfun_dir_of_mem_jar hz]
  ring

theorem cen_Rmap_snd (z : I × (I^ Fin k)) : cen (Rmap z).2 = rScale z • cen z.2 := by
  funext i
  simp only [cen, Rmap, Pi.smul_apply, smul_eq_mul]
  ring

theorem Rmap_mem_jar {z : I × (I^ Fin k)} (hz : z.1 = 0) : Rmap z ∈ jarSet k := by
  have hz' : (z.1 : ℝ) = 0 := Set.Icc.coe_eq_zero.2 hz
  have hscale : rScale z = tfun (cen z.2) := by
    simp only [rScale, hz', sub_zero]
    exact max_eq_right (one_le_tfun (norm_cen_le_one z.2))
  by_cases hn : ‖cen z.2‖ ≤ 2⁻¹
  · refine Or.inl (Set.Icc.coe_eq_zero.1 ?_)
    show 2 - rScale z = 0
    rw [hscale, tfun_eq_two hn]
    ring
  · refine Or.inr ((mem_boundary_iff_norm_cen _).2 ?_)
    rw [cen_Rmap_snd, norm_smul, Real.norm_eq_abs, abs_of_pos (rScale_pos z), hscale]
    exact tfun_mul_norm_eq_one (not_le.1 hn).le

end CubeJar

/-! ### Lifting along the jar inclusion -/

section Jar

open CubeJar

variable {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]

/-- The inclusion of the jar of the cylinder `I × I^k`. -/
def jarIncl (k : ℕ) : C(jarSet k, I × (I^ Fin k)) := ⟨Subtype.val, continuous_subtype_val⟩

/-- A Serre fibration has the lifting property along the jar inclusion
`{0} × I^k ∪ I × ∂I^k ↪ I × I^k`. -/
theorem IsSerreFibration.hasRLPAlong_jarIncl {p : C(E, B)} (hp : IsSerreFibration p) (k : ℕ) :
    HasRLPAlong p (jarIncl k) := by
  refine HasRLPAlong.of_retract (p := p) (ι := jarIncl k) (ι' := botIncl (I^ Fin k))
    (S := ⟨Smap, continuous_Smap⟩) (R := ⟨Rmap, continuous_Rmap⟩)
    (s := ⟨fun a => (Smap a.1).2,
      continuous_snd.comp (continuous_Smap.comp continuous_subtype_val)⟩)
    (r := ⟨fun a => ⟨Rmap (0, a), Rmap_mem_jar rfl⟩,
      (continuous_Rmap.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩)
    (fun a => ?_) (fun _ => rfl) Rmap_Smap (fun a => ?_)
    ((hp k).hasRLPAlong_botIncl)
  · show Smap a.1 = ((0 : I), (Smap a.1).2)
    exact Prod.ext (Smap_mem_bot a.2) rfl
  refine Subtype.ext ?_
  show Rmap (0, (Smap a.1).2) = a.1
  rw [show ((0 : I), (Smap a.1).2) = Smap a.1 from Prod.ext (Smap_mem_bot a.2).symm rfl]
  exact Rmap_Smap a.1

end Jar

/-! ### Lifting along the boundary-jar inclusion of the cube -/

section BoundaryJar

variable {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]

/-- Under `Cube.splitAtLast`, the boundary jar of the cube is the jar of the cylinder. -/
theorem mem_jarSet_splitAtLast {k : ℕ} {y : I^ Fin (k + 1)} :
    Cube.splitAtLast y ∈ CubeJar.jarSet k ↔ y ∈ (⊔I^(k+1)) :=
  Cube.mem_boundaryJar_iff_splitAtLast.symm

theorem splitAtLast_symm_mem_boundaryJar {k : ℕ} (a : CubeJar.jarSet k) :
    Cube.splitAtLast.symm a.1 ∈ (⊔I^(k+1)) := by
  have h := a.2
  rwa [← mem_jarSet_splitAtLast, Homeomorph.apply_symm_apply]

/-- A Serre fibration has the lifting property along `⊔I^(k+1) ↪ I^(k+1)`. -/
theorem IsSerreFibration.hasRLPAlong_boundaryJarIncl {p : C(E, B)} (hp : IsSerreFibration p)
    (k : ℕ) : HasRLPAlong p (Cube.boundaryJarIncl (k + 1)) := by
  exact HasRLPAlong.of_retract (p := p) (ι := Cube.boundaryJarIncl (k + 1)) (ι' := jarIncl k)
    (S := ⟨Cube.splitAtLast, Cube.splitAtLast.continuous⟩)
    (R := ⟨Cube.splitAtLast.symm, Cube.splitAtLast.symm.continuous⟩)
    (s := ⟨fun a => ⟨Cube.splitAtLast a.1, mem_jarSet_splitAtLast.2 a.2⟩,
      (Cube.splitAtLast.continuous.comp continuous_subtype_val).subtype_mk
        fun a => mem_jarSet_splitAtLast.2 a.2⟩)
    (r := ⟨fun a => ⟨Cube.splitAtLast.symm a.1, splitAtLast_symm_mem_boundaryJar a⟩,
      (Cube.splitAtLast.symm.continuous.comp continuous_subtype_val).subtype_mk
        splitAtLast_symm_mem_boundaryJar⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun x => Cube.splitAtLast.symm_apply_apply x)
    (fun a => Subtype.ext (Cube.splitAtLast.symm_apply_apply a.1))
    (hp.hasRLPAlong_jarIncl k)

end BoundaryJar

/-! ### Lifting along the homotopy jar -/

section HomotopyJar

variable {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]

/-- Membership in the boundary of a cube, in terms of splitting off the last coordinate. -/
theorem mem_boundary_iff_splitAtLast {m : ℕ} {y : I^ Fin (m + 1)} :
    y ∈ (∂I^(m+1)) ↔ (Cube.splitAtLast y).1 = 0 ∨ (Cube.splitAtLast y).1 = 1 ∨
      (Cube.splitAtLast y).2 ∈ (∂I^m) := by
  rw [Cube.splitAtLast_fst_eq]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · rw [← Cube.splitAtLast_snd_apply_eq y j] at hi
      exact Or.inr (Or.inr ⟨j, hi⟩)
    · rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨j, hj⟩)
    · exact ⟨Fin.last m, Or.inl h⟩
    · exact ⟨Fin.last m, Or.inr h⟩
    · rw [Cube.splitAtLast_snd_apply_eq] at hj
      exact ⟨j.castSucc, hj⟩

/-- The "homotopy jar" inside `I × I^(k+1)`: the two ends of the cylinder together with the
boundary jar of the cube. -/
def homotopyJarSet (k : ℕ) : Set (I × (I^ Fin (k + 1))) :=
  {z | z.2 ∈ (⊔I^(k+1)) ∨ z.1 = 0 ∨ z.1 = 1}

/-- The inclusion of the homotopy jar. -/
def homotopyJarIncl (k : ℕ) : C(homotopyJarSet k, I × (I^ Fin (k + 1))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The involution of `I × I^(k+1)` that exchanges the homotopy parameter with the last
coordinate of the cube. -/
def swapLast (k : ℕ) : (I × (I^ Fin (k + 1))) ≃ₜ (I × (I^ Fin (k + 1))) where
  toFun z := ((Cube.splitAtLast z.2).1, Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2))
  invFun z := ((Cube.splitAtLast z.2).1, Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2))
  left_inv z := by
    have h : Cube.splitAtLast (Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2))
        = (z.1, (Cube.splitAtLast z.2).2) := Cube.splitAtLast.apply_symm_apply _
    simp only [h]
    exact Prod.ext rfl (Cube.splitAtLast.symm_apply_apply z.2)
  right_inv z := by
    have h : Cube.splitAtLast (Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2))
        = (z.1, (Cube.splitAtLast z.2).2) := Cube.splitAtLast.apply_symm_apply _
    simp only [h]
    exact Prod.ext rfl (Cube.splitAtLast.symm_apply_apply z.2)
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (Cube.splitAtLast.continuous.comp continuous_snd)
    · exact Cube.splitAtLast.symm.continuous.comp (continuous_fst.prodMk
        (continuous_snd.comp (Cube.splitAtLast.continuous.comp continuous_snd)))
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (Cube.splitAtLast.continuous.comp continuous_snd)
    · exact Cube.splitAtLast.symm.continuous.comp (continuous_fst.prodMk
        (continuous_snd.comp (Cube.splitAtLast.continuous.comp continuous_snd)))

@[simp]
theorem swapLast_apply {k : ℕ} (z : I × (I^ Fin (k + 1))) :
    swapLast k z =
      ((Cube.splitAtLast z.2).1, Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2)) := rfl

theorem mem_jarSet_swapLast {k : ℕ} {z : I × (I^ Fin (k + 1))} :
    swapLast k z ∈ CubeJar.jarSet (k + 1) ↔ z ∈ homotopyJarSet k := by
  have h : Cube.splitAtLast (Cube.splitAtLast.symm (z.1, (Cube.splitAtLast z.2).2))
      = (z.1, (Cube.splitAtLast z.2).2) := Cube.splitAtLast.apply_symm_apply _
  show (swapLast k z).1 = 0 ∨ (swapLast k z).2 ∈ (∂I^(k+1)) ↔ _
  rw [swapLast_apply, mem_boundary_iff_splitAtLast, h]
  show _ ↔ (z.2 ∈ (⊔I^(k+1)) ∨ _)
  rw [Cube.mem_boundaryJar_iff_splitAtLast]
  tauto

theorem swapLast_symm_mem_homotopyJar {k : ℕ} (a : CubeJar.jarSet (k + 1)) :
    (swapLast k).symm a.1 ∈ homotopyJarSet k := by
  have h := a.2
  rwa [← mem_jarSet_swapLast, Homeomorph.apply_symm_apply]

/-- A Serre fibration has the lifting property along the homotopy jar inclusion. -/
theorem IsSerreFibration.hasRLPAlong_homotopyJarIncl {p : C(E, B)} (hp : IsSerreFibration p)
    (k : ℕ) : HasRLPAlong p (homotopyJarIncl k) := by
  exact HasRLPAlong.of_retract (p := p) (ι := homotopyJarIncl k) (ι' := jarIncl (k + 1))
    (S := ⟨swapLast k, (swapLast k).continuous⟩)
    (R := ⟨(swapLast k).symm, (swapLast k).symm.continuous⟩)
    (s := ⟨fun a => ⟨swapLast k a.1, mem_jarSet_swapLast.2 a.2⟩,
      ((swapLast k).continuous.comp continuous_subtype_val).subtype_mk
        fun a => mem_jarSet_swapLast.2 a.2⟩)
    (r := ⟨fun a => ⟨(swapLast k).symm a.1, swapLast_symm_mem_homotopyJar a⟩,
      ((swapLast k).symm.continuous.comp continuous_subtype_val).subtype_mk
        swapLast_symm_mem_homotopyJar⟩)
    (fun _ => rfl) (fun _ => rfl)
    (fun x => (swapLast k).symm_apply_apply x)
    (fun a => Subtype.ext ((swapLast k).symm_apply_apply a.1))
    (hp.hasRLPAlong_jarIncl (k + 1))

end HomotopyJar

end Submission
