/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Path
import Submission.Model.SuspSphere

/-!
# Explicit contraction data

The Wang sequence is obtained from Mayer–Vietoris applied to `E = p⁻¹(D₊) ∪ p⁻¹(D₋)` for a
fibration `p : E → Sᵐ`. Identifying `p⁻¹(D±)` with the fibre requires a *fibre-homotopy*
trivialisation of `p` over `D±`. In general this is Dold's theorem, but for the path fibrations we
apply Wang to, the trivialisation is completely explicit as soon as one is given a **continuous
family of paths contracting `D±` to a point**. This file introduces that datum and constructs it
for the two enlarged hemispheres of a sphere.

## Main definitions

* `Submission.ContractionData T t₀` — a continuous family of paths in `T` from `t₀` to every point,
  constant at `t₀`;
* `Submission.sphCap m ε h` — the closed spherical cap `{z ∈ S^{m+1} | -h ≤ ε * z_last}`;
* `Submission.sphLowerCap m`, `Submission.sphUpperCap m` — the two enlarged hemispheres, i.e. the
  caps `{z_last ≤ 1/3}` and `{-1/3 ≤ z_last}`;
* `Submission.capContraction` — the meridian contraction of a cap onto its pole;
* `Submission.sphBelt m` — the intersection of the two enlarged hemispheres.

## Main results

* `Submission.ContractionData.contractibleSpace` — a space carrying contraction data is
  contractible;
* `Submission.sphLowerCap_eq_image`, `Submission.sphUpperCap_eq_image` — the enlarged hemispheres
  are the images under `suspSphHomeo` of `{height ≤ 2/3}` and `{1/3 ≤ height}`;
* `Submission.sphBeltHomeo` — the intersection of the two enlarged hemispheres is homeomorphic to
  `Sph m × [-1/3, 1/3]`;
* `Submission.sphBeltHomotopyEquiv` — hence homotopy equivalent to `Sph m`.

The contraction of a cap uses the *meridian* formula: writing a point of `S^{m+1}` as `(y, a)` with
`‖y‖² + a² = 1`, the path from the pole `(0, ε)` to `(y, a)` is
`s ↦ (√(s (2 - s r) / (1 + ε a)) • y, ε (1 - s r))`, where `r = 1 - ε a`.
The point of this parametrisation is that the scalar in front of `y` involves no division by a
quantity that vanishes on the cap, so the family is jointly continuous, while the norm identity
`s (2 - s r) r + (1 - s r)² = 1` is an exact algebraic identity.
-/

namespace Submission

open unitInterval

universe u v

/-- A continuous contraction of a based space `(T, t₀)`: a continuous family of paths from `t₀` to
every point of `T`, which at `t₀` is the constant path.

For a subspace `D ⊆ X` with base point `b₀ : D` this is `ContractionData ↥D b₀`, i.e. a continuous
family of paths *inside `D`* from `b₀` to each point of `D`. -/
structure ContractionData (T : Type u) [TopologicalSpace T] (t₀ : T) where
  /-- The path from the base point `t₀` to the point `t`. -/
  path : ∀ t : T, Path t₀ t
  /-- The family of paths is jointly continuous. -/
  continuous_uncurry : Continuous fun p : T × I => path p.1 p.2
  /-- At the base point the path is constant. -/
  path_base : path t₀ = Path.refl t₀

namespace ContractionData

variable {T : Type u} [TopologicalSpace T] {t₀ : T}

/-- The contraction bundled as a single continuous map `T × I → T`. -/
def curve (c : ContractionData T t₀) : C(T × I, T) :=
  ⟨fun p => c.path p.1 p.2, c.continuous_uncurry⟩

@[simp] theorem curve_apply (c : ContractionData T t₀) (t : T) (s : I) :
    c.curve (t, s) = c.path t s := rfl

@[simp] theorem curve_zero (c : ContractionData T t₀) (t : T) : c.curve (t, 0) = t₀ :=
  (c.path t).source

@[simp] theorem curve_one (c : ContractionData T t₀) (t : T) : c.curve (t, 1) = t :=
  (c.path t).target

@[simp] theorem curve_base (c : ContractionData T t₀) (s : I) : c.curve (t₀, s) = t₀ := by
  rw [curve_apply, c.path_base]; rfl

/-- A space carrying contraction data is contractible. -/
theorem contractibleSpace (c : ContractionData T t₀) : ContractibleSpace T := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨t₀, ⟨⟨⟨fun p => c.curve (p.2, σ p.1), c.curve.continuous.comp
    (continuous_snd.prodMk (continuous_symm.comp continuous_fst))⟩, fun t => ?_, fun t => ?_⟩⟩⟩
  · simp
  · simp

end ContractionData

/-! ### Products with a contractible factor -/

/-- If `Y` is contractible then `X × Y` is homotopy equivalent to `X`. -/
noncomputable def prodHomotopyEquivOfContractible (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace Y] : ContinuousMap.HomotopyEquiv (X × Y) X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (ContractibleSpace.hequiv_unit Y).some).trans (Homeomorph.prodUnique X Unit).toHomotopyEquiv

/-! ### Coordinates on a sphere -/

section Sphere

open Metric

variable {m : ℕ}

/-- The last coordinate ("height") of a point of `S^{m+1}`. -/
def sphHeight (z : Sph (m + 1)) : ℝ := (z : EuclideanSpace ℝ (Fin (m + 2))) (Fin.last (m + 1))

theorem continuous_sphHeight : Continuous (sphHeight (m := m)) :=
  (PiLp.continuous_apply 2 (fun _ : Fin (m + 2) => ℝ) (Fin.last (m + 1))).comp
    continuous_subtype_val

/-- The equatorial component of a point of `S^{m+1}`: its first `m + 1` coordinates. -/
def sphEquator (z : Sph (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 fun i => (z : EuclideanSpace ℝ (Fin (m + 2))) i.castSucc

theorem continuous_sphEquator : Continuous (sphEquator (m := m)) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp (continuous_pi fun i => ?_)
  exact (PiLp.continuous_apply 2 (fun _ : Fin (m + 2) => ℝ) i.castSucc).comp continuous_subtype_val

theorem snocLp_sphEquator_sphHeight (z : Sph (m + 1)) :
    snocLp (sphEquator z) (sphHeight z) = (z : EuclideanSpace ℝ (Fin (m + 2))) :=
  (eq_snocLp _).symm

theorem norm_sphEquator_sq (z : Sph (m + 1)) : ‖sphEquator z‖ ^ 2 = 1 - sphHeight z ^ 2 := by
  have hz : ‖(z : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have h := norm_snocLp_sq (sphEquator z) (sphHeight z)
  rw [snocLp_sphEquator_sphHeight, hz, one_pow] at h
  linarith

theorem sphHeight_sq_le_one (z : Sph (m + 1)) : sphHeight z ^ 2 ≤ 1 := by
  nlinarith [norm_sphEquator_sq z, sq_nonneg ‖sphEquator z‖]

/-! ### Spherical caps -/

/-- The closed spherical cap `{z ∈ S^{m+1} | -h ≤ ε * z_last}`. For `ε = 1` this is the region of
height at least `-h`, for `ε = -1` the region of height at most `h`. -/
def sphCap (m : ℕ) (ε h : ℝ) : Set (Sph (m + 1)) := {z | -h ≤ ε * sphHeight z}

theorem mem_sphCap {ε h : ℝ} {z : Sph (m + 1)} : z ∈ sphCap m ε h ↔ -h ≤ ε * sphHeight z := Iff.rfl

theorem zero_lt_one_add_of_mem_sphCap {ε h : ℝ} (hh1 : h < 1) {z : Sph (m + 1)}
    (hz : z ∈ sphCap m ε h) : 0 < 1 + ε * sphHeight z := by
  rw [mem_sphCap] at hz; linarith

/-- The pole `(0, …, 0, ε)` of `S^{m+1}`, for `ε = ±1`. -/
noncomputable def sphPole (m : ℕ) (ε : ℝ) (hε : ε ^ 2 = 1) : Sph (m + 1) :=
  ⟨snocLp 0 ε, mem_sphere_zero_iff_norm.mpr (norm_eq_one_of_norm_sq_eq_one (by
    rw [norm_snocLp_sq, norm_zero, hε]; norm_num))⟩

@[simp] theorem sphHeight_sphPole (ε : ℝ) (hε : ε ^ 2 = 1) :
    sphHeight (sphPole m ε hε) = ε := snocLp_last 0 ε

@[simp] theorem sphEquator_sphPole (ε : ℝ) (hε : ε ^ 2 = 1) :
    sphEquator (sphPole m ε hε) = 0 :=
  PiLp.ext fun i => by simp [sphEquator, sphPole]

/-! ### The meridian contraction of a cap -/

/-- The point at parameter `s` on the meridian from the pole `(0, ε)` to `z`. -/
noncomputable def capPathFun (ε : ℝ) (z : Sph (m + 1)) (s : ℝ) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  snocLp (Real.sqrt (s * (2 - s * (1 - ε * sphHeight z)) / (1 + ε * sphHeight z)) • sphEquator z)
    (ε * (1 - s * (1 - ε * sphHeight z)))

@[simp] theorem capPathFun_zero (ε : ℝ) (z : Sph (m + 1)) : capPathFun ε z 0 = snocLp 0 ε := by
  simp [capPathFun]

theorem capPathFun_last (ε : ℝ) (z : Sph (m + 1)) (s : ℝ) :
    capPathFun ε z s (Fin.last (m + 1)) = ε * (1 - s * (1 - ε * sphHeight z)) :=
  snocLp_last _ _

/-- On the sphere the quantity `1 - ε * z_last` is nonnegative when `ε = ±1`. -/
theorem one_sub_mul_sphHeight_nonneg {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1)) :
    0 ≤ 1 - ε * sphHeight z := by
  nlinarith [sphHeight_sq_le_one z, sq_nonneg (ε - sphHeight z), sq_nonneg (ε + sphHeight z)]

theorem capPathFun_one {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1))
    (hz : 0 < 1 + ε * sphHeight z) : capPathFun ε z 1 = (z : EuclideanSpace ℝ (Fin (m + 2))) := by
  have h1 : (1 : ℝ) * (2 - 1 * (1 - ε * sphHeight z)) / (1 + ε * sphHeight z) = 1 := by
    rw [show (1 : ℝ) * (2 - 1 * (1 - ε * sphHeight z)) = 1 + ε * sphHeight z by ring]
    exact div_self (ne_of_gt hz)
  have h2 : ε * (1 - 1 * (1 - ε * sphHeight z)) = sphHeight z := by
    linear_combination sphHeight z * hε
  rw [capPathFun, h1, h2, Real.sqrt_one, one_smul, snocLp_sphEquator_sphHeight]

theorem norm_capPathFun {ε : ℝ} (hε : ε ^ 2 = 1) (z : Sph (m + 1))
    (hz : 0 < 1 + ε * sphHeight z) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖capPathFun ε z s‖ = 1 := by
  set a := sphHeight z with ha
  set r := 1 - ε * a with hr
  have hr0 : 0 ≤ r := one_sub_mul_sphHeight_nonneg hε z
  have hsr : s * r ≤ r := by nlinarith
  have harg : 0 ≤ s * (2 - s * r) / (1 + ε * a) := by
    apply div_nonneg _ hz.le
    have h2 : 2 - s * r ≥ 1 + ε * a := by simp only [hr] at hsr ⊢; linarith
    nlinarith
  refine norm_eq_one_of_norm_sq_eq_one ?_
  rw [capPathFun, ← ha, ← hr, norm_snocLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt harg, norm_sphEquator_sq, ← ha]
  have hfac : (1 : ℝ) - a ^ 2 = r * (1 + ε * a) := by
    rw [hr]; linear_combination a ^ 2 * hε
  rw [hfac]
  field_simp
  nlinarith [hε]

theorem capPathFun_mem_sphCap {ε h : ℝ} (hε : ε ^ 2 = 1) {z : Sph (m + 1)}
    (hzc : z ∈ sphCap m ε h) {s : ℝ} (hs1 : s ≤ 1) :
    -h ≤ ε * (capPathFun ε z s (Fin.last (m + 1))) := by
  have hr0 : 0 ≤ 1 - ε * sphHeight z := one_sub_mul_sphHeight_nonneg hε z
  have hsr : s * (1 - ε * sphHeight z) ≤ 1 - ε * sphHeight z := by nlinarith [hr0, hs1]
  have hzc' : -h ≤ ε * sphHeight z := hzc
  have key : ε * (ε * (1 - s * (1 - ε * sphHeight z))) = 1 - s * (1 - ε * sphHeight z) := by
    linear_combination (1 - s * (1 - ε * sphHeight z)) * hε
  rw [capPathFun_last, key]
  linarith

theorem continuous_capPathFun {ε : ℝ} {D : Set (Sph (m + 1))}
    (hD : ∀ z : ↥D, 0 < 1 + ε * sphHeight z.1) :
    Continuous fun p : ↥D × I => capPathFun ε p.1.1 (p.2 : ℝ) := by
  have hgt : Continuous fun p : ↥D × I => sphHeight p.1.1 :=
    continuous_sphHeight.comp (continuous_subtype_val.comp continuous_fst)
  have hs : Continuous fun p : ↥D × I => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  have hy : Continuous fun p : ↥D × I => sphEquator p.1.1 :=
    continuous_sphEquator.comp (continuous_subtype_val.comp continuous_fst)
  have hr : Continuous fun p : ↥D × I => 1 - ε * sphHeight p.1.1 :=
    continuous_const.sub (continuous_const.mul hgt)
  have hnum : Continuous fun p : ↥D × I =>
      (p.2 : ℝ) * (2 - (p.2 : ℝ) * (1 - ε * sphHeight p.1.1)) :=
    hs.mul (continuous_const.sub (hs.mul hr))
  have hden : Continuous fun p : ↥D × I => 1 + ε * sphHeight p.1.1 :=
    continuous_const.add (continuous_const.mul hgt)
  have hsqrt : Continuous fun p : ↥D × I => Real.sqrt
      ((p.2 : ℝ) * (2 - (p.2 : ℝ) * (1 - ε * sphHeight p.1.1)) / (1 + ε * sphHeight p.1.1)) :=
    Real.continuous_sqrt.comp (hnum.div hden fun p => ne_of_gt (hD p.1))
  exact continuous_snocLp.comp ((hsqrt.smul hy).prodMk
    (continuous_const.mul (continuous_const.sub (hs.mul hr))))

variable (m) in
/-- The pole of the cap `sphCap m ε h`, as a point of that cap. -/
noncomputable def capPole (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) : ↥(sphCap m ε h) :=
  ⟨sphPole m ε hε, by rw [mem_sphCap, sphHeight_sphPole, ← pow_two, hε]; linarith⟩

/-- The meridian path inside the cap `sphCap m ε h` from the pole to the point `z`. -/
noncomputable def capPath (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) (hh1 : h < 1)
    (z : ↥(sphCap m ε h)) : Path (capPole m ε h hε hh) z where
  toFun s :=
    ⟨⟨capPathFun ε z.1 s, mem_sphere_zero_iff_norm.mpr (norm_capPathFun hε z.1
        (zero_lt_one_add_of_mem_sphCap hh1 z.2) s.2.1 s.2.2)⟩,
      capPathFun_mem_sphCap hε z.2 s.2.2⟩
  continuous_toFun := by
    have hcont : Continuous fun s : I => capPathFun ε z.1 (s : ℝ) :=
      (continuous_capPathFun
          (fun w : ↥(sphCap m ε h) => zero_lt_one_add_of_mem_sphCap hh1 w.2)).comp
        (Continuous.prodMk (continuous_const : Continuous fun _ : I => z) continuous_id)
    exact (hcont.subtype_mk _).subtype_mk _
  source' := Subtype.ext (Subtype.ext (by
    show capPathFun ε z.1 ((0 : I) : ℝ) = snocLp 0 ε
    rw [Set.Icc.coe_zero, capPathFun_zero]))
  target' := Subtype.ext (Subtype.ext (by
    show capPathFun ε z.1 ((1 : I) : ℝ) = (z.1 : EuclideanSpace ℝ (Fin (m + 2)))
    rw [Set.Icc.coe_one]
    exact capPathFun_one hε z.1 (zero_lt_one_add_of_mem_sphCap hh1 z.2)))

/-- **The meridian contraction of a spherical cap onto its pole.** -/
noncomputable def capContraction (ε h : ℝ) (hε : ε ^ 2 = 1) (hh : -1 ≤ h) (hh1 : h < 1) :
    ContractionData ↥(sphCap m ε h) (capPole m ε h hε hh) where
  path z := capPath ε h hε hh hh1 z
  continuous_uncurry :=
    (((continuous_capPathFun
      (fun w : ↥(sphCap m ε h) => zero_lt_one_add_of_mem_sphCap hh1 w.2)).subtype_mk
        _).subtype_mk _)
  path_base := by
    refine Path.ext (funext fun s => Subtype.ext (Subtype.ext ?_))
    show capPathFun ε (sphPole m ε hε) (s : ℝ) = snocLp 0 ε
    rw [capPathFun, sphEquator_sphPole, smul_zero, sphHeight_sphPole, ← pow_two, hε]
    norm_num

/-! ### The two enlarged hemispheres -/

variable (m) in
/-- The enlarged lower hemisphere `{z ∈ S^{m+1} | z_last ≤ 1/3}`. -/
def sphLowerCap : Set (Sph (m + 1)) := sphCap m (-1) (1 / 3)

variable (m) in
/-- The enlarged upper hemisphere `{z ∈ S^{m+1} | -1/3 ≤ z_last}`. -/
def sphUpperCap : Set (Sph (m + 1)) := sphCap m 1 (1 / 3)

theorem mem_sphLowerCap {z : Sph (m + 1)} : z ∈ sphLowerCap m ↔ sphHeight z ≤ 1 / 3 := by
  rw [sphLowerCap, mem_sphCap]; constructor <;> intro h <;> linarith

theorem mem_sphUpperCap {z : Sph (m + 1)} : z ∈ sphUpperCap m ↔ -(1 / 3) ≤ sphHeight z := by
  rw [sphUpperCap, mem_sphCap]; constructor <;> intro h <;> linarith

variable (m) in
/-- **The contraction of the enlarged lower hemisphere onto the south pole.** -/
noncomputable def sphLowerCapContraction :
    ContractionData ↥(sphLowerCap m) (capPole m (-1) (1 / 3) (by norm_num) (by norm_num)) :=
  capContraction (-1) (1 / 3) (by norm_num) (by norm_num) (by norm_num)

variable (m) in
/-- **The contraction of the enlarged upper hemisphere onto the north pole.** -/
noncomputable def sphUpperCapContraction :
    ContractionData ↥(sphUpperCap m) (capPole m 1 (1 / 3) (by norm_num) (by norm_num)) :=
  capContraction 1 (1 / 3) (by norm_num) (by norm_num) (by norm_num)

/-! ### The two enlarged hemispheres cover the sphere -/

instance instContractibleSpaceSphLowerCap (m : ℕ) : ContractibleSpace (sphLowerCap m) :=
  (sphLowerCapContraction m).contractibleSpace

instance instContractibleSpaceSphUpperCap (m : ℕ) : ContractibleSpace (sphUpperCap m) :=
  (sphUpperCapContraction m).contractibleSpace

variable (m) in
/-- The part of `S^{m+1}` strictly below a given height is open. -/
theorem isOpen_sphHeight_lt (c : ℝ) : IsOpen {z : Sph (m + 1) | sphHeight z < c} :=
  isOpen_lt continuous_sphHeight continuous_const

variable (m) in
/-- The part of `S^{m+1}` strictly above a given height is open. -/
theorem isOpen_lt_sphHeight (c : ℝ) : IsOpen {z : Sph (m + 1) | c < sphHeight z} :=
  isOpen_lt continuous_const continuous_sphHeight

variable (m) in
/-- The interiors of the two enlarged hemispheres cover `S^{m+1}`. -/
theorem sphCap_interior_union :
    interior (sphLowerCap m) ∪ interior (sphUpperCap m) = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases hz : sphHeight z < 1 / 3
  · refine Or.inl ((isOpen_sphHeight_lt m (1 / 3)).subset_interior_iff.2 ?_ hz)
    intro w hw
    exact mem_sphLowerCap.2 (le_of_lt hw)
  · refine Or.inr ((isOpen_lt_sphHeight m (-(1 / 3))).subset_interior_iff.2 ?_ ?_)
    · intro w hw
      exact mem_sphUpperCap.2 (le_of_lt hw)
    · simp only [Set.mem_setOf_eq]
      rw [not_lt] at hz
      linarith

/-! ### Comparison with the suspension picture -/

theorem sphHeight_suspSphLift (q : Susp (Sph m)) :
    sphHeight (suspSphLift m q) = 2 * (Susp.height q : ℝ) - 1 := by
  induction q using Susp.ind with
  | h p => exact snocLp_last _ _

theorem sphHeight_eq (z : Sph (m + 1)) :
    sphHeight z = 2 * (Susp.height ((suspSphHomeo m).symm z) : ℝ) - 1 := by
  rw [← sphHeight_suspSphLift, ← suspSphHomeo_apply, Homeomorph.apply_symm_apply]

theorem sphLowerCap_eq_image :
    sphLowerCap m = suspSphHomeo m '' {q : Susp (Sph m) | (Susp.height q : ℝ) ≤ 2 / 3} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_sphLowerCap]
  constructor
  · intro hz
    refine ⟨(suspSphHomeo m).symm z, ?_, (suspSphHomeo m).apply_symm_apply z⟩
    rw [sphHeight_eq] at hz
    linarith
  · rintro ⟨q, hq, rfl⟩
    rw [suspSphHomeo_apply, sphHeight_suspSphLift]
    linarith

theorem sphUpperCap_eq_image :
    sphUpperCap m = suspSphHomeo m '' {q : Susp (Sph m) | (1 : ℝ) / 3 ≤ Susp.height q} := by
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_sphUpperCap]
  constructor
  · intro hz
    refine ⟨(suspSphHomeo m).symm z, ?_, (suspSphHomeo m).apply_symm_apply z⟩
    rw [sphHeight_eq] at hz
    linarith
  · rintro ⟨q, hq, rfl⟩
    rw [suspSphHomeo_apply, sphHeight_suspSphLift]
    linarith

/-! ### The intersection of the two hemispheres -/

variable (m) in
/-- The intersection of the two enlarged hemispheres: the belt `{|z_last| ≤ 1/3}`. -/
def sphBelt : Set (Sph (m + 1)) := sphLowerCap m ∩ sphUpperCap m

theorem mem_sphBelt {z : Sph (m + 1)} :
    z ∈ sphBelt m ↔ -(1 / 3) ≤ sphHeight z ∧ sphHeight z ≤ 1 / 3 := by
  rw [sphBelt, Set.mem_inter_iff, mem_sphLowerCap, mem_sphUpperCap, and_comm]

/-- The vector attached to a pair `(x, a) ∈ Sph m × [-1/3, 1/3]`, namely `(√(1 - a²) x, a)`. -/
noncomputable def beltVec (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :
    EuclideanSpace ℝ (Fin (m + 2)) :=
  snocLp (Real.sqrt (1 - (p.2 : ℝ) ^ 2) • (p.1 : EuclideanSpace ℝ (Fin (m + 1)))) (p.2 : ℝ)

theorem beltVec_last (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :
    beltVec p (Fin.last (m + 1)) = (p.2 : ℝ) := snocLp_last _ _

theorem norm_beltVec (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) : ‖beltVec p‖ = 1 := by
  have hx : ‖(p.1 : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
  have hnn : (0 : ℝ) ≤ 1 - (p.2 : ℝ) ^ 2 := by nlinarith [h2.1, h2.2]
  refine norm_eq_one_of_norm_sq_eq_one ?_
  rw [beltVec, norm_snocLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hnn, hx]
  ring

/-- The parametrisation of the belt by `Sph m × [-1/3, 1/3]`. -/
noncomputable def beltOfProd (p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3)) : ↥(sphBelt m) :=
  ⟨⟨beltVec p, mem_sphere_zero_iff_norm.mpr (norm_beltVec p)⟩, by
    have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
    rw [mem_sphBelt]
    show -(1 / 3) ≤ beltVec p (Fin.last (m + 1)) ∧ beltVec p (Fin.last (m + 1)) ≤ 1 / 3
    rw [beltVec_last]
    exact h2⟩

theorem continuous_beltOfProd : Continuous (beltOfProd (m := m)) := by
  have hx : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) =>
      (p.1 : EuclideanSpace ℝ (Fin (m + 1))) := continuous_subtype_val.comp continuous_fst
  have ha : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hsqrt : Continuous fun p : Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) =>
      Real.sqrt (1 - (p.2 : ℝ) ^ 2) :=
    Real.continuous_sqrt.comp (continuous_const.sub (ha.pow 2))
  exact ((continuous_snocLp.comp ((hsqrt.smul hx).prodMk ha)).subtype_mk _).subtype_mk _

theorem beltOfProd_bijective : Function.Bijective (beltOfProd (m := m)) := by
  constructor
  · intro p q hpq
    have hpq' : beltVec p = beltVec q := congrArg (fun w : ↥(sphBelt m) => w.1.1) hpq
    obtain ⟨hv, hc⟩ := snocLp_eq_iff.mp hpq'
    have h2 : -(1 / 3) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1 / 3 := Set.mem_Icc.mp p.2.2
    have hpos : (0 : ℝ) < Real.sqrt (1 - (p.2 : ℝ) ^ 2) := by
      apply Real.sqrt_pos.mpr; nlinarith [h2.1, h2.2]
    rw [hc] at hv hpos
    exact Prod.ext (Subtype.ext (smul_right_injective _ (ne_of_gt hpos) hv)) (Subtype.ext hc)
  · rintro ⟨z, hz⟩
    rw [mem_sphBelt] at hz
    have hnorm : ‖sphEquator z‖ ^ 2 = 1 - sphHeight z ^ 2 := norm_sphEquator_sq z
    have hpos : (0 : ℝ) < 1 - sphHeight z ^ 2 := by nlinarith [hz.1, hz.2]
    have hne : ‖sphEquator z‖ ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      nlinarith
    have hx : ‖‖sphEquator z‖⁻¹ • sphEquator z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have hsqrt : Real.sqrt (1 - sphHeight z ^ 2) = ‖sphEquator z‖ := by
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨(⟨‖sphEquator z‖⁻¹ • sphEquator z, mem_sphere_zero_iff_norm.mpr hx⟩,
      ⟨sphHeight z, Set.mem_Icc.mpr ⟨hz.1, hz.2⟩⟩), Subtype.ext (Subtype.ext ?_)⟩
    show snocLp (Real.sqrt (1 - sphHeight z ^ 2) • (‖sphEquator z‖⁻¹ • sphEquator z))
      (sphHeight z) = (z : EuclideanSpace ℝ (Fin (m + 2)))
    rw [hsqrt, smul_smul, mul_inv_cancel₀ hne, one_smul, snocLp_sphEquator_sphHeight]

variable (m) in
/-- **The intersection of the two enlarged hemispheres is `Sph m × [-1/3, 1/3]`.** -/
noncomputable def sphBeltHomeo : ↥(sphBelt m) ≃ₜ Sph m × Set.Icc (-(1 / 3) : ℝ) (1 / 3) :=
  haveI : CompactSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ beltOfProd_bijective)
    continuous_beltOfProd).symm

variable (m) in
/-- **The intersection of the two enlarged hemispheres is homotopy equivalent to `Sph m`.** -/
noncomputable def sphBeltHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(sphBelt m) (Sph m) :=
  haveI : ContractibleSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by rw [Set.mem_Icc]; norm_num⟩
  (sphBeltHomeo m).toHomotopyEquiv.trans
    (prodHomotopyEquivOfContractible (Sph m) (Set.Icc (-(1 / 3) : ℝ) (1 / 3)))

end Sphere

end Submission
