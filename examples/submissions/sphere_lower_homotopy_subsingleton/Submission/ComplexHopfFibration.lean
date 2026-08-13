/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.FibrationLESGroup
import Submission.HopfFibration
import Submission.MetricSpherePiOneGeneric
import Submission.Model.SphereConnected
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions

/-!
# The complex Hopf fibration in every dimension

This file constructs the quotient map from the unit sphere in `ℂ^(n+1)` to complex
projective `n`-space and proves directly that it is a Serre fibration.  A projective line is
represented by its normalized rank-one orthogonal projector.  Projecting and normalizing a
nearby unit vector gives short transport; uniform continuity and dyadic subdivision then give
the homotopy lifting property on every finite cube.

The basepoint fibre is explicitly homeomorphic to the circle.  The fibration long exact
sequence consequently computes `π₁`, `π₂`, and every homotopy group in degree at least
three.  The final section compares the intrinsic `L²` model with the plain function-space
projectivization used by the benchmark declarations.
-/

open scoped Topology Topology.Homotopy
open unitInterval

noncomputable section

namespace Submission

abbrev ComplexEuclidean (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

abbrev ComplexProjectiveModel (n : ℕ) := Projectivization ℂ (ComplexEuclidean n)

noncomputable instance instTopologicalSpaceComplexProjectiveModel (n : ℕ) :
    TopologicalSpace (ComplexProjectiveModel n) := by
  unfold ComplexProjectiveModel Projectivization
  infer_instance

abbrev ComplexUnitSphere (n : ℕ) := Metric.sphere (0 : ComplexEuclidean n) 1

noncomputable def complexUnitSphereBasepoint (n : ℕ) : ComplexUnitSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [ComplexUnitSphere]⟩

theorem norm_coe_complexUnitSphere {n : ℕ} (x : ComplexUnitSphere n) :
    ‖(x : ComplexEuclidean n)‖ = 1 := by
  have hx := x.property
  change dist (x : ComplexEuclidean n) 0 = 1 at hx
  rw [dist_zero_right] at hx
  exact hx

theorem complexUnitSphere_ne_zero {n : ℕ} (x : ComplexUnitSphere n) :
    (x : ComplexEuclidean n) ≠ 0 := by
  intro hx
  have := norm_coe_complexUnitSphere x
  rw [hx, norm_zero] at this
  norm_num at this

noncomputable def complexHopfMap (n : ℕ) :
    C(ComplexUnitSphere n, ComplexProjectiveModel n) where
  toFun x := Projectivization.mk ℂ (x : ComplexEuclidean n) (complexUnitSphere_ne_zero x)
  continuous_toFun := by
    let f : C(ComplexUnitSphere n, {v : ComplexEuclidean n // v ≠ 0}) :=
      ⟨fun x => ⟨x, complexUnitSphere_ne_zero x⟩,
        Continuous.subtype_mk continuous_subtype_val _⟩
    exact continuous_quotient_mk'.comp f.continuous

@[simp]
theorem complexHopfMap_basepoint (n : ℕ) :
    complexHopfMap n (complexUnitSphereBasepoint n) =
      Projectivization.mk ℂ (EuclideanSpace.single 0 1 : ComplexEuclidean n) (by simp) :=
  rfl

noncomputable def complexLineProjectorRaw {n : ℕ}
    (v : {v : ComplexEuclidean n // v ≠ 0}) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean n :=
  (inner ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n))⁻¹ •
    InnerProductSpace.rankOne ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n)

@[simp]
theorem complexLineProjectorRaw_apply {n : ℕ}
    (v : {v : ComplexEuclidean n // v ≠ 0}) (x : ComplexEuclidean n) :
    complexLineProjectorRaw v x =
      (inner ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n))⁻¹ •
        (inner ℂ (v : ComplexEuclidean n) x • (v : ComplexEuclidean n)) :=
  rfl

theorem continuous_complexLineProjectorRaw {n : ℕ} :
    Continuous (complexLineProjectorRaw :
      {v : ComplexEuclidean n // v ≠ 0} → ComplexEuclidean n →L[ℂ] ComplexEuclidean n) := by
  unfold complexLineProjectorRaw
  have hinner : Continuous fun v : {v : ComplexEuclidean n // v ≠ 0} =>
      inner ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n) := by
    fun_prop
  have hinv : Continuous fun v : {v : ComplexEuclidean n // v ≠ 0} =>
      (inner ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n))⁻¹ :=
    hinner.inv₀ fun v => inner_self_ne_zero.mpr v.property
  have hrank : Continuous fun v : {v : ComplexEuclidean n // v ≠ 0} =>
      InnerProductSpace.rankOne ℂ (v : ComplexEuclidean n) (v : ComplexEuclidean n) := by
    rw [continuous_clm_apply]
    intro x
    simp only [InnerProductSpace.rankOne_apply]
    fun_prop
  exact hinv.smul hrank

theorem complexLineProjectorRaw_smul_invariant {n : ℕ}
    (a b : {v : ComplexEuclidean n // v ≠ 0}) (t : ℂ)
    (h : a = t • (b : ComplexEuclidean n)) :
    complexLineProjectorRaw a = complexLineProjectorRaw b := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    rw [h, ht, zero_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [complexLineProjectorRaw_apply, h, inner_smul_left, inner_smul_right,
    smul_smul]
  apply congrArg (fun c : ℂ => c • (b : ComplexEuclidean n))
  field_simp [ht, inner_self_ne_zero.mpr b.property]

noncomputable def complexLineProjector (n : ℕ) :
    ComplexProjectiveModel n → ComplexEuclidean n →L[ℂ] ComplexEuclidean n :=
  Projectivization.lift complexLineProjectorRaw complexLineProjectorRaw_smul_invariant

@[simp]
theorem complexLineProjector_mk {n : ℕ} (v : ComplexEuclidean n) (hv : v ≠ 0) :
    complexLineProjector n (Projectivization.mk ℂ v hv) =
      complexLineProjectorRaw ⟨v, hv⟩ :=
  rfl

theorem continuous_complexLineProjector (n : ℕ) :
    Continuous (complexLineProjector n) := by
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr continuous_complexLineProjectorRaw

theorem inner_self_complexUnitSphere {n : ℕ} (x : ComplexUnitSphere n) :
    inner ℂ (x : ComplexEuclidean n) (x : ComplexEuclidean n) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_coe_complexUnitSphere]
  norm_num

@[simp]
theorem complexLineProjector_hopfMap_apply {n : ℕ} (x : ComplexUnitSphere n) :
    complexLineProjector n (complexHopfMap n x) (x : ComplexEuclidean n) =
      (x : ComplexEuclidean n) := by
  change complexLineProjector n
      (Projectivization.mk ℂ (x : ComplexEuclidean n) (complexUnitSphere_ne_zero x))
      (x : ComplexEuclidean n) = (x : ComplexEuclidean n)
  rw [complexLineProjector_mk]
  simp [complexLineProjectorRaw_apply]

theorem continuous_complexLineProjector_apply (n : ℕ) :
    Continuous fun p : ComplexProjectiveModel n × ComplexEuclidean n =>
      complexLineProjector n p.1 p.2 :=
  ((continuous_complexLineProjector n).comp continuous_fst).clm_apply continuous_snd

theorem complexLineProjector_apply_mem_line {n : ℕ}
    (p : ComplexProjectiveModel n) (x : ComplexEuclidean n)
    (hpx : complexLineProjector n p x ≠ 0) :
    Projectivization.mk ℂ (complexLineProjector n p x) hpx = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [Projectivization.mk_eq_mk_iff']
      let c : ℂ :=
        (inner ℂ v v)⁻¹ * inner ℂ v x
      have hc : c • v = complexLineProjectorRaw
          (⟨v, hv⟩ : {w : ComplexEuclidean n // w ≠ 0}) x := by
        simp [c, complexLineProjectorRaw_apply, smul_smul]
      have heval : complexLineProjector n (Projectivization.mk ℂ v hv) x =
          complexLineProjectorRaw (⟨v, hv⟩ : {w : ComplexEuclidean n // w ≠ 0}) x :=
        congrArg (fun f : ComplexEuclidean n →L[ℂ] ComplexEuclidean n => f x)
          (complexLineProjector_mk v hv)
      exact ⟨c, hc.trans heval.symm⟩

abbrev ComplexHopfTransportDomain (n : ℕ) :=
  {p : ComplexUnitSphere n × ComplexProjectiveModel n //
    dist (complexLineProjector n p.2)
      (complexLineProjector n (complexHopfMap n p.1)) < 1}

def ComplexHopfTransportDomain.source {n : ℕ}
    (p : ComplexHopfTransportDomain n) : ComplexUnitSphere n :=
  p.1.1

def ComplexHopfTransportDomain.target {n : ℕ}
    (p : ComplexHopfTransportDomain n) : ComplexProjectiveModel n :=
  p.1.2

theorem complexHopfProject_ne_zero {n : ℕ} (p : ComplexHopfTransportDomain n) :
    complexLineProjector n p.target (p.source : ComplexEuclidean n) ≠ 0 := by
  intro hzero
  have hself := complexLineProjector_hopfMap_apply p.source
  have hopNorm :=
    (complexLineProjector n p.target -
      complexLineProjector n (complexHopfMap n p.source)).le_opNorm
        (p.source : ComplexEuclidean n)
  rw [sub_apply, hzero, hself, zero_sub, norm_neg,
    norm_coe_complexUnitSphere, mul_one] at hopNorm
  have hdist : ‖complexLineProjector n p.target -
      complexLineProjector n (complexHopfMap n p.source)‖ < 1 := by
    simpa [dist_eq_norm, ComplexHopfTransportDomain.source,
      ComplexHopfTransportDomain.target] using p.property
  linarith

noncomputable def complexHopfTransportVec {n : ℕ} (p : ComplexHopfTransportDomain n) :
    ComplexEuclidean n :=
  NormedSpace.normalize
    (complexLineProjector n p.target (p.source : ComplexEuclidean n))

theorem norm_complexHopfTransportVec {n : ℕ} (p : ComplexHopfTransportDomain n) :
    ‖complexHopfTransportVec p‖ = 1 :=
  NormedSpace.norm_normalize (complexHopfProject_ne_zero p)

noncomputable def complexHopfTransport {n : ℕ} (p : ComplexHopfTransportDomain n) :
    ComplexUnitSphere n :=
  ⟨complexHopfTransportVec p, by
    rw [Metric.mem_sphere, dist_zero_right, norm_complexHopfTransportVec]⟩

theorem continuous_complexHopfTransportVec {n : ℕ} :
    Continuous (complexHopfTransportVec : ComplexHopfTransportDomain n → ComplexEuclidean n) := by
  have hargs : Continuous fun p : ComplexHopfTransportDomain n =>
      (p.target, (p.source : ComplexEuclidean n)) := by
    unfold ComplexHopfTransportDomain.source ComplexHopfTransportDomain.target
    fun_prop
  have hv : Continuous fun p : ComplexHopfTransportDomain n =>
      complexLineProjector n p.target (p.source : ComplexEuclidean n) :=
    (continuous_complexLineProjector_apply n).comp hargs
  unfold complexHopfTransportVec NormedSpace.normalize
  exact (hv.norm.inv₀ fun p => norm_ne_zero_iff.mpr (complexHopfProject_ne_zero p)).smul hv

theorem continuous_complexHopfTransport {n : ℕ} :
    Continuous (complexHopfTransport : ComplexHopfTransportDomain n → ComplexUnitSphere n) :=
  Continuous.subtype_mk continuous_complexHopfTransportVec _

@[simp]
theorem complexHopfMap_complexHopfTransport {n : ℕ} (p : ComplexHopfTransportDomain n) :
    complexHopfMap n (complexHopfTransport p) = p.target := by
  let v : ComplexEuclidean n :=
    complexLineProjector n p.target (p.source : ComplexEuclidean n)
  have hv : v ≠ 0 := complexHopfProject_ne_zero p
  have hnormalize : NormedSpace.normalize v ≠ 0 := by
    exact fun h => hv ((NormedSpace.normalize_eq_zero_iff v).mp h)
  have hsame : Projectivization.mk ℂ (NormedSpace.normalize v) hnormalize =
      Projectivization.mk ℂ v hv := by
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(‖v‖⁻¹ : ℂ), ?_⟩
    unfold NormedSpace.normalize
    simpa using (RCLike.real_smul_eq_coe_smul (K := ℂ) ‖v‖⁻¹ v).symm
  change Projectivization.mk ℂ (NormedSpace.normalize v) hnormalize = p.target
  exact hsame.trans (complexLineProjector_apply_mem_line p.target _ hv)

noncomputable def complexHopfTransportSelf {n : ℕ}
    (x : ComplexUnitSphere n) : ComplexHopfTransportDomain n :=
  ⟨(x, complexHopfMap n x), by simp⟩

@[simp]
theorem complexHopfTransport_self {n : ℕ} (x : ComplexUnitSphere n) :
    complexHopfTransport (complexHopfTransportSelf x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize
      (complexLineProjector n (complexHopfMap n x) (x : ComplexEuclidean n)) =
    (x : ComplexEuclidean n)
  rw [complexLineProjector_hopfMap_apply]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_coe_complexUnitSphere x)

/-! ## Dyadic lifting -/

/-- On time intervals of dyadic length `2^-m`, the projectors of the base lines move by
less than one in operator norm. -/
def ComplexHopfDyadicControl {A : Type*} [TopologicalSpace A]
    (n m : ℕ) (H : C(I × A, ComplexProjectiveModel n)) : Prop :=
  ∀ s t a, dist s t ≤ (1 / 2 : ℝ) ^ m →
    dist (complexLineProjector n (H (s, a)))
      (complexLineProjector n (H (t, a))) < 1

theorem ComplexHopfDyadicControl.lowerHalf
    {A : Type*} [TopologicalSpace A] {n m : ℕ}
    {H : C(I × A, ComplexProjectiveModel n)}
    (h : ComplexHopfDyadicControl n (m + 1) H) :
    ComplexHopfDyadicControl n m (hopfLowerHalf H) := by
  intro s t a hst
  apply h (hopfLowerHalfTime s) (hopfLowerHalfTime t) a
  rw [dist_hopfLowerHalfTime, pow_succ]
  nlinarith

theorem ComplexHopfDyadicControl.upperHalf
    {A : Type*} [TopologicalSpace A] {n m : ℕ}
    {H : C(I × A, ComplexProjectiveModel n)}
    (h : ComplexHopfDyadicControl n (m + 1) H) :
    ComplexHopfDyadicControl n m (hopfUpperHalf H) := by
  intro s t a hst
  apply h (hopfUpperHalfTime s) (hopfUpperHalfTime t) a
  rw [dist_hopfUpperHalfTime, pow_succ]
  nlinarith

theorem exists_complexHopfLift_of_dyadicControl_zero
    {A : Type*} [TopologicalSpace A] (n : ℕ)
    (f : C(A, ComplexUnitSphere n))
    (H : C(I × A, ComplexProjectiveModel n))
    (hzero : ∀ a, H (0, a) = complexHopfMap n (f a))
    (hcontrol : ComplexHopfDyadicControl n 0 H) :
    ∃ L : C(I × A, ComplexUnitSphere n),
      (∀ a, L (0, a) = f a) ∧ ∀ z, complexHopfMap n (L z) = H z := by
  let D : C(I × A, ComplexHopfTransportDomain n) :=
    { toFun := fun z => ⟨(f z.2, H z), by
        change dist (complexLineProjector n (H z))
          (complexLineProjector n (complexHopfMap n (f z.2))) < 1
        rw [← hzero z.2]
        apply hcontrol z.1 0 z.2
        simp only [pow_zero]
        exact unitInterval_dist_le_one _ _⟩
      continuous_toFun := by
        apply continuous_induced_rng.2
        exact (f.continuous.comp continuous_snd).prodMk H.continuous }
  refine ⟨⟨fun z => complexHopfTransport (D z),
      continuous_complexHopfTransport.comp D.continuous⟩, ?_, ?_⟩
  · intro a
    have hD : D (0, a) = complexHopfTransportSelf (f a) := by
      apply Subtype.ext
      exact Prod.ext rfl (hzero a)
    change complexHopfTransport (D (0, a)) = f a
    rw [hD, complexHopfTransport_self]
  · intro z
    exact complexHopfMap_complexHopfTransport (D z)

theorem exists_complexHopfLift_of_dyadicControl
    {A : Type*} [TopologicalSpace A] (n m : ℕ)
    (f : C(A, ComplexUnitSphere n))
    (H : C(I × A, ComplexProjectiveModel n))
    (hzero : ∀ a, H (0, a) = complexHopfMap n (f a))
    (hcontrol : ComplexHopfDyadicControl n m H) :
    ∃ L : C(I × A, ComplexUnitSphere n),
      (∀ a, L (0, a) = f a) ∧ ∀ z, complexHopfMap n (L z) = H z := by
  induction m generalizing f H with
  | zero =>
      exact exists_complexHopfLift_of_dyadicControl_zero n f H hzero hcontrol
  | succ m ih =>
      have hzeroLower : ∀ a, hopfLowerHalf H (0, a) = complexHopfMap n (f a) := by
        intro a
        simpa using hzero a
      obtain ⟨L, hLzero, hLproj⟩ :=
        ih f (hopfLowerHalf H) hzeroLower hcontrol.lowerHalf
      let fmid : C(A, ComplexUnitSphere n) :=
        { toFun := fun a => L (1, a)
          continuous_toFun := L.continuous.comp
            (continuous_const.prodMk continuous_id) }
      have hzeroUpper : ∀ a, hopfUpperHalf H (0, a) = complexHopfMap n (fmid a) := by
        intro a
        calc
          hopfUpperHalf H (0, a) = hopfLowerHalf H (1, a) := by
            change H (hopfUpperHalfTime 0, a) = H (hopfLowerHalfTime 1, a)
            rw [hopfLowerHalfTime_one_eq_hopfUpperHalfTime_zero]
          _ = complexHopfMap n (L (1, a)) := (hLproj (1, a)).symm
          _ = complexHopfMap n (fmid a) := rfl
      obtain ⟨R, hRzero, hRproj⟩ :=
        ih fmid (hopfUpperHalf H) hzeroUpper hcontrol.upperHalf
      let fend : C(A, ComplexUnitSphere n) :=
        { toFun := fun a => R (1, a)
          continuous_toFun := R.continuous.comp
            (continuous_const.prodMk continuous_id) }
      let Lhom : ContinuousMap.Homotopy f fmid :=
        { toFun := L
          continuous_toFun := L.continuous
          map_zero_left := hLzero
          map_one_left := fun _ => rfl }
      let Rhom : ContinuousMap.Homotopy fmid fend :=
        { toFun := R
          continuous_toFun := R.continuous
          map_zero_left := hRzero
          map_one_left := fun _ => rfl }
      let K : ContinuousMap.Homotopy f fend := Lhom.trans Rhom
      refine ⟨K.toContinuousMap, K.map_zero_left, ?_⟩
      intro z
      dsimp [K]
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs with hz
      · change complexHopfMap n (L _) = H z
        rw [hLproj]
        apply ContinuousMap.congr_arg H
        apply Prod.ext
        · apply Subtype.ext
          change (2 * (z.1 : ℝ)) / 2 = (z.1 : ℝ)
          ring
        · rfl
      · change complexHopfMap n (R _) = H z
        rw [hRproj]
        apply ContinuousMap.congr_arg H
        apply Prod.ext
        · apply Subtype.ext
          change ((2 * (z.1 : ℝ) - 1) + 1) / 2 = (z.1 : ℝ)
          ring
        · rfl

theorem exists_complexHopfDyadicControl
    {A : Type*} [PseudoMetricSpace A] [CompactSpace A] (n : ℕ)
    (H : C(I × A, ComplexProjectiveModel n)) :
    ∃ m, ComplexHopfDyadicControl n m H := by
  let PH : C(I × A, ComplexEuclidean n →L[ℂ] ComplexEuclidean n) :=
    ⟨fun z => complexLineProjector n (H z),
      (continuous_complexLineProjector n).comp H.continuous⟩
  have huc : UniformContinuous PH :=
    CompactSpace.uniformContinuous_of_continuous PH.continuous
  obtain ⟨delta, hdelta, hmove⟩ :=
    Metric.uniformContinuous_iff.mp huc 1 (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < delta :=
    exists_pow_lt_of_lt_one hdelta (by norm_num)
  refine ⟨m, ?_⟩
  intro s t a hst
  apply hmove
  rw [dist_prod_same_right]
  exact lt_of_le_of_lt hst hm

theorem complexHopfMap_hasHLP_cube (n d : ℕ) :
    HasHLP (complexHopfMap n) (Fin d → I) := by
  intro f H hzero
  obtain ⟨m, hcontrol⟩ := exists_complexHopfDyadicControl n H
  exact exists_complexHopfLift_of_dyadicControl n m f H hzero hcontrol

theorem complexHopfMap_isSerreFibration (n : ℕ) :
    IsSerreFibration (complexHopfMap n) :=
  complexHopfMap_hasHLP_cube n

/-! ## The basepoint fibre -/

noncomputable def complexProjectiveModelBasepoint (n : ℕ) :
    ComplexProjectiveModel n :=
  complexHopfMap n (complexUnitSphereBasepoint n)

abbrev ComplexHopfFiber (n : ℕ) :=
  (⇑(complexHopfMap n) ⁻¹' {complexProjectiveModelBasepoint n} :
    Set (ComplexUnitSphere n))

noncomputable def complexHopfFiberBasepoint (n : ℕ) : ComplexHopfFiber n :=
  ⟨complexUnitSphereBasepoint n, rfl⟩

noncomputable def complexCircleInclVec (n : ℕ) (z : Circle) : ComplexEuclidean n :=
  EuclideanSpace.single 0 (z : ℂ)

@[simp]
theorem norm_complexCircleInclVec (n : ℕ) (z : Circle) :
    ‖complexCircleInclVec n z‖ = 1 := by
  simp [complexCircleInclVec]

theorem continuous_complexCircleInclVec (n : ℕ) :
    Continuous (complexCircleInclVec n) := by
  have h : Isometry fun z : ℂ =>
      (EuclideanSpace.single 0 z : ComplexEuclidean n) := by
    intro z w
    exact PiLp.edist_single_same 2 (fun _ : Fin (n + 1) => ℂ) 0 z w
  exact h.continuous.comp continuous_subtype_val

noncomputable def complexCircleIncl (n : ℕ) (z : Circle) : ComplexUnitSphere n :=
  ⟨complexCircleInclVec n z, by
    rw [Metric.mem_sphere, dist_zero_right, norm_complexCircleInclVec]⟩

theorem continuous_complexCircleIncl (n : ℕ) :
    Continuous (complexCircleIncl n) :=
  Continuous.subtype_mk (continuous_complexCircleInclVec n) _

@[simp]
theorem complexCircleIncl_one (n : ℕ) :
    complexCircleIncl n 1 = complexUnitSphereBasepoint n := by
  rfl

@[simp]
theorem complexHopfMap_complexCircleIncl (n : ℕ) (z : Circle) :
    complexHopfMap n (complexCircleIncl n z) = complexProjectiveModelBasepoint n := by
  change Projectivization.mk ℂ (EuclideanSpace.single 0 (z : ℂ)) _ =
    Projectivization.mk ℂ (EuclideanSpace.single 0 1 : ComplexEuclidean n) _
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨(z : ℂ), by ext i; simp⟩

theorem complexHopfFiber_vector_eq (n : ℕ) (x : ComplexHopfFiber n) :
    ∃ z : ℂ, z • (EuclideanSpace.single 0 1 : ComplexEuclidean n) =
      ((x : ComplexUnitSphere n) : ComplexEuclidean n) := by
  have hx := x.property
  change Projectivization.mk ℂ
      (((x : ComplexUnitSphere n) : ComplexEuclidean n)) _ =
    Projectivization.mk ℂ (EuclideanSpace.single 0 1 : ComplexEuclidean n) _ at hx
  rw [Projectivization.mk_eq_mk_iff'] at hx
  exact hx

theorem norm_complexHopfFiber_first (n : ℕ) (x : ComplexHopfFiber n) :
    ‖((x : ComplexUnitSphere n) : ComplexEuclidean n) 0‖ = 1 := by
  obtain ⟨z, hz⟩ := complexHopfFiber_vector_eq n x
  have hnorm := norm_coe_complexUnitSphere (x : ComplexUnitSphere n)
  rw [← hz] at hnorm
  have hzNorm : ‖z‖ = 1 := by
    simpa only [norm_smul, PiLp.norm_single, norm_one, mul_one] using hnorm
  rw [← hz]
  simpa using hzNorm

noncomputable def complexCircleToHopfFiber (n : ℕ) (z : Circle) :
    ComplexHopfFiber n :=
  ⟨complexCircleIncl n z, complexHopfMap_complexCircleIncl n z⟩

noncomputable def complexHopfFiberToCircle (n : ℕ) (x : ComplexHopfFiber n) : Circle :=
  ⟨((x : ComplexUnitSphere n) : ComplexEuclidean n) 0,
    mem_sphere_zero_iff_norm.mpr (norm_complexHopfFiber_first n x)⟩

theorem continuous_complexCircleToHopfFiber (n : ℕ) :
    Continuous (complexCircleToHopfFiber n) :=
  Continuous.subtype_mk (continuous_complexCircleIncl n) _

theorem continuous_complexHopfFiberToCircle (n : ℕ) :
    Continuous (complexHopfFiberToCircle n) := by
  refine Continuous.subtype_mk ?_ ?_
  exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℂ) 0).comp
    (continuous_subtype_val.comp continuous_subtype_val)

noncomputable def circleHomeomorphComplexHopfFiber (n : ℕ) :
    Circle ≃ₜ ComplexHopfFiber n where
  toFun := complexCircleToHopfFiber n
  invFun := complexHopfFiberToCircle n
  left_inv z := by
    apply Subtype.ext
    simp [complexHopfFiberToCircle, complexCircleToHopfFiber, complexCircleIncl,
      complexCircleInclVec]
  right_inv x := by
    obtain ⟨z, hz⟩ := complexHopfFiber_vector_eq n x
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [complexCircleToHopfFiber, complexCircleIncl, complexCircleInclVec,
        complexHopfFiberToCircle]
    · have hzi := congrArg (fun v : ComplexEuclidean n => v i) hz
      simpa [complexCircleToHopfFiber, complexCircleIncl, complexCircleInclVec,
        complexHopfFiberToCircle, hi] using hzi
  continuous_toFun := continuous_complexCircleToHopfFiber n
  continuous_invFun := continuous_complexHopfFiberToCircle n

@[simp]
theorem circleHomeomorphComplexHopfFiber_one (n : ℕ) :
    circleHomeomorphComplexHopfFiber n 1 = complexHopfFiberBasepoint n := by
  rfl

/-! ## Realification of the total sphere -/

noncomputable def complexEuclideanRealLinearIsometryEquiv (n : ℕ) :
    ComplexEuclidean n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * n + 1 + 1)) :=
  (Pi.orthonormalBasis
      (fun _ : Fin (n + 1) => Complex.orthonormalBasisOneI)).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      ((Equiv.sigmaEquivProd (Fin (n + 1)) (Fin 2)).trans
        ((finProdFinEquiv : Fin (n + 1) × Fin 2 ≃ Fin ((n + 1) * 2)).trans
          (finCongr (by omega : (n + 1) * 2 = 2 * n + 1 + 1)))))

noncomputable def complexUnitSphereHomeomorphSphere (n : ℕ) :
    ComplexUnitSphere n ≃ₜ Sph (2 * n + 1) where
  toFun x := ⟨complexEuclideanRealLinearIsometryEquiv n x, by
    rw [Metric.mem_sphere, dist_zero_right,
      (complexEuclideanRealLinearIsometryEquiv n).norm_map,
      norm_coe_complexUnitSphere]⟩
  invFun y := ⟨(complexEuclideanRealLinearIsometryEquiv n).symm y, by
    rw [Metric.mem_sphere, dist_zero_right,
      (complexEuclideanRealLinearIsometryEquiv n).symm.norm_map, norm_coe_sph]⟩
  left_inv x := Subtype.ext <|
    (complexEuclideanRealLinearIsometryEquiv n).symm_apply_apply x
  right_inv y := Subtype.ext <|
    (complexEuclideanRealLinearIsometryEquiv n).apply_symm_apply y
  continuous_toFun := Continuous.subtype_mk
    ((complexEuclideanRealLinearIsometryEquiv n).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((complexEuclideanRealLinearIsometryEquiv n).symm.continuous.comp continuous_subtype_val) _

theorem complexUnitSphere_positive_lower_homotopy_subsingleton
    (n q : ℕ) (hq : q + 1 < 2 * n + 1) :
    Subsingleton
      (π_ (q + 1) (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin (q + 1)) (complexUnitSphereHomeomorphSphere n).toHomotopyEquiv
      (complexUnitSphereBasepoint n)
  exact e.toEquiv.subsingleton_congr.mpr <|
    subsingleton_homotopyGroup_sphere_of_lt (q + 1) (2 * n + 1) hq
      (complexUnitSphereHomeomorphSphere n (complexUnitSphereBasepoint n))

/-! ## Homotopy groups of the fibre and base -/

@[simp]
theorem circleHomeomorphSphOne_one :
    circleHomeomorphSphOne (1 : Circle) = sphereBasepoint 1 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [circleHomeomorphSphOne, sphereBasepoint]

@[simp]
theorem circleHomeomorphSphOne_symm_basepoint :
    circleHomeomorphSphOne.symm (sphereBasepoint 1) = (1 : Circle) := by
  apply circleHomeomorphSphOne.injective
  rw [circleHomeomorphSphOne.apply_symm_apply, circleHomeomorphSphOne_one]

noncomputable def sphOneHomeomorphComplexHopfFiber (n : ℕ) :
    Sph 1 ≃ₜ ComplexHopfFiber n :=
  circleHomeomorphSphOne.symm.trans (circleHomeomorphComplexHopfFiber n)

@[simp]
theorem sphOneHomeomorphComplexHopfFiber_basepoint (n : ℕ) :
    sphOneHomeomorphComplexHopfFiber n (sphereBasepoint 1) =
      complexHopfFiberBasepoint n := by
  simp [sphOneHomeomorphComplexHopfFiber]

theorem complexHopfFiber_piZero_subsingleton (n : ℕ) :
    Subsingleton (π_ 0 (ComplexHopfFiber n) (complexHopfFiberBasepoint n)) := by
  letI : PathConnectedSpace (Sph 1) := pathConnectedSpace_sph (by omega)
  letI : PathConnectedSpace (ComplexHopfFiber n) :=
    (sphOneHomeomorphComplexHopfFiber n).surjective.pathConnectedSpace
      (sphOneHomeomorphComplexHopfFiber n).continuous
  exact subsingleton_piZero (complexHopfFiberBasepoint n)

theorem complexHopfFiber_piOne_mulEquiv_int (n : ℕ) :
    Nonempty
      (π_ 1 (ComplexHopfFiber n) (complexHopfFiberBasepoint n) ≃*
        Multiplicative ℤ) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 1)
    (sphOneHomeomorphComplexHopfFiber n)
    (sphOneHomeomorphComplexHopfFiber_basepoint n)
  obtain ⟨circle⟩ := pi1_sph_one_at_mulEquiv_int (sphereBasepoint 1)
  exact ⟨e.symm.trans circle⟩

theorem complexHopfFiber_higher_homotopy_subsingleton (n k : ℕ) :
    Subsingleton
      (π_ (k + 2) (ComplexHopfFiber n) (complexHopfFiberBasepoint n)) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (k + 2))
    (sphOneHomeomorphComplexHopfFiber n)
    (sphOneHomeomorphComplexHopfFiber_basepoint n)
  exact e.toEquiv.subsingleton_congr.mp <|
    sph_one_higher_homotopy_subsingleton_at k (sphereBasepoint 1)

theorem piOne_complexProjectiveModel_subsingleton
    (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (π_ 1 (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n)) := by
  let e := complexHopfFiberBasepoint n
  let hp := complexHopfMap_isSerreFibration n
  have hE : Subsingleton
      (π_ 1 (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) :=
    complexUnitSphere_positive_lower_homotopy_subsingleton n 0 (by omega)
  have hE' : Subsingleton
      (π_ 1 (ComplexUnitSphere n) (e : ComplexUnitSphere n)) := by
    simpa [e, complexHopfFiberBasepoint] using hE
  have hF : Subsingleton
      (π_ 0 (ComplexHopfFiber n) (complexHopfFiberBasepoint n)) :=
    complexHopfFiber_piZero_subsingleton n
  have key : ∀ x :
      π_ 1 (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n),
      x = default := by
    intro x
    have hmem : x ∈ fibDelta e hp 0 ⁻¹' {default} := by
      show fibDelta e hp 0 x = default
      exact Subsingleton.elim _ _
    rw [isExactAt_pStarAbs_fibDelta e hp 0] at hmem
    obtain ⟨y, rfl⟩ := hmem
    rw [hE'.elim y default, pStarAbs_default]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem piTwo_complexProjectiveModel_mulEquiv_int
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (π_ 2 (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n) ≃*
        Multiplicative ℤ) := by
  let e := complexHopfFiberBasepoint n
  have hE2 : Subsingleton
      (π_ 2 (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) :=
    complexUnitSphere_positive_lower_homotopy_subsingleton n 1 (by omega)
  have hE1 : Subsingleton
      (π_ 1 (ComplexUnitSphere n) (complexUnitSphereBasepoint n)) :=
    complexUnitSphere_positive_lower_homotopy_subsingleton n 0 (by omega)
  let delta := fibDeltaMulEquiv e (complexHopfMap_isSerreFibration n) 0 hE2 hE1
  obtain ⟨circle⟩ := complexHopfFiber_piOne_mulEquiv_int n
  exact ⟨delta.trans circle⟩

noncomputable def complexHopfPiHigherHom (n k : ℕ) :
    π_ (k + 3) (ComplexUnitSphere n) (complexUnitSphereBasepoint n) →*
      π_ (k + 3) (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n) :=
  pStarAbsHom (complexHopfFiberBasepoint n) (k + 2)

theorem complexHopfPiHigherHom_bijective (n k : ℕ) :
    Function.Bijective (complexHopfPiHigherHom n k) := by
  have h := bijective_pStarAbs_of_subsingleton_fibre
    (complexHopfFiberBasepoint n) (complexHopfMap_isSerreFibration n) (k + 2)
    (complexHopfFiber_higher_homotopy_subsingleton n (k + 1))
    (complexHopfFiber_higher_homotopy_subsingleton n k)
  have heq : ⇑(complexHopfPiHigherHom n k) =
      pStarAbs (complexHopfFiberBasepoint n) (k + 3) := by
    funext x
    exact pStarAbsHom_apply (complexHopfFiberBasepoint n) (k + 2) x
  rw [heq]
  exact h

noncomputable def complexHopfPiHigherEquiv (n k : ℕ) :
    π_ (k + 3) (ComplexUnitSphere n) (complexUnitSphereBasepoint n) ≃*
      π_ (k + 3) (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n) :=
  MulEquiv.ofBijective (complexHopfPiHigherHom n k)
    (complexHopfPiHigherHom_bijective n k)

theorem complexProjectiveModel_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (_hn : 1 ≤ n) :
    Nonempty
      (π_ (k + 3) (ComplexProjectiveModel n) (complexProjectiveModelBasepoint n) ≃*
        π_ (k + 3) (Sph (2 * n + 1)) (sphereBasepoint (2 * n + 1))) := by
  letI : PathConnectedSpace (Sph (2 * n + 1)) := pathConnectedSpace_sph (by omega)
  obtain ⟨changeSpace⟩ := nonempty_mulEquiv_of_homotopyEquiv'
    (N := Fin (k + 3)) (complexUnitSphereHomeomorphSphere n).toHomotopyEquiv
      (complexUnitSphereBasepoint n)
  obtain ⟨changeBasepoint⟩ := nonempty_mulEquiv_of_pathConnectedSpace
    (N := Fin (k + 3))
      (complexUnitSphereHomeomorphSphere n (complexUnitSphereBasepoint n))
      (sphereBasepoint (2 * n + 1))
  exact ⟨(complexHopfPiHigherEquiv n k).symm.trans
    (changeSpace.trans changeBasepoint)⟩

/-! ## Comparison with the plain function-space projective model -/

abbrev ComplexProjectiveFunctionModel (n : ℕ) :=
  Projectivization ℂ (Fin (n + 1) → ℂ)

noncomputable instance instTopologicalSpaceComplexProjectiveFunctionModel (n : ℕ) :
    TopologicalSpace (ComplexProjectiveFunctionModel n) := by
  unfold ComplexProjectiveFunctionModel Projectivization
  infer_instance

noncomputable def complexCoordinateEquiv (n : ℕ) :
    ComplexEuclidean n ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)

noncomputable def complexProjectiveModelToFunction (n : ℕ) :
    ComplexProjectiveModel n → ComplexProjectiveFunctionModel n :=
  Projectivization.map (complexCoordinateEquiv n).toLinearEquiv.toLinearMap
    (complexCoordinateEquiv n).toLinearEquiv.injective

noncomputable def complexProjectiveFunctionToModel (n : ℕ) :
    ComplexProjectiveFunctionModel n → ComplexProjectiveModel n :=
  Projectivization.map (complexCoordinateEquiv n).symm.toLinearEquiv.toLinearMap
    (complexCoordinateEquiv n).symm.toLinearEquiv.injective

@[simp]
theorem complexProjectiveModelToFunction_mk (n : ℕ)
    (v : ComplexEuclidean n) (hv : v ≠ 0) :
    complexProjectiveModelToFunction n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (complexCoordinateEquiv n v)
        ((complexCoordinateEquiv n).injective.ne hv) :=
  rfl

@[simp]
theorem complexProjectiveFunctionToModel_mk (n : ℕ)
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    complexProjectiveFunctionToModel n (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ ((complexCoordinateEquiv n).symm v)
        ((complexCoordinateEquiv n).symm.injective.ne hv) :=
  rfl

theorem continuous_complexProjectiveModelToFunction (n : ℕ) :
    Continuous (complexProjectiveModelToFunction n) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have h : Continuous fun v : {v : ComplexEuclidean n // v ≠ 0} =>
      Projectivization.mk ℂ (complexCoordinateEquiv n v)
        ((complexCoordinateEquiv n).injective.ne v.property) := by
    apply continuous_quotient_mk'.comp
    exact Continuous.subtype_mk
      ((complexCoordinateEquiv n).continuous.comp continuous_subtype_val) _
  exact h

theorem continuous_complexProjectiveFunctionToModel (n : ℕ) :
    Continuous (complexProjectiveFunctionToModel n) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  have h : Continuous fun v : {v : (Fin (n + 1) → ℂ) // v ≠ 0} =>
      Projectivization.mk ℂ ((complexCoordinateEquiv n).symm v)
        ((complexCoordinateEquiv n).symm.injective.ne v.property) := by
    apply continuous_quotient_mk'.comp
    exact Continuous.subtype_mk
      ((complexCoordinateEquiv n).symm.continuous.comp continuous_subtype_val) _
  exact h

noncomputable def complexProjectiveModelHomeomorphFunction (n : ℕ) :
    ComplexProjectiveModel n ≃ₜ ComplexProjectiveFunctionModel n where
  toFun := complexProjectiveModelToFunction n
  invFun := complexProjectiveFunctionToModel n
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
        rw [complexProjectiveModelToFunction_mk,
          complexProjectiveFunctionToModel_mk,
          Projectivization.mk_eq_mk_iff']
        refine ⟨1, ?_⟩
        simp
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
        rw [complexProjectiveFunctionToModel_mk,
          complexProjectiveModelToFunction_mk,
          Projectivization.mk_eq_mk_iff']
        refine ⟨1, ?_⟩
        simp
  continuous_toFun := continuous_complexProjectiveModelToFunction n
  continuous_invFun := continuous_complexProjectiveFunctionToModel n

noncomputable def complexProjectiveFunctionBasepoint (n : ℕ) :
    ComplexProjectiveFunctionModel n :=
  Projectivization.mk ℂ (Pi.single 0 1)
    (Pi.single_ne_zero_iff.mpr one_ne_zero)

@[simp]
theorem complexProjectiveModelHomeomorphFunction_basepoint (n : ℕ) :
    complexProjectiveModelHomeomorphFunction n
      (complexProjectiveModelBasepoint n) =
        complexProjectiveFunctionBasepoint n := by
  change complexProjectiveModelToFunction n
      (Projectivization.mk ℂ (EuclideanSpace.single 0 1) _) = _
  rw [complexProjectiveModelToFunction_mk]
  change Projectivization.mk ℂ
      (complexCoordinateEquiv n (EuclideanSpace.single 0 1)) _ =
    Projectivization.mk ℂ (Pi.single 0 1) _
  apply congrArg (fun v : {v : (Fin (n + 1) → ℂ) // v ≠ 0} =>
    Projectivization.mk' ℂ v)
  apply Subtype.ext
  funext i
  simp [complexCoordinateEquiv, Pi.single_apply]

theorem piOne_complexProjectiveFunctionModel_subsingleton
    (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton
      (π_ 1 (ComplexProjectiveFunctionModel n)
        (complexProjectiveFunctionBasepoint n)) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 1)
    (complexProjectiveModelHomeomorphFunction n)
    (complexProjectiveModelHomeomorphFunction_basepoint n)
  exact e.toEquiv.subsingleton_congr.mp <|
    piOne_complexProjectiveModel_subsingleton n hn

theorem piTwo_complexProjectiveFunctionModel_mulEquiv_int
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (π_ 2 (ComplexProjectiveFunctionModel n)
          (complexProjectiveFunctionBasepoint n) ≃* Multiplicative ℤ) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin 2)
    (complexProjectiveModelHomeomorphFunction n)
    (complexProjectiveModelHomeomorphFunction_basepoint n)
  obtain ⟨h⟩ := piTwo_complexProjectiveModel_mulEquiv_int n hn
  exact ⟨e.symm.trans h⟩

theorem complexProjectiveFunctionModel_higher_homotopy_mulEquiv_sphere
    (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (π_ (k + 3) (ComplexProjectiveFunctionModel n)
          (complexProjectiveFunctionBasepoint n) ≃*
        π_ (k + 3) (Sph (2 * n + 1)) (sphereBasepoint (2 * n + 1))) := by
  let e := HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (k + 3))
    (complexProjectiveModelHomeomorphFunction n)
    (complexProjectiveModelHomeomorphFunction_basepoint n)
  obtain ⟨h⟩ := complexProjectiveModel_higher_homotopy_mulEquiv_sphere n k hn
  exact ⟨e.symm.trans h⟩

end Submission
