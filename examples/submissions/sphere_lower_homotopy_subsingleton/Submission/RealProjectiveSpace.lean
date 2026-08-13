/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Covering.Quotient
import Submission.ForMathlib.HomotopyGroup.Covering
import Submission.Model.SphereConnected

/-!
# The sphere cover of real projective space

This file identifies the concrete quotient-topology model of real projective space used by the
benchmark with the antipodal quotient of the unit sphere.  The resulting two-sheeted covering
computes its fundamental group and identifies all of its higher homotopy groups with those of the
sphere.
-/

noncomputable section

open Topology
open scoped Topology

namespace Submission

/-- The quotient-topology real projective `n`-space, independently of any benchmark namespace. -/
abbrev RealProjectiveModel (n : ℕ) :=
  Projectivization ℝ (Fin (n + 1) → ℝ)

noncomputable instance instTopologicalSpaceRealProjectiveModel (n : ℕ) :
    TopologicalSpace (RealProjectiveModel n) := by
  unfold RealProjectiveModel Projectivization
  infer_instance

/-- The line through the first coordinate vector. -/
def realProjectiveModelBasepoint (n : ℕ) : RealProjectiveModel n :=
  Projectivization.mk ℝ (Pi.single 0 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)

/-- The first coordinate vector on the unit sphere. -/
def sphereModelBasepoint (n : ℕ) : Sph n :=
  ⟨EuclideanSpace.single 0 1, by
    rw [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩

abbrev RealSphereDeckGroup := rootsOfUnity 2 ℝ

/-- Every real square root of `1` has norm `1`. -/
private theorem norm_coe_realSphereDeckGroup (g : RealSphereDeckGroup) :
    ‖(((g : ℝˣ) : ℝ))‖ = 1 := by
  have hg : (((g : ℝˣ) : ℝ)) ^ 2 = 1 :=
    (mem_rootsOfUnity' 2 (g : ℝˣ)).mp g.2
  rcases sq_eq_one_iff.mp hg with h | h <;> simp [h]

/-- The unit sphere is invariant under the two real square roots of unity. -/
private def realSphereSubMulAction (n : ℕ) :
    SubMulAction RealSphereDeckGroup (EuclideanSpace ℝ (Fin (n + 1))) where
  carrier := Metric.sphere 0 1
  smul_mem' g x hx := by
    change (((g : ℝˣ) : ℝ) • x) ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_coe_realSphereDeckGroup, one_mul]
    simpa [Metric.mem_sphere, dist_zero_right] using hx

noncomputable instance instMulActionRealSphereDeckGroup (n : ℕ) :
    MulAction RealSphereDeckGroup (Sph n) :=
  (realSphereSubMulAction n).mulAction

noncomputable instance instContinuousConstSMulRealSphereDeckGroup (n : ℕ) :
    ContinuousConstSMul RealSphereDeckGroup (Sph n) where
  continuous_const_smul g := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun x : Sph n ↦ ((g : ℝˣ) : ℝ) •
      (x : EuclideanSpace ℝ (Fin (n + 1)))
    exact continuous_subtype_val.const_smul (((g : ℝˣ) : ℝ))

noncomputable instance instIsCancelSMulRealSphereDeckGroup (n : ℕ) :
    IsCancelSMul RealSphereDeckGroup (Sph n) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hgx
  apply (rootsOfUnity.coe_injective (M := ℝ) (n := 2))
  have hx : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    intro hzero
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  apply (smul_left_injective ℝ (m := (x : EuclideanSpace ℝ (Fin (n + 1)))) hx)
  have hval := congrArg Subtype.val hgx
  change (((g : ℝˣ) : ℝ) • (x : EuclideanSpace ℝ (Fin (n + 1)))) =
    (x : EuclideanSpace ℝ (Fin (n + 1))) at hval
  simpa only [Subgroup.coe_one, Units.val_one, one_smul] using hval

private theorem sphereVector_ne_zero {n : ℕ} (x : Sph n) :
    (fun i ↦ x.1 i) ≠ (0 : Fin (n + 1) → ℝ) := by
  intro h
  have hx : (x.1 : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
    refine PiLp.ext fun i ↦ ?_
    simpa using congrFun h i
  have hnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2
  rw [hx, norm_zero] at hnorm
  norm_num at hnorm

/-- The canonical map from the unit sphere to real projective space. -/
def realProjectiveCover (n : ℕ) : C(Sph n, RealProjectiveModel n) where
  toFun x := Projectivization.mk ℝ (fun i ↦ x.1 i) (sphereVector_ne_zero x)
  continuous_toFun := by
    apply continuous_quotient_mk'.comp
    exact Continuous.subtype_mk
      (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) ↦ ℝ) |>.comp continuous_subtype_val) _

private abbrev NonzeroRealVector (n : ℕ) :=
  {v : Fin (n + 1) → ℝ // v ≠ 0}

/-- Radially normalize a nonzero real vector to the unit sphere. -/
private def normalizeToSphere (n : ℕ) : C(NonzeroRealVector n, Sph n) where
  toFun v := ⟨NormedSpace.normalize (WithLp.toLp 2 v.1), by
    rw [Metric.mem_sphere, dist_zero_right, NormedSpace.norm_normalize]
    exact fun h ↦ v.2 ((WithLp.toLp_eq_zero 2).mp h)⟩
  continuous_toFun := by
    have hv : Continuous fun v : NonzeroRealVector n ↦ WithLp.toLp 2 v.1 :=
      (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp continuous_subtype_val
    refine Continuous.subtype_mk ?_ _
    exact (hv.norm.inv₀ fun v h ↦ v.2 <| (WithLp.toLp_eq_zero 2).mp <| norm_eq_zero.mp h).smul hv

private theorem realProjectiveCover_normalizeToSphere (n : ℕ) (v : NonzeroRealVector n) :
    realProjectiveCover n (normalizeToSphere n v) = Projectivization.mk ℝ v.1 v.2 := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨‖WithLp.toLp 2 v.1‖⁻¹, ?_⟩
  funext i
  simp [normalizeToSphere, NormedSpace.normalize]

/-- The canonical sphere-to-projective-space map is a quotient map. -/
theorem realProjectiveCover_isQuotientMap (n : ℕ) :
    IsQuotientMap (realProjectiveCover n) := by
  let q : NonzeroRealVector n → RealProjectiveModel n := Projectivization.mk' ℝ
  have hq : IsQuotientMap q := by
    change IsQuotientMap
      (@Quotient.mk' (NonzeroRealVector n)
        (projectivizationSetoid ℝ (Fin (n + 1) → ℝ)))
    exact isQuotientMap_quotient_mk'
  have hcomp : (realProjectiveCover n : Sph n → RealProjectiveModel n) ∘
      normalizeToSphere n = q := by
    funext v
    simpa [q] using realProjectiveCover_normalizeToSphere n v
  exact IsQuotientMap.of_comp (normalizeToSphere n).continuous (realProjectiveCover n).continuous
    (hcomp ▸ hq)

/-- Two unit vectors determine the same real projective point exactly when they differ by a real
square root of unity. -/
theorem realProjectiveCover_eq_iff_mem_orbit (n : ℕ) (x y : Sph n) :
    realProjectiveCover n x = realProjectiveCover n y ↔
      x ∈ MulAction.orbit RealSphereDeckGroup y := by
  constructor
  · intro h
    change Projectivization.mk ℝ (fun i ↦ x.1 i) (sphereVector_ne_zero x) =
      Projectivization.mk ℝ (fun i ↦ y.1 i) (sphereVector_ne_zero y) at h
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff ℝ _ _ (sphereVector_ne_zero x)
        (sphereVector_ne_zero y)).mp h
    have hvec : ((a : ℝ) • (y.1 : EuclideanSpace ℝ (Fin (n + 1)))) = x.1 := by
      refine PiLp.ext fun i ↦ ?_
      simpa [Units.smul_def] using congrFun ha i
    have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.2
    have hynorm : ‖(y.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using y.2
    have hanorm : ‖(a : ℝ)‖ = 1 := by
      have hn := congrArg norm hvec
      simpa [norm_smul, hxnorm, hynorm] using hn
    have hasq : (a : ℝ) ^ 2 = 1 := by
      have habs : |(a : ℝ)| = 1 := by simpa [Real.norm_eq_abs] using hanorm
      nlinarith [sq_abs (a : ℝ)]
    have hapow : a ^ 2 = 1 := by
      apply Units.ext
      simpa using hasq
    let g : RealSphereDeckGroup := ⟨a, hapow⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change ((a : ℝ) • (y.1 : EuclideanSpace ℝ (Fin (n + 1)))) = x.1
    exact hvec
  · rintro ⟨g, hg⟩
    change Projectivization.mk ℝ (fun i ↦ x.1 i) (sphereVector_ne_zero x) =
      Projectivization.mk ℝ (fun i ↦ y.1 i) (sphereVector_ne_zero y)
    apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
    refine ⟨(g : ℝˣ), ?_⟩
    have hval := congrArg Subtype.val hg
    change (((g : ℝˣ) : ℝ) • (y.1 : EuclideanSpace ℝ (Fin (n + 1)))) = x.1 at hval
    funext i
    simpa [Units.smul_def] using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i) hval

/-- The antipodal sphere projection is a two-sheeted quotient covering map. -/
theorem realProjectiveCover_isQuotientCoveringMap (n : ℕ) :
    IsQuotientCoveringMap (realProjectiveCover n) RealSphereDeckGroup :=
  (realProjectiveCover_isQuotientMap n).isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (fun {x y} ↦ realProjectiveCover_eq_iff_mem_orbit n x y)

@[simp]
theorem realProjectiveCover_sphereModelBasepoint (n : ℕ) :
    realProjectiveCover n (sphereModelBasepoint n) = realProjectiveModelBasepoint n := by
  rfl

/-- The real two-element deck group is cyclic of order two. -/
noncomputable def realSphereDeckGroupMulEquivZModTwo :
    RealSphereDeckGroup ≃* Multiplicative (ZMod 2) := by
  have hprimitive : IsPrimitiveRoot (-1 : ℝ) 2 :=
    IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hcard : Nat.card RealSphereDeckGroup = 2 := hprimitive.card_rootsOfUnity
  let e := zmodCyclicMulEquiv (G := RealSphereDeckGroup)
    (inferInstance : IsCyclic RealSphereDeckGroup)
  rw [hcard] at e
  exact e.symm

/-- Higher homotopy groups of real projective space are those of its sphere cover. -/
theorem realProjectiveModel_higher_homotopy_mulEquiv_sphere (n k : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) (RealProjectiveModel n) (realProjectiveModelBasepoint n) ≃*
        HomotopyGroup.Pi (k + 2) (Sph n) (sphereModelBasepoint n)) := by
  rw [← realProjectiveCover_sphereModelBasepoint n]
  exact ⟨(HomotopyGroup.coveringMulEquiv
    (realProjectiveCover_isQuotientCoveringMap n).isCoveringMap
    (sphereModelBasepoint n)).symm⟩

/-- For `n ≥ 2`, the fundamental group of real projective `n`-space is cyclic of order two. -/
theorem piOne_realProjectiveModel_mulEquiv_zmod_two (n : ℕ) (hn : 2 ≤ n) :
    Nonempty
      (HomotopyGroup.Pi 1 (RealProjectiveModel n) (realProjectiveModelBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  letI : SimplyConnectedSpace (Sph n) := simplyConnectedSpace_sph_of_two_le hn
  let e : (realProjectiveCover n : Sph n → RealProjectiveModel n) ⁻¹'
      {realProjectiveModelBasepoint n} :=
    ⟨sphereModelBasepoint n, by simp⟩
  exact ⟨HomotopyGroup.pi1MulEquivFundamentalGroup |>.trans
    ((realProjectiveCover_isQuotientCoveringMap n).fundamentalGroupEquiv e) |>.trans
    (MulOpposite.opMulEquiv (M := RealSphereDeckGroup)).symm |>.trans
    realSphereDeckGroupMulEquivZModTwo⟩

end Submission
