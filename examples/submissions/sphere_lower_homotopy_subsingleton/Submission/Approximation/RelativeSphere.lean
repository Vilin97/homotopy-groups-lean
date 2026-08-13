/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SpherePairwiseGeneralPosition
import Submission.SphereSuspensionExcision
import Submission.SphereSuspension

/-!
# Piecewise-linear approximation of relative sphere loops

An ordinary radial PL approximation of a map to a sphere need not preserve a closed cap
condition on the cube boundary: normalization can amplify a small negative height.  This file
supplies the relative approximation needed by sphere-cap excision.

First, a based height reparametrization of the suspension model moves the enlarged upper cap into
the closed northern half-sphere.  Its homotopy fixes the distinguished equatorial basepoint and
keeps the cap invariant.  Second, face-specific grid lemmas show that affine interpolation
preserves the resulting nonnegative boundary height and remains exactly constant on the cubical
boundary jar.  Radial projection therefore produces a relative generalized loop and the usual
straight-line approximation homotopy is a relative homotopy.

## Main results

* `Submission.upperCapSqueezeSphereHomotopy_mem_upperCap`
* `Submission.cubeGridAffineApprox_eq_of_mem_boundaryJar`
* `Submission.exists_relativeSpherePLApproximation`
* `Submission.exists_homotopic_relativeSpherePLApproximation`
* `Submission.relHomotopyGroup_exists_relativeSpherePLRepresentative`
-/

open MeasureTheory Module Set
open scoped unitInterval Topology Topology.Homotopy

namespace Submission

variable {d : ℕ}

/-! ### A based squeeze of the upper spherical cap -/

/-- Reparametrize suspension height so every level at least `1/3` moves to a level at least
`1/2`, while the midpoint and both endpoints remain fixed. -/
noncomputable def upperCapSqueezeCoord (t : I) : I :=
  ⟨max (t : ℝ) (min ((3 / 2 : ℝ) * t) (1 / 2)), by
    constructor
    · exact le_trans t.2.1 (le_max_left _ _)
    · exact max_le t.2.2 (le_trans (min_le_right _ _) (by norm_num))⟩

theorem continuous_upperCapSqueezeCoord : Continuous upperCapSqueezeCoord := by
  change Continuous fun t : I =>
    (⟨max (t : ℝ) (min ((3 / 2 : ℝ) * t) (1 / 2)), _⟩ : I)
  fun_prop

@[simp] theorem upperCapSqueezeCoord_zero : upperCapSqueezeCoord 0 = 0 := by
  apply Subtype.ext
  norm_num [upperCapSqueezeCoord]

@[simp] theorem upperCapSqueezeCoord_one : upperCapSqueezeCoord 1 = 1 := by
  apply Subtype.ext
  norm_num [upperCapSqueezeCoord]

@[simp] theorem upperCapSqueezeCoord_midpoint :
    upperCapSqueezeCoord Susp.midpoint = Susp.midpoint := by
  apply Subtype.ext
  norm_num [upperCapSqueezeCoord, Susp.midpoint]

theorem le_upperCapSqueezeCoord (t : I) : t ≤ upperCapSqueezeCoord t :=
  by
    rw [← Subtype.coe_le_coe]
    exact le_max_left _ _

theorem midpoint_le_upperCapSqueezeCoord {t : I} (ht : (1 / 3 : ℝ) ≤ t) :
    Susp.midpoint ≤ upperCapSqueezeCoord t := by
  rw [← Subtype.coe_le_coe]
  change (1 / 2 : ℝ) ≤ max (t : ℝ) (min ((3 / 2 : ℝ) * t) (1 / 2))
  have hmul : (1 / 2 : ℝ) ≤ (3 / 2 : ℝ) * t := by linarith
  rw [min_eq_right hmul]
  exact le_max_right _ _

namespace Susp

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Reparametrize only the height coordinate of an unreduced suspension. -/
def reparam (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1) : C(Susp X, Susp X) :=
  Susp.lift
    ⟨fun p => Susp.mk (r p.1, p.2), Susp.mk.continuous.comp (by fun_prop)⟩
    (fun x y => by
      change Susp.mk (r 0, x) = Susp.mk (r 0, y)
      rw [hzero]
      exact Susp.mk_zero_eq_mk_zero x y)
    (fun x y => by
      change Susp.mk (r 1, x) = Susp.mk (r 1, y)
      rw [hone]
      exact Susp.mk_one_eq_mk_one x y)

@[simp] theorem reparam_mk (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (p : I × X) : reparam r hzero hone (Susp.mk p) = Susp.mk (r p.1, p.2) :=
  rfl

theorem height_reparam (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (q : Susp X) : Susp.height (reparam r hzero hone q) = r (Susp.height q) := by
  induction q using Susp.ind with
  | h p => rfl

/-- The height-reparametrization homotopy, linearly interpolating the old and new interval
coordinates. -/
def reparamHomotopyToFun (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (p : I × Susp X) : Susp X :=
  Quotient.lift
    (fun q : I × X => Susp.mk (Set.Icc.convexComb q.1 (r q.1) p.1, q.2))
    (by
      intro a b hab
      rcases hab with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact congrArg
          (fun q : I × X => Susp.mk (Set.Icc.convexComb q.1 (r q.1) p.1, q.2)) h
      · rw [ha, hb, hzero, Set.Icc.convexComb_eq]
        exact Susp.mk_zero_eq_mk_zero _ _
      · rw [ha, hb, hone, Set.Icc.convexComb_eq]
        exact Susp.mk_one_eq_mk_one _ _)
    p.2

@[simp] theorem reparamHomotopyToFun_mk
    (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (s : I) (p : I × X) :
    reparamHomotopyToFun r hzero hone (s, Susp.mk p) =
      Susp.mk (Set.Icc.convexComb p.1 (r p.1) s, p.2) :=
  rfl

theorem continuous_reparamHomotopyToFun
    (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1) :
    Continuous (reparamHomotopyToFun (X := X) r hzero hone) := by
  refine (Susp.isQuotientMap_mk (X := X)).continuous_lift_prod_right
    (Y := I) (Z := Susp X) ?_
  change Continuous fun p : I × (I × X) =>
    Susp.mk (Set.Icc.convexComb p.2.1 (r p.2.1) p.1, p.2.2)
  fun_prop

/-- Height reparametrization is homotopic to the identity. -/
def reparamHomotopy (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1) :
    ContinuousMap.Homotopy (ContinuousMap.id (Susp X)) (reparam r hzero hone) where
  toFun := reparamHomotopyToFun (X := X) r hzero hone
  continuous_toFun := continuous_reparamHomotopyToFun (X := X) r hzero hone
  map_zero_left q := by
    induction q using Susp.ind with
    | h p => rw [reparamHomotopyToFun_mk, Set.Icc.convexComb_zero]; rfl
  map_one_left q := by
    induction q using Susp.ind with
    | h p => rw [reparamHomotopyToFun_mk, Set.Icc.convexComb_one]; rfl

@[simp] theorem reparamHomotopy_mk
    (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (s : I) (p : I × X) :
    reparamHomotopy r hzero hone (s, Susp.mk p) =
      Susp.mk (Set.Icc.convexComb p.1 (r p.1) s, p.2) :=
  rfl

theorem height_reparamHomotopy
    (r : C(I, I)) (hzero : r 0 = 0) (hone : r 1 = 1)
    (s : I) (q : Susp X) :
    Susp.height (reparamHomotopy r hzero hone (s, q)) =
      Set.Icc.convexComb (Susp.height q) (r (Susp.height q)) s := by
  induction q using Susp.ind with
  | h p => rfl

end Susp

/-- The self-map of `S^(d+1)` induced by the upper-cap height squeeze. -/
noncomputable def upperCapSqueezeSphere (d : ℕ) : C(Sph (d + 1), Sph (d + 1)) :=
  (suspSphHomeo d : C(Susp (Sph d), Sph (d + 1))).comp
    ((Susp.reparam ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
      upperCapSqueezeCoord_zero upperCapSqueezeCoord_one).comp
      (suspSphHomeo d).symm)

/-- The homotopy from the identity sphere map to the upper-cap squeeze. -/
noncomputable def upperCapSqueezeSphereHomotopy (d : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Sph (d + 1))) (upperCapSqueezeSphere d) where
  toFun p := suspSphHomeo d
    (Susp.reparamHomotopy
      ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
      upperCapSqueezeCoord_zero upperCapSqueezeCoord_one
      (p.1, (suspSphHomeo d).symm p.2))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change suspSphHomeo d
      (Susp.reparamHomotopy
        ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
        upperCapSqueezeCoord_zero upperCapSqueezeCoord_one
        (0, (suspSphHomeo d).symm z)) = z
    exact (congrArg (suspSphHomeo d)
      ((Susp.reparamHomotopy _ _ _).map_zero_left ((suspSphHomeo d).symm z))).trans
      ((suspSphHomeo d).apply_symm_apply z)
  map_one_left z := by
    change suspSphHomeo d
      (Susp.reparamHomotopy
        ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
        upperCapSqueezeCoord_zero upperCapSqueezeCoord_one
        (1, (suspSphHomeo d).symm z)) =
      suspSphHomeo d
        (Susp.reparam
          ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
          upperCapSqueezeCoord_zero upperCapSqueezeCoord_one
          ((suspSphHomeo d).symm z))
    exact congrArg (suspSphHomeo d)
      ((Susp.reparamHomotopy _ _ _).map_one_left ((suspSphHomeo d).symm z))

theorem upperCapSqueezeSphereHomotopy_base (d : ℕ) (s : I) :
    upperCapSqueezeSphereHomotopy d (s, sphereBasepoint (d + 1)) =
      sphereBasepoint (d + 1) := by
  change suspSphHomeo d
    (Susp.reparamHomotopy
      ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
      upperCapSqueezeCoord_zero upperCapSqueezeCoord_one
      (s, (suspSphHomeo d).symm (sphereBasepoint (d + 1)))) =
    sphereBasepoint (d + 1)
  rw [suspSphHomeo_symm_sphereBasepoint,
    Susp.reparamHomotopy_mk]
  dsimp only [Prod.fst, Prod.snd, ContinuousMap.coe_mk]
  rw [upperCapSqueezeCoord_midpoint,
    Set.Icc.convexComb_eq, suspSphHomeo_equator_sphereBasepoint]

theorem upperCapSqueezeSphere_boundaryHeightNonneg {z : Sph (d + 1)}
    (hz : z ∈ sphUpperCap d) : 0 ≤ sphHeight (upperCapSqueezeSphere d z) := by
  let q := (suspSphHomeo d).symm z
  have hq : (1 / 3 : ℝ) ≤ Susp.height q := by
    rw [mem_sphUpperCap, sphHeight_eq] at hz
    dsimp [q]
    linarith
  change 0 ≤ sphHeight (suspSphHomeo d
    (Susp.reparam ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
      upperCapSqueezeCoord_zero upperCapSqueezeCoord_one q))
  rw [suspSphHomeo_apply, sphHeight_suspSphLift, Susp.height_reparam]
  have := midpoint_le_upperCapSqueezeCoord hq
  rw [← Subtype.coe_le_coe] at this
  change (1 / 2 : ℝ) ≤ (upperCapSqueezeCoord (Susp.height q) : ℝ) at this
  change 0 ≤ 2 * (upperCapSqueezeCoord (Susp.height q) : ℝ) - 1
  linarith

theorem upperCapSqueezeSphereHomotopy_mem_upperCap {z : Sph (d + 1)}
    (hz : z ∈ sphUpperCap d) (s : I) :
    upperCapSqueezeSphereHomotopy d (s, z) ∈ sphUpperCap d := by
  let q := (suspSphHomeo d).symm z
  have hq : (1 / 3 : ℝ) ≤ Susp.height q := by
    rw [mem_sphUpperCap, sphHeight_eq] at hz
    dsimp [q]
    linarith
  rw [mem_sphUpperCap]
  change -(1 / 3 : ℝ) ≤ sphHeight (suspSphHomeo d
    (Susp.reparamHomotopy
      ⟨upperCapSqueezeCoord, continuous_upperCapSqueezeCoord⟩
      upperCapSqueezeCoord_zero upperCapSqueezeCoord_one (s, q)))
  rw [suspSphHomeo_apply, sphHeight_suspSphLift,
    Susp.height_reparamHomotopy]
  have hle : Susp.height q ≤ upperCapSqueezeCoord (Susp.height q) :=
    le_upperCapSqueezeCoord (Susp.height q)
  have hinterp := Set.Icc.le_convexComb hle s
  rw [← Subtype.coe_le_coe] at hinterp
  change -(1 / 3 : ℝ) ≤ 2 *
    (Set.Icc.convexComb (Susp.height q) (upperCapSqueezeCoord (Susp.height q)) s : ℝ) - 1
  linarith

theorem upperCapSqueezeSphere_base (d : ℕ) :
    upperCapSqueezeSphere d (sphereBasepoint (d + 1)) = sphereBasepoint (d + 1) := by
  rw [← (upperCapSqueezeSphereHomotopy d).map_one_left (sphereBasepoint (d + 1))]
  exact upperCapSqueezeSphereHomotopy_base d 1

/-! ### Grid approximation on prescribed cube faces -/

variable {k N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem gridVertex_eq_zero_of_gridCoeff_pos (hN : 1 ≤ N)
    {v : Fin k → ℕ} {y : I^ Fin k} {j : Fin k}
    (hj : y j = 0) (hv : v ∈ activeVerts N y) : gridVertex N v j = 0 := by
  obtain ⟨hvmem, hvpos⟩ := mem_activeVerts.mp hv
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have habs := abs_lt.mp (abs_sub_lt_one_of_gridCoeff_pos hvpos j)
  have hcoe := coe_gridVertex hN hvmem j
  have hyj : ((y j : I) : ℝ) = 0 := congrArg Subtype.val hj
  rw [hyj, mul_zero] at habs
  have hlt : (v j : ℝ) < 1 := by linarith [habs.1]
  have hv0 : v j = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hlt)
  apply Subtype.ext
  rw [hcoe, hv0]
  simp

theorem gridVertex_eq_one_of_gridCoeff_pos (hN : 1 ≤ N)
    {v : Fin k → ℕ} {y : I^ Fin k} {j : Fin k}
    (hj : y j = 1) (hv : v ∈ activeVerts N y) : gridVertex N v j = 1 := by
  obtain ⟨hvmem, hvpos⟩ := mem_activeVerts.mp hv
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have habs := abs_lt.mp (abs_sub_lt_one_of_gridCoeff_pos hvpos j)
  have hcoe := coe_gridVertex hN hvmem j
  have hyj : ((y j : I) : ℝ) = 1 := congrArg Subtype.val hj
  rw [hyj, mul_one] at habs
  have hlt : (v j : ℝ) < (N : ℝ) + 1 := by linarith [habs.1]
  have hgt : (N : ℝ) - 1 < (v j : ℝ) := by linarith [habs.2]
  have h1' : v j < N + 1 := by exact_mod_cast hlt
  have h2' : N ≤ v j := by
    by_contra hc
    have : (v j : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_le hc)
    linarith
  have hvN : v j = N := by omega
  apply Subtype.ext
  rw [hcoe, hvN, div_self (ne_of_gt hN')]
  simp

theorem gridVertex_mem_boundaryJar_of_gridCoeff_pos (hN : 1 ≤ N)
    {v : Fin (k + 1) → ℕ} {y : I^ Fin (k + 1)}
    (hy : y ∈ ⊔I^(k + 1)) (hv : v ∈ activeVerts N y) :
    gridVertex N v ∈ ⊔I^(k + 1) := by
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hside
  · apply Cube.mem_boundaryJar_of_exists_eq_zero
    refine ⟨Fin.last k, ?_⟩
    apply gridVertex_eq_zero_of_gridCoeff_pos hN _ hv
    simpa [Cube.splitAtLast_fst_eq] using hbot
  · obtain ⟨j, hj⟩ := hside
    apply Cube.mem_boundaryJar_of_lt_last
    refine ⟨j.castSucc, Fin.castSucc_lt_last j, ?_⟩
    rw [Cube.splitAtLast_snd_apply_eq] at hj
    rcases hj with hj | hj
    · exact Or.inl (gridVertex_eq_zero_of_gridCoeff_pos hN hj hv)
    · exact Or.inr (gridVertex_eq_one_of_gridCoeff_pos hN hj hv)

/-- A grid approximation preserves a constant boundary jar exactly. -/
theorem cubeGridAffineApprox_eq_of_mem_boundaryJar (hN : 1 ≤ N)
    (g : C(I^ Fin (k + 1), V)) {b : V}
    (hg : ∀ z ∈ ⊔I^(k + 1), g z = b) {y : I^ Fin (k + 1)}
    (hy : y ∈ ⊔I^(k + 1)) : cubeGridAffineApprox (k + 1) N g y = b := by
  have hval : ∀ v ∈ activeVerts N y, g (gridVertex N v) = b := fun v hv =>
    hg _ (gridVertex_mem_boundaryJar_of_gridCoeff_pos hN hy hv)
  rw [cubeGridAffineApprox_eq_sum_activeVerts,
    Finset.sum_congr rfl (fun v hv => by rw [hval v hv]), ← Finset.sum_smul,
    sum_gridCoeff_activeVerts hN, one_smul]

/-! ### Half-space control on the full cube boundary -/

variable {d : ℕ}

/-- If the values of a sphere map on the cube boundary have nonnegative last coordinate, then
the ambient grid approximation has nonnegative last coordinate there as well. -/
theorem cubeGridAffineApprox_last_nonneg_of_mem_boundary
    (hN : 1 ≤ N)
    (g : C(I^ Fin (k + 1), EuclideanSpace ℝ (Fin (d + 2))))
    (hg : ∀ z ∈ ∂I^(k + 1),
      0 ≤ g z (Fin.last (d + 1)))
    {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApprox (k + 1) N g y (Fin.last (d + 1)) := by
  obtain ⟨j, hj⟩ := hy
  rw [cubeGridAffineApprox_eq_sum_activeVerts]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ), map_sum]
  simp only [map_smul, PiLp.projₗ_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun v hv => mul_nonneg gridCoeff_nonneg
    (hg _ (gridVertex_mem_boundary_of_gridCoeff_pos hN
      hj hv))

theorem radialProj_last_nonneg {v : EuclideanSpace ℝ (Fin (d + 2))}
    (hv : 0 ≤ v (Fin.last (d + 1))) :
    0 ≤ radialProj v (Fin.last (d + 1)) := by
  rw [radialProj, PiLp.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) hv

/-! ### Relative loops with a strict cap margin -/

/-- A relative sphere loop, read as a continuous map into its ambient Euclidean space. -/
noncomputable def relGenLoopToEuclidean
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    C(I^ Fin (k + 1), EuclideanSpace ℝ (Fin (d + 2))) :=
  ⟨fun y => ((p.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))),
    continuous_subtype_val.comp p.val.continuous⟩

@[simp] theorem relGenLoopToEuclidean_apply
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (y : I^ Fin (k + 1)) :
    relGenLoopToEuclidean p y =
      ((p.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) :=
  rfl

/-- The useful strict form of the relative boundary condition: the whole boundary maps into the
closed northern half-sphere. -/
def RelGenLoop.BoundaryHeightNonneg
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) : Prop :=
  ∀ y ∈ ∂I^(k + 1), 0 ≤ sphHeight (p.val y)

/-- Apply the upper-cap squeeze to a relative sphere loop. -/
noncomputable def upperCapSqueezeRelGenLoop
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨(upperCapSqueezeSphere d).comp p.val,
    ⟨fun y hy => by
        have hnonneg := upperCapSqueezeSphere_boundaryHeightNonneg (p.property.1 y hy)
        rw [mem_sphUpperCap]
        exact le_trans (by norm_num) hnonneg,
      fun y hy => by
        rw [ContinuousMap.comp_apply, p.property.2 y hy]
        exact upperCapSqueezeSphere_base d⟩⟩

theorem upperCapSqueezeRelGenLoop_boundaryHeightNonneg
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    RelGenLoop.BoundaryHeightNonneg (upperCapSqueezeRelGenLoop p) := by
  intro y hy
  exact upperCapSqueezeSphere_boundaryHeightNonneg (p.property.1 y hy)

/-- The upper-cap squeeze does not change the relative homotopy class. -/
theorem relGenLoopHomotopic_upperCapSqueeze
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    RelGenLoop.Homotopic p (upperCapSqueezeRelGenLoop p) := by
  refine ⟨⟨⟨fun sy => upperCapSqueezeSphereHomotopy d (sy.1, p.val sy.2), by fun_prop⟩,
    fun y => ?_, fun y => ?_⟩, fun s => ?_⟩
  · change upperCapSqueezeSphereHomotopy d (0, p.val y) = p.val y
    exact (upperCapSqueezeSphereHomotopy d).map_zero_left (p.val y)
  · change upperCapSqueezeSphereHomotopy d (1, p.val y) =
      upperCapSqueezeSphere d (p.val y)
    exact (upperCapSqueezeSphereHomotopy d).map_one_left (p.val y)
  · constructor
    · intro y hy
      exact upperCapSqueezeSphereHomotopy_mem_upperCap (p.property.1 y hy) s
    · intro y hy
      change upperCapSqueezeSphereHomotopy d (s, p.val y) =
        (sphUpperCapBase d : Sph (d + 1))
      rw [p.property.2 y hy]
      exact upperCapSqueezeSphereHomotopy_base d s

theorem cubeGridAffineApprox_relGenLoop_last_nonneg
    (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p) {y : I^ Fin (k + 1)}
    (hy : y ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y
      (Fin.last (d + 1)) :=
  cubeGridAffineApprox_last_nonneg_of_mem_boundary hN _
    (fun z hz => hp z hz) hy

theorem cubeGridAffineApprox_relGenLoop_eq_on_boundaryJar
    (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) := by
  apply cubeGridAffineApprox_eq_of_mem_boundaryJar hN
    (relGenLoopToEuclidean p) _ hy
  intro z hz
  exact congrArg Subtype.val (p.property.2 z hz)

/-- Radial projection of a grid approximation with strict boundary margin, bundled again as a
relative generalized loop of the sphere/upper-cap pair. -/
noncomputable def radialCubeGridAffineApproxRelGenLoop
    (N : ℕ) (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (hne : ∀ y, cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y ≠ 0) :
    RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d) :=
  ⟨⟨fun y =>
      ⟨radialProj (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y),
        mem_sphere_zero_iff_norm.mpr (norm_radialProj (hne y))⟩,
    Continuous.subtype_mk
      (continuous_radialProj
        (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p)).continuous hne) _⟩,
    ⟨fun y hy => by
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤
          radialProj (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y)
            (Fin.last (d + 1))
        exact le_trans (by norm_num)
          (radialProj_last_nonneg
            (cubeGridAffineApprox_relGenLoop_last_nonneg hN p hp hy)),
      fun y hy => Subtype.ext (by
        change radialProj (cubeGridAffineApprox (k + 1) N
          (relGenLoopToEuclidean p) y) =
            ((sphereBasepoint (d + 1) : Sph (d + 1)) :
              EuclideanSpace ℝ (Fin (d + 2)))
        rw [cubeGridAffineApprox_relGenLoop_eq_on_boundaryJar hN p hy]
        exact radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1))))⟩⟩

@[simp] theorem coe_radialCubeGridAffineApproxRelGenLoop
    (N : ℕ) (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (hne : ∀ y, cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y ≠ 0)
    (y : I^ Fin (k + 1)) :
    (((radialCubeGridAffineApproxRelGenLoop N hN p hp hne).val y : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (cubeGridAffineApprox (k + 1) N (relGenLoopToEuclidean p) y) :=
  rfl

theorem cubeGridAffineApproxHomotopy_relGenLoop_last_nonneg
    (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ∂I^(k + 1)) :
    0 ≤ cubeGridAffineApproxHomotopy (k + 1) N (relGenLoopToEuclidean p) (s, y)
      (Fin.last (d + 1)) := by
  rw [cubeGridAffineApproxHomotopy_apply]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ),
    map_add, map_smul, map_smul]
  simp only [PiLp.projₗ_apply, smul_eq_mul]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr s.2.2) (hp y hy))
    (mul_nonneg s.2.1 (cubeGridAffineApprox_relGenLoop_last_nonneg hN p hp hy))

theorem cubeGridAffineApproxHomotopy_relGenLoop_eq_on_boundaryJar
    (hN : 1 ≤ N)
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (s : I) {y : I^ Fin (k + 1)} (hy : y ∈ ⊔I^(k + 1)) :
    cubeGridAffineApproxHomotopy (k + 1) N (relGenLoopToEuclidean p) (s, y) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) := by
  rw [cubeGridAffineApproxHomotopy_apply,
    show relGenLoopToEuclidean p y =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) from
        congrArg Subtype.val (p.property.2 y hy),
    cubeGridAffineApprox_relGenLoop_eq_on_boundaryJar hN p hy, ← add_smul]
  norm_num

/-- Finite PL approximation data for a relative sphere loop whose boundary has been moved into
the closed northern half-sphere. -/
structure RelativeSpherePLApproximation
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p) where
  mesh : ℕ
  mesh_pos : 1 ≤ mesh
  approx : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)
  dist_le_half : ∀ y, dist
    (cubeGridAffineApprox (k + 1) mesh (relGenLoopToEuclidean p) y)
    (relGenLoopToEuclidean p y) ≤ 1 / 2
  approx_ne_zero : ∀ y,
    cubeGridAffineApprox (k + 1) mesh (relGenLoopToEuclidean p) y ≠ 0
  coe_approx : ∀ y,
    ((approx.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2))) =
      radialProj (cubeGridAffineApprox (k + 1) mesh (relGenLoopToEuclidean p) y)
  homotopic : RelGenLoop.Homotopic p approx

/-- Every relative sphere loop whose whole boundary has nonnegative height has a finite radial
PL representative in the same relative homotopy class. -/
theorem exists_relativeSpherePLApproximation
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p) :
    Nonempty (RelativeSpherePLApproximation p hp) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  let F := relGenLoopToEuclidean p
  have hFnorm : ∀ y, ‖F y‖ = 1 := fun y => norm_coe_sph (p.val y)
  obtain ⟨N, hN, hdist⟩ := exists_cubeGridAffineApprox_dist_le (k + 1) F hhalf
  have hHdist : ∀ (s : I) (y : I^ Fin (k + 1)),
      dist (cubeGridAffineApproxHomotopy (k + 1) N F (s, y)) (F y) ≤ 1 / 2 :=
    fun s y => cubeGridAffineApproxHomotopy_dist_le F hdist s y
  have hHne : ∀ q : I × I^ Fin (k + 1),
      cubeGridAffineApproxHomotopy (k + 1) N F q ≠ 0 := by
    rintro ⟨s, y⟩ hzero
    have h := hHdist s y
    rw [hzero, dist_zero_left, hFnorm] at h
    linarith
  have hGne : ∀ y : I^ Fin (k + 1),
      cubeGridAffineApprox (k + 1) N F y ≠ 0 := by
    intro y
    have h := hHne (1, y)
    rwa [cubeGridAffineApproxHomotopy_one] at h
  let q := radialCubeGridAffineApproxRelGenLoop N hN p hp hGne
  have hhom : RelGenLoop.Homotopic p q := by
    refine ⟨⟨⟨fun sy =>
        ⟨radialProj (cubeGridAffineApproxHomotopy (k + 1) N F sy),
          mem_sphere_zero_iff_norm.mpr (norm_radialProj (hHne sy))⟩,
        Continuous.subtype_mk
          (continuous_radialProj
            (cubeGridAffineApproxHomotopy (k + 1) N F).continuous hHne) _⟩,
      fun y => ?_, fun y => ?_⟩, fun s => ?_⟩
    · apply Subtype.ext
      change radialProj (cubeGridAffineApproxHomotopy (k + 1) N F (0, y)) =
        ((p.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
      rw [cubeGridAffineApproxHomotopy_zero]
      exact radialProj_of_norm_eq_one (hFnorm y)
    · apply Subtype.ext
      change radialProj (cubeGridAffineApproxHomotopy (k + 1) N F (1, y)) =
        ((q.val y : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
      rw [cubeGridAffineApproxHomotopy_one]
      rfl
    · constructor
      · intro y hy
        rw [mem_sphUpperCap]
        change -(1 / 3 : ℝ) ≤
          radialProj (cubeGridAffineApproxHomotopy (k + 1) N F (s, y))
            (Fin.last (d + 1))
        exact le_trans (by norm_num)
          (radialProj_last_nonneg
            (cubeGridAffineApproxHomotopy_relGenLoop_last_nonneg hN p hp s hy))
      · intro y hy
        apply Subtype.ext
        change radialProj (cubeGridAffineApproxHomotopy (k + 1) N F (s, y)) =
          ((sphereBasepoint (d + 1) : Sph (d + 1)) : EuclideanSpace ℝ (Fin (d + 2)))
        rw [cubeGridAffineApproxHomotopy_relGenLoop_eq_on_boundaryJar hN p s hy]
        exact radialProj_of_norm_eq_one (norm_coe_sph (sphereBasepoint (d + 1)))
  exact ⟨⟨N, hN, q, hdist, hGne, fun _ => rfl, hhom⟩⟩

/-- Every relative sphere loop is homotopic to a finite radial PL representative which preserves
the upper-cap boundary condition and fixes the boundary jar exactly. -/
theorem exists_homotopic_relativeSpherePLApproximation
    (p : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ (q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
      (hq : RelGenLoop.BoundaryHeightNonneg q)
      (A : RelativeSpherePLApproximation q hq),
      RelGenLoop.Homotopic p A.approx := by
  let q := upperCapSqueezeRelGenLoop p
  let hq : RelGenLoop.BoundaryHeightNonneg q :=
    upperCapSqueezeRelGenLoop_boundaryHeightNonneg p
  obtain ⟨A⟩ := exists_relativeSpherePLApproximation q hq
  exact ⟨q, hq, A, (relGenLoopHomotopic_upperCapSqueeze p).trans A.homotopic⟩

/-- Every relative homotopy class of the sphere/upper-cap pair has a cap-safe finite PL
representative. -/
theorem relHomotopyGroup_exists_relativeSpherePLRepresentative
    (a : π_rel (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d)) :
    ∃ (q : RelGenLoop (k + 1) (Sph (d + 1)) (sphUpperCap d) (sphUpperCapBase d))
      (hq : RelGenLoop.BoundaryHeightNonneg q)
      (A : RelativeSpherePLApproximation q hq),
      a = ⟦A.approx⟧ := by
  induction a using Quotient.inductionOn with
  | h p =>
      obtain ⟨q, hq, A, hA⟩ := exists_homotopic_relativeSpherePLApproximation p
      exact ⟨q, hq, A, Quotient.sound hA⟩

end Submission
