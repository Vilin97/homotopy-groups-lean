/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import ChallengeDeps
import Submission.Model.Sphere
import Submission.WhiteheadTheorem.Shapes.DiskHomeoCube

/-!
# A canonical cubical generator for a metric sphere

We map the closed `n`-disk onto `Sⁿ` by the standard quadratic folding map

`v ↦ (2 ‖v‖² - 1, 2 √(1 - ‖v‖²) v)`.

Its whole boundary is the benchmark basepoint `(1, 0, ..., 0)`.  Transporting along the
disk--cube homeomorphism therefore gives a generalized `n`-loop in the exact metric-sphere model
used by the lattice.  This is the geometric map needed to compare cubical homotopy classes with
homological degree.
-/

open scoped Topology Topology.Homotopy TopCat unitInterval

noncomputable section

namespace Submission

open HomotopyGroups

/-- Prepend one coordinate to a Euclidean vector. -/
noncomputable def consLp {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons a (WithLp.ofLp v))

@[simp]
theorem consLp_zero {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    consLp a v 0 = a := by
  simp [consLp]

@[simp]
theorem consLp_succ {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    consLp a v i.succ = v i := by
  simp [consLp]

/-- The squared Euclidean norm after prepending a coordinate. -/
theorem norm_consLp_sq {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖consLp a v‖ ^ 2 = a ^ 2 + ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp

/-- Prepending a coordinate is continuous in both inputs. -/
theorem continuous_consLp {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => consLp p.1 p.2) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp (continuous_pi fun i => ?_)
  induction i using Fin.cases with
  | zero => simpa [consLp] using continuous_fst
  | succ i =>
      simpa [consLp] using
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp' continuous_snd

/-- Every Euclidean vector splits into its first coordinate and its remaining coordinates. -/
theorem eq_consLp {n : ℕ} (z : EuclideanSpace ℝ (Fin (n + 1))) :
    z = consLp (z 0) (WithLp.toLp 2 fun i : Fin n => z i.succ) := by
  apply PiLp.ext
  intro i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- The first coordinate and the tail of a point on `Sⁿ` satisfy the unit-sphere equation. -/
theorem sphere_first_tail_norm_sq {n : ℕ} (z : Sph n) :
    (z.val 0) ^ 2 + ‖WithLp.toLp 2 (fun i : Fin n => z.val i.succ)‖ ^ 2 = 1 := by
  have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  rw [← norm_consLp_sq, ← eq_consLp z.val, hz]
  norm_num

/-- The ambient vector underlying the standard disk-to-sphere quotient map. -/
noncomputable def diskSphereFun (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  let v : EuclideanSpace ℝ (Fin n) := x.val
  consLp (2 * ‖v‖ ^ 2 - 1) ((2 * √(1 - ‖v‖ ^ 2) : ℝ) • v)

/-- The disk-to-sphere formula has unit norm. -/
theorem norm_diskSphereFun (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖diskSphereFun n x‖ = 1 := by
  let v : EuclideanSpace ℝ (Fin n) := x.val
  have hv : ‖v‖ ≤ 1 := by
    have hmem := x.property
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have hrad : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith
  apply norm_eq_one_of_norm_sq_eq_one
  rw [diskSphereFun, norm_consLp_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  change (2 * ‖v‖ ^ 2 - 1) ^ 2 +
    (2 * √(1 - ‖v‖ ^ 2)) ^ 2 * ‖v‖ ^ 2 = 1
  nlinarith [Real.sq_sqrt hrad]

/-- The standard continuous quotient map from the ordinary closed `n`-disk to the metric
`n`-sphere. -/
noncomputable def closedDiskToSphere (n : ℕ) :
    C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, Sph n) where
  toFun x := ⟨diskSphereFun n x,
    mem_sphere_zero_iff_norm.mpr (norm_diskSphereFun n x)⟩
  continuous_toFun := by
    have hv : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => (x.val : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val
    have hr : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => ‖x.val‖) := hv.norm
    have hsqrt : Continuous (fun x : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) 1 => √(1 - ‖x.val‖ ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hr.pow 2))
    refine Continuous.subtype_mk (continuous_consLp.comp (Continuous.prodMk ?_ ?_)) _
    · exact (continuous_const.mul (hr.pow 2)).sub continuous_const
    · exact (continuous_const.mul hsqrt).smul hv

/-- Every boundary point of the ordinary disk is sent to the benchmark's first-coordinate
basepoint. -/
theorem closedDiskToSphere_boundary (n : ℕ)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (hx : ‖x.val‖ = 1) :
    closedDiskToSphere n x = sphereBasepoint n := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  induction i using Fin.cases with
  | zero => norm_num [closedDiskToSphere, diskSphereFun, hx, sphereBasepoint]
  | succ i => simp [closedDiskToSphere, diskSphereFun, hx, sphereBasepoint]

/-- In every positive dimension, the disk-to-sphere quotient map is surjective. -/
theorem closedDiskToSphere_surjective (n : ℕ) :
    Function.Surjective (closedDiskToSphere (n + 1)) := by
  intro z
  let a : ℝ := z.val 0
  let w : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 fun i : Fin (n + 1) => z.val i.succ
  have hnorm : a ^ 2 + ‖w‖ ^ 2 = 1 := sphere_first_tail_norm_sq z
  have ha_sq : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
  have habs : |a| ≤ 1 := (sq_le_one_iff_abs_le_one a).mp ha_sq
  have ha_lower : -1 ≤ a := (abs_le.mp habs).1
  have ha_upper : a ≤ 1 := (abs_le.mp habs).2
  by_cases ha : a = 1
  · have hw_norm : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    have hw : w = 0 := norm_eq_zero.mp hw_norm
    have hzbase : z = sphereBasepoint (n + 1) := by
      apply Subtype.ext
      rw [eq_consLp z.val]
      apply PiLp.ext
      intro i
      induction i using Fin.cases with
      | zero => simp [a, ha, sphereBasepoint]
      | succ i => simp [w, hw, sphereBasepoint]
    let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
    have hv : ‖v‖ = 1 := by simp [v]
    let x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      ⟨v, by rw [Metric.mem_closedBall, dist_zero_right, hv]⟩
    refine ⟨x, ?_⟩
    rw [closedDiskToSphere_boundary (n + 1) x hv, hzbase]
  · have halt : a < 1 := lt_of_le_of_ne ha_upper ha
    let r2 : ℝ := (a + 1) / 2
    let s2 : ℝ := 1 - r2
    let c : ℝ := 2 * √s2
    have hr2_nonneg : 0 ≤ r2 := by dsimp [r2]; linarith
    have hr2_le_one : r2 ≤ 1 := by dsimp [r2]; linarith
    have hs2_pos : 0 < s2 := by dsimp [s2, r2]; linarith
    have hc_pos : 0 < c := mul_pos (by norm_num) (Real.sqrt_pos.2 hs2_pos)
    have hw_sq : ‖w‖ ^ 2 = 1 - a ^ 2 := by nlinarith
    have hc_sq : c ^ 2 = 4 * s2 := by
      dsimp [c]
      rw [mul_pow, Real.sq_sqrt hs2_pos.le]
      ring
    let v : EuclideanSpace ℝ (Fin (n + 1)) := c⁻¹ • w
    have hv_sq : ‖v‖ ^ 2 = r2 := by
      rw [show ‖v‖ = c⁻¹ * ‖w‖ by
        unfold v
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc_pos)]]
      field_simp [hc_pos.ne']
      dsimp [r2, s2] at hc_sq ⊢
      nlinarith
    have hv_le : ‖v‖ ≤ 1 :=
      (sq_le_one_iff₀ (norm_nonneg v)).mp (hv_sq.trans_le hr2_le_one)
    let x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
      ⟨v, by rw [Metric.mem_closedBall, dist_zero_right]; exact hv_le⟩
    have hfirst : 2 * ‖v‖ ^ 2 - 1 = a := by
      rw [hv_sq]
      dsimp [r2]
      ring
    have htail : (2 * √(1 - ‖v‖ ^ 2) : ℝ) • v = w := by
      rw [hv_sq]
      change c • v = w
      rw [show v = c⁻¹ • w by rfl, smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change diskSphereFun (n + 1) x = z.val
    rw [eq_consLp z.val]
    change consLp (2 * ‖v‖ ^ 2 - 1) ((2 * √(1 - ‖v‖ ^ 2) : ℝ) • v) =
      consLp a w
    rw [hfirst, htail]

/-- The only nontrivial fibres of the disk-to-sphere map are on the collapsed boundary. -/
theorem closedDiskToSphere_eq_iff (n : ℕ)
    (x y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    closedDiskToSphere n x = closedDiskToSphere n y ↔
      x = y ∨ (‖x.val‖ = 1 ∧ ‖y.val‖ = 1) := by
  constructor
  · intro h
    have hvec : diskSphereFun n x = diskSphereFun n y := congrArg Subtype.val h
    have hfirst := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z 0) hvec
    have hsq : ‖x.val‖ ^ 2 = ‖y.val‖ ^ 2 := by
      simpa [diskSphereFun] using (show
        2 * ‖x.val‖ ^ 2 - 1 = 2 * ‖y.val‖ ^ 2 - 1 from hfirst)
    have hnorm : ‖x.val‖ = ‖y.val‖ :=
      eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _) hsq
    by_cases hx : ‖x.val‖ = 1
    · exact Or.inr ⟨hx, hnorm ▸ hx⟩
    · left
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.succ) hvec
      have hxle : ‖x.val‖ ≤ 1 := by
        have hmem := x.property
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      have hxlt : ‖x.val‖ < 1 := lt_of_le_of_ne hxle hx
      have hrad : 0 < 1 - ‖x.val‖ ^ 2 := by nlinarith [norm_nonneg x.val]
      have hc : (2 * √(1 - ‖x.val‖ ^ 2) : ℝ) ≠ 0 :=
        (mul_pos (by norm_num) (Real.sqrt_pos.2 hrad)).ne'
      simp only [diskSphereFun, consLp_succ, PiLp.smul_apply, smul_eq_mul] at hi
      rw [← hnorm] at hi
      exact mul_left_cancel₀ hc hi
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [closedDiskToSphere_boundary n x hx, closedDiskToSphere_boundary n y hy]

/-- The disk-to-sphere quotient map on Mathlib's universe-lifted disk model. -/
noncomputable def diskToSphere (n : ℕ) : C(TopCat.disk.{0} n, Sph n) :=
  closedDiskToSphere n |>.comp ⟨ULift.down, continuous_uliftDown⟩

/-- The universe-lifted disk boundary is also collapsed to the benchmark basepoint. -/
theorem diskToSphere_boundary (n : ℕ) (x : TopCat.disk.{0} n) (hx : ‖x.down.val‖ = 1) :
    diskToSphere n x = sphereBasepoint n :=
  closedDiskToSphere_boundary n x.down hx

/-- The disk-to-sphere map on Mathlib's lifted disk is surjective in positive dimensions. -/
theorem diskToSphere_surjective (n : ℕ) : Function.Surjective (diskToSphere (n + 1)) := by
  intro z
  obtain ⟨x, hx⟩ := closedDiskToSphere_surjective n z
  exact ⟨ULift.up x, hx⟩

/-- The inverse disk--cube homeomorphism sends the cube boundary to the disk boundary. -/
theorem norm_diskHomeoCube_symm_eq_one_of_mem_boundary (n : ℕ) (y : I^ Fin n)
    (hy : y ∈ Cube.boundary (Fin n)) :
    ‖((TopCat.diskHomeoCube.{0} n).symm y).down.val‖ = 1 := by
  let yb : Cube.boundary (Fin n) := ⟨y, hy⟩
  let xb : TopCat.diskBoundary.{0} n :=
    (TopCat.diskBoundaryHomeoCubeBoundary.{0} n).symm yb
  have hpair := congrArg
    (fun h : TopCat.diskBoundary.{0} n ⟶ TopCat.of (I^ Fin n) => h xb)
    (TopCat.diskPair.homeoCubePair_comm n)
  change TopCat.diskHomeoCube.{0} n (TopCat.diskBoundaryIncl n xb) =
    Cube.boundaryIncl n (TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb) at hpair
  have hcube : TopCat.diskHomeoCube.{0} n (TopCat.diskBoundaryIncl n xb) = y := by
    rw [show TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb = yb by
      exact (TopCat.diskBoundaryHomeoCubeBoundary.{0} n).apply_symm_apply yb] at hpair
    exact hpair
  have hinv : (TopCat.diskHomeoCube.{0} n).symm y = TopCat.diskBoundaryIncl n xb :=
    (TopCat.diskHomeoCube.{0} n).symm_apply_eq.mpr hcube.symm
  rw [hinv]
  change ‖xb.down.val‖ = 1
  have hmem := xb.down.property
  rw [Metric.mem_sphere, dist_zero_right] at hmem
  exact hmem

/-- The standard continuous map from the `n`-cube to `Sⁿ`, constant on the cube boundary. -/
noncomputable def cubeToSphere (n : ℕ) : C(I^ Fin n, Sph n) :=
  (diskToSphere n).comp
    ⟨(TopCat.diskHomeoCube.{0} n).symm, (TopCat.diskHomeoCube.{0} n).continuous_symm⟩

/-- The cube-to-sphere map collapses the whole cube boundary to the benchmark basepoint. -/
theorem cubeToSphere_boundary (n : ℕ) (y : I^ Fin n) (hy : y ∈ Cube.boundary (Fin n)) :
    cubeToSphere n y = sphereBasepoint n := by
  exact diskToSphere_boundary n _ (norm_diskHomeoCube_symm_eq_one_of_mem_boundary n y hy)

/-- In positive dimensions, the cubical sphere generator is surjective. -/
theorem cubeToSphere_surjective (n : ℕ) : Function.Surjective (cubeToSphere (n + 1)) := by
  intro z
  obtain ⟨x, hx⟩ := diskToSphere_surjective n z
  refine ⟨TopCat.diskHomeoCube.{0} (n + 1) x, ?_⟩
  simpa [cubeToSphere] using hx

/-- In positive dimensions, the cubical sphere generator is a quotient map. -/
theorem isQuotientMap_cubeToSphere (n : ℕ) :
    Topology.IsQuotientMap (cubeToSphere (n + 1)) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (cubeToSphere_surjective n) (cubeToSphere (n + 1)).continuous

/-- A cube point lies on the boundary exactly when its inverse disk coordinate has norm one. -/
theorem mem_boundary_iff_norm_diskHomeoCube_symm_eq_one (n : ℕ) (y : I^ Fin n) :
    y ∈ Cube.boundary (Fin n) ↔
      ‖((TopCat.diskHomeoCube.{0} n).symm y).down.val‖ = 1 := by
  constructor
  · exact norm_diskHomeoCube_symm_eq_one_of_mem_boundary n y
  · intro hnorm
    let d : TopCat.disk.{0} n := (TopCat.diskHomeoCube.{0} n).symm y
    let raw : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨d.down.val, by rw [Metric.mem_sphere, dist_zero_right]; exact hnorm⟩
    let xb : TopCat.diskBoundary.{0} n := ULift.up raw
    have hd : TopCat.diskBoundaryIncl n xb = d := by
      apply ULift.ext
      apply Subtype.ext
      rfl
    have hpair := congrArg
      (fun h : TopCat.diskBoundary.{0} n ⟶ TopCat.of (I^ Fin n) => h xb)
      (TopCat.diskPair.homeoCubePair_comm n)
    change TopCat.diskHomeoCube.{0} n (TopCat.diskBoundaryIncl n xb) =
      Cube.boundaryIncl n (TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb) at hpair
    rw [hd, show TopCat.diskHomeoCube.{0} n d = y by
      exact (TopCat.diskHomeoCube.{0} n).apply_symm_apply y] at hpair
    let yb : Cube.boundary (Fin n) := TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb
    have hy : y = yb.val := by
      change y = (TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb).val
      change y = (TopCat.diskBoundaryHomeoCubeBoundary.{0} n xb).val at hpair
      exact hpair
    rw [hy]
    exact yb.property

/-- Two cube points have the same image under the generator exactly when they are equal or both
belong to the collapsed boundary. -/
theorem cubeToSphere_eq_iff (n : ℕ) (x y : I^ Fin n) :
    cubeToSphere n x = cubeToSphere n y ↔
      x = y ∨ (x ∈ Cube.boundary (Fin n) ∧ y ∈ Cube.boundary (Fin n)) := by
  constructor
  · intro h
    let dx : TopCat.disk.{0} n := (TopCat.diskHomeoCube.{0} n).symm x
    let dy : TopCat.disk.{0} n := (TopCat.diskHomeoCube.{0} n).symm y
    have hd : closedDiskToSphere n dx.down = closedDiskToSphere n dy.down := by
      exact h
    rcases (closedDiskToSphere_eq_iff n dx.down dy.down).mp hd with hxy | ⟨hx, hy⟩
    · left
      have hdx : dx = dy := by
        apply ULift.ext
        exact hxy
      exact (TopCat.diskHomeoCube.{0} n).symm.injective hdx
    · right
      exact ⟨(mem_boundary_iff_norm_diskHomeoCube_symm_eq_one n x).2 hx,
        (mem_boundary_iff_norm_diskHomeoCube_symm_eq_one n y).2 hy⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [cubeToSphere_boundary n x hx, cubeToSphere_boundary n y hy]

/-- The canonical generalized `n`-loop generating the cubical model of `Sⁿ`. -/
noncomputable def sphereGenerator (n : ℕ) :
    Ω^ (Fin n) (SphereSpace n) (sphereBasepoint n) :=
  ⟨cubeToSphere n, cubeToSphere_boundary n⟩

/-- The homotopy-group class represented by the canonical cubical sphere generator. -/
noncomputable def sphereGeneratorClass (n : ℕ) :
    HomotopyGroup.Pi n (SphereSpace n) (sphereBasepoint n) :=
  ⟦sphereGenerator n⟧

/-- A generalized loop is constant on every fibre of the cubical sphere generator. -/
theorem genLoop_factorsThrough_cubeToSphere (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    Function.FactorsThrough (α : C(I^ Fin (n + 1), SphereSpace (n + 1)))
      (cubeToSphere (n + 1)) := by
  intro x y hxy
  rcases (cubeToSphere_eq_iff (n + 1) x y).mp hxy with rfl | ⟨hx, hy⟩
  · rfl
  · rw [α.property x hx, α.property y hy]

/-- Descend a cubical generalized loop through the quotient `Iⁿ/∂Iⁿ → Sⁿ`, obtaining a sphere
self-map. -/
noncomputable def genLoopSphereMap (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    C(SphereSpace (n + 1), SphereSpace (n + 1)) :=
  (isQuotientMap_cubeToSphere n).lift α.1 (genLoop_factorsThrough_cubeToSphere n α)

/-- Descending a generalized loop and then precomposing with the generator recovers the loop. -/
@[simp]
theorem genLoopSphereMap_comp_cubeToSphere (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    (genLoopSphereMap n α).comp (cubeToSphere (n + 1)) = α.1 :=
  (isQuotientMap_cubeToSphere n).lift_comp _ _

/-- The descended sphere self-map fixes the benchmark basepoint. -/
theorem genLoopSphereMap_basepoint (n : ℕ)
    (α : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    genLoopSphereMap n α (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) := by
  let y : I^ Fin (n + 1) := fun _ => 0
  have hy : y ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  calc
    genLoopSphereMap n α (sphereBasepoint (n + 1)) =
        genLoopSphereMap n α (cubeToSphere (n + 1) y) := by
          rw [cubeToSphere_boundary (n + 1) y hy]
    _ = α y := by
      have h := congrArg (fun f : C(I^ Fin (n + 1), SphereSpace (n + 1)) => f y)
        (genLoopSphereMap_comp_cubeToSphere n α)
      exact h
    _ = sphereBasepoint (n + 1) := α.property y hy

/-- A relative cubical homotopy, curried in the cube variable, is constant on the fibres of the
cubical sphere generator. -/
theorem genLoopHomotopyCurry_factorsThrough_cubeToSphere (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    Function.FactorsThrough (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (cubeToSphere (n + 1)) := by
  intro x y hxy
  apply ContinuousMap.ext
  intro t
  change H (t, x) = H (t, y)
  rcases (cubeToSphere_eq_iff (n + 1) x y).mp hxy with rfl | ⟨hx, hy⟩
  · rfl
  · rw [H.eq_fst t hx, H.eq_fst t hy, α.property x hx, α.property y hy]

/-- Descend a cubical relative homotopy to a continuous family of paths on the sphere. -/
noncomputable def genLoopSphereHomotopyCurry (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    C(SphereSpace (n + 1), C(I, SphereSpace (n + 1))) :=
  (isQuotientMap_cubeToSphere n).lift
    (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
    (genLoopHomotopyCurry_factorsThrough_cubeToSphere n H)

/-- Evaluation of the descended homotopy after precomposition recovers the original cubical
homotopy. -/
@[simp]
theorem genLoopSphereHomotopyCurry_apply_cubeToSphere (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1))))
    (x : I^ Fin (n + 1)) (t : I) :
    genLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) x) t = H (t, x) := by
  have h := congrArg
    (fun f : C(I^ Fin (n + 1), C(I, SphereSpace (n + 1))) => f x t)
    ((isQuotientMap_cubeToSphere n).lift_comp
      (H.toContinuousMap.comp ContinuousMap.prodSwap).curry
      (genLoopHomotopyCurry_factorsThrough_cubeToSphere n H))
  exact h

/-- A cubical homotopy relative to the boundary descends to a homotopy of sphere self-maps. -/
noncomputable def genLoopSphereMapHomotopy (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) :
    ContinuousMap.Homotopy (genLoopSphereMap n α) (genLoopSphereMap n β) where
  toContinuousMap := (genLoopSphereHomotopyCurry n H).uncurry.comp ContinuousMap.prodSwap
  map_zero_left z := by
    obtain ⟨x, rfl⟩ := cubeToSphere_surjective n z
    change genLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) x) 0 =
      genLoopSphereMap n α (cubeToSphere (n + 1) x)
    rw [genLoopSphereHomotopyCurry_apply_cubeToSphere]
    have h := congrArg (fun f : C(I^ Fin (n + 1), SphereSpace (n + 1)) => f x)
      (genLoopSphereMap_comp_cubeToSphere n α)
    exact (H.map_zero_left x).trans h.symm
  map_one_left z := by
    obtain ⟨x, rfl⟩ := cubeToSphere_surjective n z
    change genLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) x) 1 =
      genLoopSphereMap n β (cubeToSphere (n + 1) x)
    rw [genLoopSphereHomotopyCurry_apply_cubeToSphere]
    have h := congrArg (fun f : C(I^ Fin (n + 1), SphereSpace (n + 1)) => f x)
      (genLoopSphereMap_comp_cubeToSphere n β)
    exact (H.map_one_left x).trans h.symm

/-- The descended homotopy fixes the sphere basepoint at every time. -/
theorem genLoopSphereMapHomotopy_basepoint (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : ContinuousMap.HomotopyRel α.1 β.1 (Cube.boundary (Fin (n + 1)))) (t : I) :
    genLoopSphereMapHomotopy n H (t, sphereBasepoint (n + 1)) =
      sphereBasepoint (n + 1) := by
  let y : I^ Fin (n + 1) := fun _ => 0
  have hy : y ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hbase : cubeToSphere (n + 1) y = sphereBasepoint (n + 1) :=
    cubeToSphere_boundary (n + 1) y hy
  conv_lhs => rw [← hbase]
  change genLoopSphereHomotopyCurry n H (cubeToSphere (n + 1) y) t = _
  rw [genLoopSphereHomotopyCurry_apply_cubeToSphere, H.eq_fst t hy, α.property y hy]

/-- Homotopic cubical representatives descend to based-homotopic sphere self-maps. -/
theorem genLoopSphereMap_homotopic (n : ℕ)
    {α β : Ω^ (Fin (n + 1)) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))}
    (H : GenLoop.Homotopic α β) :
    ContinuousMap.Homotopic (genLoopSphereMap n α) (genLoopSphereMap n β) := by
  obtain ⟨H⟩ := H
  exact ⟨genLoopSphereMapHomotopy n H⟩

/-- Precomposition with the cubical generator turns a based sphere self-map into a generalized
loop in the cubical definition of `πₙ(Sⁿ)`. -/
noncomputable def sphereSelfMapGenLoop (n : ℕ) (f : C(SphereSpace n, SphereSpace n))
    (hf : f (sphereBasepoint n) = sphereBasepoint n) :
    Ω^ (Fin n) (SphereSpace n) (sphereBasepoint n) :=
  ⟨f.comp (cubeToSphere n), fun y hy => by
    rw [ContinuousMap.comp_apply, cubeToSphere_boundary n y hy, hf]⟩

/-- The cubical homotopy class represented by a based sphere self-map. -/
noncomputable def sphereSelfMapClass (n : ℕ) (f : C(SphereSpace n, SphereSpace n))
    (hf : f (sphereBasepoint n) = sphereBasepoint n) :
    HomotopyGroup.Pi n (SphereSpace n) (sphereBasepoint n) :=
  ⟦sphereSelfMapGenLoop n f hf⟧

/-- A based homotopy of sphere self-maps induces a homotopy relative to the cube boundary after
precomposition with the cubical generator. -/
theorem sphereSelfMapGenLoopHomotopy (n : ℕ)
    {f g : C(SphereSpace n, SphereSpace n)}
    (hf : f (sphereBasepoint n) = sphereBasepoint n)
    (hg : g (sphereBasepoint n) = sphereBasepoint n)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint n) = sphereBasepoint n) :
    GenLoop.Homotopic (sphereSelfMapGenLoop n f hf) (sphereSelfMapGenLoop n g hg) := by
  refine ⟨H.compContinuousMap (cubeToSphere n), ?_⟩
  intro t y hy
  change H (t, cubeToSphere n y) = f (cubeToSphere n y)
  rw [cubeToSphere_boundary n y hy, hbase, hf]

/-- Based-homotopic sphere self-maps determine the same cubical homotopy-group class. -/
theorem sphereSelfMapClass_eq_of_homotopy (n : ℕ)
    {f g : C(SphereSpace n, SphereSpace n)}
    (hf : f (sphereBasepoint n) = sphereBasepoint n)
    (hg : g (sphereBasepoint n) = sphereBasepoint n)
    (H : ContinuousMap.Homotopy f g)
    (hbase : ∀ t : I, H (t, sphereBasepoint n) = sphereBasepoint n) :
    sphereSelfMapClass n f hf = sphereSelfMapClass n g hg :=
  Quotient.sound (sphereSelfMapGenLoopHomotopy n hf hg H hbase)

/-- The identity self-map represents the canonical cubical sphere generator. -/
@[simp]
theorem sphereSelfMapClass_id (n : ℕ) :
    sphereSelfMapClass n (ContinuousMap.id (SphereSpace n)) rfl = sphereGeneratorClass n := by
  apply Quotient.sound
  exact GenLoop.Homotopic.refl _

/-- Every positive-dimensional diagonal cubical homotopy class is represented by a based sphere
self-map.  This is the quotient-model bridge needed before applying homological degree. -/
theorem homotopyGroup_exists_sphereSelfMapRepresentative (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (SphereSpace (n + 1)) (sphereBasepoint (n + 1))) :
    ∃ (f : C(SphereSpace (n + 1), SphereSpace (n + 1)))
        (hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1)),
      sphereSelfMapClass (n + 1) f hf = a := by
  induction a using Quotient.ind with
  | _ α =>
      let f := genLoopSphereMap n α
      have hf : f (sphereBasepoint (n + 1)) = sphereBasepoint (n + 1) :=
        genLoopSphereMap_basepoint n α
      refine ⟨f, hf, ?_⟩
      have hloop : sphereSelfMapGenLoop (n + 1) f hf = α := by
        apply GenLoop.ext
        intro y
        have h := congrArg (fun g : C(I^ Fin (n + 1), SphereSpace (n + 1)) => g y)
          (genLoopSphereMap_comp_cubeToSphere n α)
        exact h
      change (⟦sphereSelfMapGenLoop (n + 1) f hf⟧) = ⟦α⟧
      rw [hloop]

end Submission
