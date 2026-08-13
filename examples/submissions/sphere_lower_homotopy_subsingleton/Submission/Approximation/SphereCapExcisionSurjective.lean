/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCapExcisionInjective
import Submission.SphereSuspensionExcisionStable
import Submission.HopfFibration
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Stable surjectivity of spherical cap excision

A target relative sphere loop is first squeezed and replaced by a finite radial PL
representative.  Its boundary jar is based in both caps, while its remaining lid lies in the
upper cap.  Stable two-cell general position and last-coordinate compression therefore supply a
lower-cell point `x`, an upper-cell point `y`, and a jar-relative compressed map which avoids
`x` on the lid and `y` everywhere.

Applying the lower-puncture raising map with strength equal to the last cube coordinate keeps the
lid in the upper cap throughout compression.  A controlled upper-puncture deformation then
lowers the endpoint into the lower cap.  Its boundary lands in the overlap, producing the desired
source representative and a target-pair homotopy from the original PL representative to its
inclusion.

## Main results

* `Submission.exists_relativeSpherePLApproximation_cellCompression`
* `Submission.relativeSpherePLApproximation_homotopic_includedSource_surjectiveRange`
* `Submission.sphereSuspensionExcisionHomAt_surjective_of_freudenthalRange`
* `Submission.sphereSuspensionExcisionStableRange_proved`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d q : ℕ}

/-! ### Stable compression of one target relative loop -/

/-- The radial ambient map underlying a relative PL approximation is pointwise its bundled
approximation. -/
theorem RelativeSpherePLApproximation.radialSphereCubeMap_eq_approx
    {p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d)}
    {hp : RelGenLoop.BoundaryHeightNonneg p}
    (A : RelativeSpherePLApproximation p hp) (z : I^ Fin (q + 2)) :
    radialSphereCubeMap
        (cubeGridAffineApprox (q + 2) A.mesh (relGenLoopToEuclidean p))
        A.approx_ne_zero z = A.approx.val z := by
  apply Subtype.ext
  exact (A.coe_approx z).symm

/-- A relative PL approximation retains the nonnegative-height boundary margin. -/
theorem RelativeSpherePLApproximation.approx_boundaryHeightNonneg
    {p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d)}
    {hp : RelGenLoop.BoundaryHeightNonneg p}
    (A : RelativeSpherePLApproximation p hp)
    {z : I^ Fin (q + 2)} (hz : z ∈ ∂I^(q + 2)) :
    0 ≤ sphHeight (A.approx.val z) := by
  change 0 ≤ (A.approx.val z).1 (Fin.last (d + 1))
  rw [A.coe_approx]
  exact radialProj_last_nonneg
    (cubeGridAffineApprox_relGenLoop_last_nonneg A.mesh_pos p hp hz)

/-- A finite PL target representative in the Freudenthal epimorphism range admits two-cell
compression relative to its boundary jar.  The compressed map avoids an upper-cell point
everywhere and a lower-cell point on its boundary lid. -/
theorem exists_relativeSpherePLApproximation_cellCompression
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (A : RelativeSpherePLApproximation p hp)
    (hrange : q + 2 ≤ 2 * d) :
    ∃ x y : Sph (d + 1),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 2), Sph (d + 1)),
        ∃ K : ContinuousMap.HomotopyRel A.approx.val g' (⊔I^(q + 2)),
          (∀ t z, z ∈ Cube.boundaryLid (q + 2) →
            K.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  let G := cubeGridAffineApprox (q + 2) A.mesh (relGenLoopToEuclidean p)
  have hhalf : ∀ z, 1 / 2 ≤ ‖G z‖ :=
    cubeGridAffineApprox_norm_ge_half (relGenLoopToEuclidean p)
      (fun z => norm_coe_sph (p.val z)) A.dist_le_half
  have hmaps :
      radialSphereCubeMap G A.approx_ne_zero = A.approx.val := by
    apply ContinuousMap.ext
    intro z
    exact A.radialSphereCubeMap_eq_approx z
  have hcompression := exists_sphereCell_compression
    (n := q + 1) G (locallyLipschitz_cubeGridAffineApprox (relGenLoopToEuclidean p))
      A.approx_ne_zero hhalf (by omega)
      (Cube.boundaryLid (q + 2))
      (by
        intro r hr s
        let z := Cube.splitAtLast.symm (s, r)
        have hzjar : z ∈ ⊔I^(q + 2) := by
          apply Cube.mem_boundaryJar_iff_splitAtLast.mpr
          right
          simpa only [z, Homeomorph.apply_symm_apply] using hr
        rw [show radialSphereCubeMap G A.approx_ne_zero z = A.approx.val z by
          exact A.radialSphereCubeMap_eq_approx z]
        rw [A.approx.property.2 z hzjar]
        exact sphereBasepoint_mem_sphLowerCap d)
      (by
        intro r
        let z := Cube.splitAtLast.symm ((0 : I), r)
        have hzjar : z ∈ ⊔I^(q + 2) := by
          apply Cube.mem_boundaryJar_iff_splitAtLast.mpr
          left
          simp only [z, Homeomorph.apply_symm_apply]
        rw [show radialSphereCubeMap G A.approx_ne_zero z = A.approx.val z by
          exact A.radialSphereCubeMap_eq_approx z]
        rw [A.approx.property.2 z hzjar]
        exact sphereBasepoint_mem_sphLowerCap d)
      (by
        intro z hz
        rw [show radialSphereCubeMap G A.approx_ne_zero z = A.approx.val z by
          exact A.radialSphereCubeMap_eq_approx z]
        exact A.approx.property.1 z
          ⟨Fin.last (q + 1), Or.inr hz⟩)
  rw [hmaps] at hcompression
  exact hcompression

/-! ### Keeping the target lid in the upper cap -/

/-- Apply lower-puncture raising to a target relative loop according to its last cube
coordinate.  A nonnegative-height boundary is fixed pointwise. -/
noncomputable def lowerCellCollarRaiseTargetRelGenLoop
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hpboundary : ∀ z, z ∈ (∂I^(q + 2)) →
      0 ≤ sphHeight (p.val z)) :
    RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d) where
  val := ⟨fun z =>
      let u := spatialLidControl z
      let havoid : u = 1 → p.val z ≠ x := fun hu hpx => by
        have hnonneg := hpboundary z
          (mem_boundary_of_spatialLidControl_eq_one hu)
        rw [hpx] at hnonneg
        linarith
      lowerCellPunctureRaisePoint x hx u (p.val z) havoid,
    by
      apply Continuous.subtype_mk
      apply continuous_radialProj
      · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
          (continuous_spatialLidControl.prodMk p.val.continuous)
      · intro z
        apply lowerCellPunctureRaiseAmbient_ne_zero x (p.val z) hx
        intro hu hpx
        have hnonneg := hpboundary z
          (mem_boundary_of_spatialLidControl_eq_one hu)
        rw [hpx] at hnonneg
        linarith⟩
  property := by
    constructor
    · intro z hz
      have hnonneg := hpboundary z hz
      have havoid : spatialLidControl z = 1 → p.val z ≠ x :=
        fun _ hpx => by rw [hpx] at hnonneg; linarith
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (p.val z) havoid ∈ sphUpperCap d
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg havoid]
      exact p.property.1 z hz
    · intro z hz
      have hboundary := Cube.boundaryJar_subset_boundary (q + 2) hz
      have hnonneg := hpboundary z hboundary
      have havoid : spatialLidControl z = 1 → p.val z ≠ x :=
        fun _ hpx => by rw [hpx] at hnonneg; linarith
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (p.val z) havoid = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg havoid]
      exact p.property.2 z hz

/-- The target collar raise is homotopic to the original target relative loop. -/
theorem relGenLoopHomotopic_lowerCellCollarRaiseTarget
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hpboundary : ∀ z, z ∈ (∂I^(q + 2)) →
      0 ≤ sphHeight (p.val z)) :
    RelGenLoop.Homotopic p
      (lowerCellCollarRaiseTargetRelGenLoop x hx p hpboundary) := by
  let control : (I × (I^ Fin (q + 2))) → I :=
    fun sz => sz.1 * spatialLidControl sz.2
  have hcontrol : Continuous control := by
    dsimp only [control]
    exact continuous_fst.mul
      (continuous_spatialLidControl.comp continuous_snd)
  have havoid : ∀ sz : I × I^ Fin (q + 2),
      control sz = 1 → p.val sz.2 ≠ x := by
    intro sz hu hpx
    have hlast : spatialLidControl sz.2 = 1 :=
      unitInterval_right_eq_one_of_mul_eq_one sz.1
        (spatialLidControl sz.2) hu
    have hnonneg := hpboundary sz.2
      (mem_boundary_of_spatialLidControl_eq_one hlast)
    rw [hpx] at hnonneg
    linarith
  refine ⟨⟨⟨fun sz =>
      lowerCellPunctureRaisePoint x hx (control sz) (p.val sz.2)
        (havoid sz), ?_⟩, ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
        (hcontrol.prodMk (p.val.continuous.comp continuous_snd))
    · intro sz
      exact lowerCellPunctureRaiseAmbient_ne_zero x (p.val sz.2) hx
        (control sz) (havoid sz)
  · intro z
    apply Subtype.ext
    change radialProj
      (lowerCellPunctureRaiseAmbient x (control (0, z)) (p.val z)) =
        (p.val z).1
    have hcontrolzero : control (0, z) = 0 := by
      apply Subtype.ext
      simp [control]
    rw [hcontrolzero]
    have hamb : lowerCellPunctureRaiseAmbient x 0 (p.val z) =
        (p.val z).1 := by
      rw [lowerCellPunctureRaiseAmbient]
      norm_num
    rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph (p.val z))]
  · intro z
    apply Subtype.ext
    change radialProj
      (lowerCellPunctureRaiseAmbient x (control (1, z)) (p.val z)) =
      radialProj
        (lowerCellPunctureRaiseAmbient x (spatialLidControl z) (p.val z))
    have hcontrolone : control (1, z) = spatialLidControl z := by
      apply Subtype.ext
      simp [control]
    rw [hcontrolone]
  · intro s
    constructor
    · intro z hz
      have hnonneg := hpboundary z hz
      change lowerCellPunctureRaisePoint x hx (control (s, z))
          (p.val z) (havoid (s, z)) ∈ sphUpperCap d
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (control (s, z)) hnonneg (havoid (s, z))]
      exact p.property.1 z hz
    · intro z hz
      have hnonneg := hpboundary z
        (Cube.boundaryJar_subset_boundary (q + 2) hz)
      change lowerCellPunctureRaisePoint x hx (control (s, z))
          (p.val z) (havoid (s, z)) = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (control (s, z)) hnonneg (havoid (s, z))]
      exact p.property.2 z hz

/-- The endpoint of a jar-relative compression remains based on the jar. -/
theorem compressedRelativeSpherePLApproximation_eq_base_of_mem_jar
    {p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d)}
    {hp : RelGenLoop.BoundaryHeightNonneg p}
    (A : RelativeSpherePLApproximation p hp)
    (g' : C(I^ Fin (q + 2), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel A.approx.val g' (⊔I^(q + 2)))
    {z : I^ Fin (q + 2)} (hz : z ∈ ⊔I^(q + 2)) :
    g' z = sphereBasepoint (d + 1) := by
  calc
    g' z = K.toHomotopy (1, z) := (K.map_one_left z).symm
    _ = A.approx.val z := K.prop' 1 z hz
    _ = sphereBasepoint (d + 1) := A.approx.property.2 z hz

/-- Lower-cell collar raising of the compressed map.  Full raising occurs only on the lid,
where compression preserved avoidance of `x`; the jar remains at the basepoint. -/
noncomputable def lowerCellRaisedCompressedRelGenLoop
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (g' : C(I^ Fin (q + 2), Sph (d + 1)))
    (hgx : ∀ z, z ∈ Cube.boundaryLid (q + 2) → g' z ≠ x)
    (hjar : ∀ z : I^ Fin (q + 2), (z ∈ ⊔I^(q + 2)) →
      g' z = sphereBasepoint (d + 1)) :
    RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d) where
  val := ⟨fun z =>
      let u := spatialLidControl z
      let havoid : u = 1 → g' z ≠ x := fun hu =>
        hgx z hu
      lowerCellPunctureRaisePoint x hx u (g' z) havoid,
    by
      apply Continuous.subtype_mk
      apply continuous_radialProj
      · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
          (continuous_spatialLidControl.prodMk g'.continuous)
      · intro z
        apply lowerCellPunctureRaiseAmbient_ne_zero x (g' z) hx
        intro hu
        exact hgx z hu⟩
  property := by
    constructor
    · intro z hz
      rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary z hz with
        hlid | hjarz
      · have havoid : spatialLidControl z = 1 → g' z ≠ x :=
          fun _ => hgx z hlid
        change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
            (g' z) havoid ∈ sphUpperCap d
        have hcontrol := spatialLidControl_eq_one_of_mem_boundaryLid hlid
        simpa only [hcontrol] using
          lowerCellPunctureRaisePoint_mem_upperCap_one x hx (hgx z hlid)
      · have hgbase := hjar z hjarz
        have hnonneg : 0 ≤ sphHeight (g' z) := by
          rw [hgbase, sphHeight_sphereBasepoint_succ]
        have havoid : spatialLidControl z = 1 → g' z ≠ x :=
          fun _ hzx => by rw [hzx] at hnonneg; linarith
        change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
            (g' z) havoid ∈ sphUpperCap d
        rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
          x hx (spatialLidControl z) hnonneg havoid, hgbase]
        exact sphereBasepoint_mem_sphUpperCap d
    · intro z hz
      have hgbase := hjar z hz
      have hnonneg : 0 ≤ sphHeight (g' z) := by
        rw [hgbase, sphHeight_sphereBasepoint_succ]
      have havoid : spatialLidControl z = 1 → g' z ≠ x :=
        fun _ hzx => by rw [hzx] at hnonneg; linarith
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (g' z) havoid = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg havoid, hgbase]

/-- Every boundary value of the raised compressed loop has nonnegative height: the lid is fully
raised and the rest of the boundary jar is the equatorial basepoint. -/
theorem lowerCellRaisedCompressedRelGenLoop_boundaryHeightNonneg
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (g' : C(I^ Fin (q + 2), Sph (d + 1)))
    (hgx : ∀ z, z ∈ Cube.boundaryLid (q + 2) → g' z ≠ x)
    (hjar : ∀ z : I^ Fin (q + 2), (z ∈ ⊔I^(q + 2)) →
      g' z = sphereBasepoint (d + 1))
    {z : I^ Fin (q + 2)} (hz : z ∈ ∂I^(q + 2)) :
    0 ≤ sphHeight
      ((lowerCellRaisedCompressedRelGenLoop x hx g' hgx hjar).val z) := by
  rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary z hz with
    hlid | hjarz
  · have havoid : spatialLidControl z = 1 → g' z ≠ x :=
      fun _ => hgx z hlid
    change 0 ≤ sphHeight
      (lowerCellPunctureRaisePoint x hx (spatialLidControl z) (g' z) havoid)
    have hcontrol := spatialLidControl_eq_one_of_mem_boundaryLid hlid
    simpa only [hcontrol] using
      lowerCellPunctureRaisePoint_height_nonneg_one x hx (hgx z hlid)
  · rw [(lowerCellRaisedCompressedRelGenLoop x hx g' hgx hjar).property.2 z hjarz,
      sphUpperCapBase, sphHeight_sphereBasepoint_succ]

/-- Lower-cell raising cannot introduce the positive-height upper puncture into the compressed
endpoint. -/
theorem lowerCellRaisedCompressedRelGenLoop_ne_upperPoint
    (x y : Sph (d + 1)) (hx : sphHeight x < 0) (hy : 0 < sphHeight y)
    (g' : C(I^ Fin (q + 2), Sph (d + 1)))
    (hgx : ∀ z, z ∈ Cube.boundaryLid (q + 2) → g' z ≠ x)
    (hjar : ∀ z : I^ Fin (q + 2), (z ∈ ⊔I^(q + 2)) →
      g' z = sphereBasepoint (d + 1))
    (hgy : ∀ z, g' z ≠ y) (z : I^ Fin (q + 2)) :
    (lowerCellRaisedCompressedRelGenLoop x hx g' hgx hjar).val z ≠ y := by
  let havoid : spatialLidControl z = 1 → g' z ≠ x := fun hu => hgx z hu
  exact lowerCellPunctureRaisePoint_ne_of_ne hx hy (spatialLidControl z)
    (hgy z) havoid

/-- Applying the collar raise pointwise to the compression homotopy turns it into a genuine
homotopy through target relative loops. -/
theorem lowerCellCollarRaiseTarget_homotopic_raisedCompression
    {p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d)}
    {hp : RelGenLoop.BoundaryHeightNonneg p}
    (A : RelativeSpherePLApproximation p hp)
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (g' : C(I^ Fin (q + 2), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel A.approx.val g' (⊔I^(q + 2)))
    (hKx : ∀ t z, z ∈ Cube.boundaryLid (q + 2) →
      K.toHomotopy (t, z) ≠ x) :
    RelGenLoop.Homotopic
      (lowerCellCollarRaiseTargetRelGenLoop x hx A.approx
        (fun _ hz => A.approx_boundaryHeightNonneg hz))
      (lowerCellRaisedCompressedRelGenLoop x hx g'
        (fun z hz => by
          intro hzx
          exact hKx 1 z hz ((K.map_one_left z).trans hzx))
        (fun z hz => compressedRelativeSpherePLApproximation_eq_base_of_mem_jar
          A g' K hz)) := by
  let hgx : ∀ z, z ∈ Cube.boundaryLid (q + 2) → g' z ≠ x :=
    fun z hz hzx => hKx 1 z hz ((K.map_one_left z).trans hzx)
  let hjar : ∀ z : I^ Fin (q + 2), (z ∈ ⊔I^(q + 2)) →
      g' z = sphereBasepoint (d + 1) :=
    fun z _hz => compressedRelativeSpherePLApproximation_eq_base_of_mem_jar
      A g' K _hz
  have havoid : ∀ tz : I × I^ Fin (q + 2),
      spatialLidControl tz.2 = 1 → K.toHomotopy tz ≠ x := by
    intro tz hu
    exact hKx tz.1 tz.2 hu
  refine ⟨⟨⟨fun tz =>
      lowerCellPunctureRaisePoint x hx (spatialLidControl tz.2)
        (K.toHomotopy tz) (havoid tz), ?_⟩, ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
        ((continuous_spatialLidControl.comp continuous_snd).prodMk
          K.continuous_toFun)
    · intro tz
      exact lowerCellPunctureRaiseAmbient_ne_zero x (K.toHomotopy tz) hx
        (spatialLidControl tz.2) (havoid tz)
  · intro z
    apply Subtype.ext
    change radialProj (lowerCellPunctureRaiseAmbient x (spatialLidControl z)
        (K.toHomotopy (0, z))) =
      radialProj (lowerCellPunctureRaiseAmbient x (spatialLidControl z)
        (A.approx.val z))
    exact congrArg
      (fun w : Sph (d + 1) => radialProj
        (lowerCellPunctureRaiseAmbient x (spatialLidControl z) w))
      (K.map_zero_left z)
  · intro z
    apply Subtype.ext
    change radialProj (lowerCellPunctureRaiseAmbient x (spatialLidControl z)
        (K.toHomotopy (1, z))) =
      radialProj (lowerCellPunctureRaiseAmbient x (spatialLidControl z)
        (g' z))
    exact congrArg
      (fun w : Sph (d + 1) => radialProj
        (lowerCellPunctureRaiseAmbient x (spatialLidControl z) w))
      (K.map_one_left z)
  · intro t
    constructor
    · intro z hz
      rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary z hz with
        hlid | hjarz
      · change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
            (K.toHomotopy (t, z)) (havoid (t, z)) ∈ sphUpperCap d
        have hcontrol := spatialLidControl_eq_one_of_mem_boundaryLid hlid
        simpa only [hcontrol] using
          lowerCellPunctureRaisePoint_mem_upperCap_one x hx (hKx t z hlid)
      · have hKbase : K.toHomotopy (t, z) = sphereBasepoint (d + 1) :=
          (K.prop' t z hjarz).trans (A.approx.property.2 z hjarz)
        have hnonneg : 0 ≤ sphHeight (K.toHomotopy (t, z)) := by
          rw [hKbase, sphHeight_sphereBasepoint_succ]
        change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
            (K.toHomotopy (t, z)) (havoid (t, z)) ∈ sphUpperCap d
        rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
          x hx (spatialLidControl z) hnonneg (havoid (t, z)), hKbase]
        exact sphereBasepoint_mem_sphUpperCap d
    · intro z hz
      have hKbase : K.toHomotopy (t, z) = sphereBasepoint (d + 1) :=
        (K.prop' t z hz).trans (A.approx.property.2 z hz)
      have hnonneg : 0 ≤ sphHeight (K.toHomotopy (t, z)) := by
        rw [hKbase, sphHeight_sphereBasepoint_succ]
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (K.toHomotopy (t, z)) (havoid (t, z)) = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg (havoid (t, z)), hKbase]

/-! ### Lowering the compressed endpoint into the source pair -/

/-- Full upper-puncture lowering of a target relative loop with nonnegative boundary gives a
source relative loop.  Its boundary has height zero, hence lies in both caps. -/
noncomputable def upperCellPunctureLowerSourceRelGenLoop
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hpy : ∀ z, p.val z ≠ y)
    (hpboundary : ∀ z, z ∈ (∂I^(q + 2)) →
      0 ≤ sphHeight (p.val z)) :
    RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d) where
  val := ⟨fun z =>
      ⟨upperCellPunctureLower y hy ⟨p.val z, hpy z⟩,
        upperCellPunctureLower_mem_lowerCap y hy ⟨p.val z, hpy z⟩⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply continuous_radialProj
      · exact (continuous_upperCellPunctureLowerAmbient y).comp p.val.continuous
      · intro z
        exact upperCellPunctureLowerAmbient_ne_zero y hy (hpy z)⟩
  property := by
    constructor
    · intro z hz
      change upperCellPunctureLower y hy ⟨p.val z, hpy z⟩ ∈ sphUpperCap d
      rw [mem_sphUpperCap]
      have hout : 0 ≤ sphHeight
          (upperCellPunctureLower y hy ⟨p.val z, hpy z⟩) := by
        rw [← upperCellPunctureLowerPointAt_one y hy (p.val z) (hpy z)]
        exact upperCellPunctureLowerPointAt_height_nonneg y hy 1
          (hpboundary z hz) (fun _ => hpy z)
      exact (by norm_num : -(1 / 3 : ℝ) ≤ 0).trans hout
    · intro z hz
      change (⟨upperCellPunctureLower y hy ⟨p.val z, hpy z⟩,
        upperCellPunctureLower_mem_lowerCap y hy ⟨p.val z, hpy z⟩⟩ :
          sphLowerCap d) = (sphCapOverlapBase d).1
      apply Subtype.ext
      have hpbase := p.property.2 z hz
      change p.val z = sphereBasepoint (d + 1) at hpbase
      have hybase : sphereBasepoint (d + 1) ≠ y := by
        intro h
        have hh := congrArg sphHeight h
        rw [sphHeight_sphereBasepoint_succ] at hh
        linarith
      have hpSub : (⟨p.val z, hpy z⟩ : SphPointCompl y) =
          ⟨sphereBasepoint (d + 1), hybase⟩ :=
        Subtype.ext hpbase
      calc
        upperCellPunctureLower y hy ⟨p.val z, hpy z⟩ =
            sphereBasepoint (d + 1) := by
              rw [hpSub]
              exact upperCellPunctureLower_base y hy hybase
        _ = (sphCapOverlapBase d).1.1 := rfl

/-- Controlled upper-puncture lowering is a target-pair homotopy from a target loop to the
inclusion of its fully lowered source loop. -/
theorem relGenLoopHomotopic_upperCellPunctureLowerSource
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hpy : ∀ z, p.val z ≠ y)
    (hpboundary : ∀ z, z ∈ (∂I^(q + 2)) →
      0 ≤ sphHeight (p.val z)) :
    RelGenLoop.Homotopic p
      (RelGenLoop.map (sphCapInclusionPairMap d)
        (upperCellPunctureLowerSourceRelGenLoop y hy p hpy hpboundary)) := by
  have havoid : ∀ uz : I × I^ Fin (q + 2),
      uz.1 = 1 → p.val uz.2 ≠ y := fun uz _ => hpy uz.2
  refine ⟨⟨⟨fun uz =>
      upperCellPunctureLowerPointAt y hy uz.1 (p.val uz.2) (havoid uz), ?_⟩,
    ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_upperCellPunctureLowerAmbientAt y).comp
        (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
    · intro uz
      exact upperCellPunctureLowerAmbientAt_ne_zero y (p.val uz.2) hy uz.1
        (havoid uz)
  · intro z
    exact upperCellPunctureLowerPointAt_zero y hy (p.val z) (havoid (0, z))
  · intro z
    change upperCellPunctureLowerPointAt y hy 1 (p.val z) (havoid (1, z)) =
      upperCellPunctureLower y hy ⟨p.val z, hpy z⟩
    simpa only using upperCellPunctureLowerPointAt_one y hy (p.val z) (hpy z)
  · intro u
    constructor
    · intro z hz
      rw [mem_sphUpperCap]
      exact (by norm_num : -(1 / 3 : ℝ) ≤ 0).trans
        (upperCellPunctureLowerPointAt_height_nonneg y hy u
          (hpboundary z hz) (havoid (u, z)))
    · intro z hz
      have hpbase := p.property.2 z hz
      change p.val z = sphereBasepoint (d + 1) at hpbase
      have hnonpos : sphHeight (p.val z) ≤ 0 := by
        rw [hpbase, sphHeight_sphereBasepoint_succ]
      change upperCellPunctureLowerPointAt y hy u (p.val z) (havoid (u, z)) =
        sphereBasepoint (d + 1)
      exact (upperCellPunctureLowerPointAt_eq_of_height_nonpos y hy u
        hnonpos (havoid (u, z))).trans hpbase

/-! ### Stable representative-level surjectivity -/

/-- Every finite PL target representative in the Freudenthal epimorphism range is relatively
homotopic to the inclusion of a source representative. -/
theorem relativeSpherePLApproximation_homotopic_includedSource_surjectiveRange
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (A : RelativeSpherePLApproximation p hp)
    (hrange : q + 2 ≤ 2 * d) :
    ∃ r : RelGenLoop (q + 2) (sphLowerCap d)
        (sphCapOverlapInLower d) (sphCapOverlapBase d),
      RelGenLoop.Homotopic A.approx
        (RelGenLoop.map (sphCapInclusionPairMap d) r) := by
  obtain ⟨x, y, hx, hy, g', K, hKx, hgy⟩ :=
    exists_relativeSpherePLApproximation_cellCompression p hp A hrange
  have hxneg : sphHeight x < 0 :=
    (sphHeight_lt_neg_third_of_not_mem_upperCap hx).trans_le (by norm_num)
  have hypos : 0 < sphHeight y :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans
      (third_lt_sphHeight_of_not_mem_lowerCap hy)
  let hgx : ∀ z, z ∈ Cube.boundaryLid (q + 2) → g' z ≠ x :=
    fun z hz hzx => hKx 1 z hz ((K.map_one_left z).trans hzx)
  let hjar : ∀ z : I^ Fin (q + 2), (z ∈ ⊔I^(q + 2)) →
      g' z = sphereBasepoint (d + 1) :=
    fun z hz => compressedRelativeSpherePLApproximation_eq_base_of_mem_jar
      A g' K hz
  let Q := lowerCellRaisedCompressedRelGenLoop x hxneg g' hgx hjar
  have hQboundary : ∀ z, z ∈ (∂I^(q + 2)) →
      0 ≤ sphHeight (Q.val z) := by
    intro z hz
    exact lowerCellRaisedCompressedRelGenLoop_boundaryHeightNonneg
      x hxneg g' hgx hjar hz
  have hQy : ∀ z, Q.val z ≠ y := by
    intro z
    exact lowerCellRaisedCompressedRelGenLoop_ne_upperPoint
      x y hxneg hypos g' hgx hjar hgy z
  let r := upperCellPunctureLowerSourceRelGenLoop y hypos Q hQy hQboundary
  refine ⟨r, ?_⟩
  have hcollar := relGenLoopHomotopic_lowerCellCollarRaiseTarget
    x hxneg A.approx (fun _ hz => A.approx_boundaryHeightNonneg hz)
  have hcompression := lowerCellCollarRaiseTarget_homotopic_raisedCompression
    A x hxneg g' K hKx
  have hlowering := relGenLoopHomotopic_upperCellPunctureLowerSource
    y hypos Q hQy hQboundary
  exact hcollar.trans <| hcompression.trans <| by
    simpa only [r] using hlowering

/-- Stable-range specialization of the sharper representative-level surjectivity theorem. -/
theorem relativeSpherePLApproximation_homotopic_includedSource_stableRange
    (p : RelGenLoop (q + 2) (Sph (d + 1))
      (sphUpperCap d) (sphUpperCapBase d))
    (hp : RelGenLoop.BoundaryHeightNonneg p)
    (A : RelativeSpherePLApproximation p hp)
    (hrange : q + 3 ≤ 2 * d) :
    ∃ r : RelGenLoop (q + 2) (sphLowerCap d)
        (sphCapOverlapInLower d) (sphCapOverlapBase d),
      RelGenLoop.Homotopic A.approx
        (RelGenLoop.map (sphCapInclusionPairMap d) r) :=
  relativeSpherePLApproximation_homotopic_includedSource_surjectiveRange
    p hp A (by omega)

/-! ### Quotient-level stable cap excision -/

/-- Two-cell compression makes the cap-inclusion map surjective throughout the full Freudenthal
epimorphism range, one degree wider than its isomorphism range. -/
theorem sphereSuspensionExcisionHomAt_surjective_of_freudenthalRange
    (d q : ℕ) (hrange : q + 2 ≤ 2 * d) :
    Function.Surjective (sphereSuspensionExcisionHomAt d q) := by
  intro a
  obtain ⟨p, hp, A, ha⟩ :=
    relHomotopyGroup_exists_relativeSpherePLRepresentative a
  obtain ⟨r, hAr⟩ :=
    relativeSpherePLApproximation_homotopic_includedSource_surjectiveRange
      p hp A hrange
  refine ⟨⟦r⟧, ?_⟩
  change (⟦RelGenLoop.map (sphCapInclusionPairMap d) r⟧ :
      π_rel (q + 2) (Sph (d + 1)) (sphUpperCap d)
        (sphUpperCapBase d)) = a
  rw [ha]
  exact (Quotient.sound hAr).symm

/-- Stable-range surjectivity as a direct corollary of the sharper epimorphism-range theorem. -/
theorem sphereSuspensionExcisionHomAt_surjective_of_stableRange
    (d q : ℕ) (hrange : q + 3 ≤ 2 * d) :
    Function.Surjective (sphereSuspensionExcisionHomAt d q) :=
  sphereSuspensionExcisionHomAt_surjective_of_freudenthalRange d q (by omega)

/-- The induced absolute sphere comparison is surjective throughout the Freudenthal
epimorphism range. -/
theorem sphereCapSuspensionHomAt_surjective_of_freudenthalRange
    (d q : ℕ) (hd : 1 ≤ d) (hrange : q + 2 ≤ 2 * d) :
    Function.Surjective (sphereCapSuspensionHomAt d q hd) :=
  sphereCapSuspensionHomAt_surjective_of_capExcision d q hd
    (sphereSuspensionExcisionHomAt_surjective_of_freudenthalRange d q hrange)

/-- The first edge case is a concrete surjection from `pi_3(S^2)` onto `pi_4(S^3)`. -/
theorem sphereCapSuspensionHomAt_two_two_surjective :
    Function.Surjective (sphereCapSuspensionHomAt 2 2 (by omega)) :=
  sphereCapSuspensionHomAt_surjective_of_freudenthalRange 2 2 (by omega) (by omega)

/-- Consequently `pi_4(S^3)` is cyclic: the edge comparison is a quotient of the already
computed infinite-cyclic group `pi_3(S^2)`. -/
theorem isCyclic_pi_four_sphere_three :
    IsCyclic (π_ 4 (Sph 3) (sphereBasepoint 3)) := by
  obtain ⟨e⟩ := pi3_sphere_two_mulEquiv_int
  let f : Multiplicative ℤ →* π_ 4 (Sph 3) (sphereBasepoint 3) :=
    (sphereCapSuspensionHomAt 2 2 (by omega)).comp e.symm.toMonoidHom
  exact isCyclic_of_surjective f
    (sphereCapSuspensionHomAt_two_two_surjective.comp e.symm.surjective)

/-- The single natural-number modulus left by the cyclic quotient description of
`pi_4(S^3)`.  Value zero denotes the infinite-cyclic possibility, as usual for `ZMod 0`. -/
noncomputable def piFourSphereThreeModulus : ℕ :=
  Nat.card (π_ 4 (Sph 3) (sphereBasepoint 3))

/-- Without any further topology, the first stable representative is already classified as the
cyclic group with its canonical cardinal modulus. -/
noncomputable def piFourSphereThreeMulEquivZMod :
    π_ 4 (Sph 3) (sphereBasepoint 3) ≃*
      Multiplicative (ZMod piFourSphereThreeModulus) :=
  (zmodCyclicMulEquiv isCyclic_pi_four_sphere_three).symm

/-- Computing the remaining modulus as two is exactly enough to close the first stable-stem
benchmark. -/
theorem piFourSphereThree_mulEquiv_zmod_two_of_modulus_eq
    (hmod : piFourSphereThreeModulus = 2) :
    Nonempty
      (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) := by
  exact ⟨piFourSphereThreeMulEquivZMod.trans
    (ZMod.ringEquivCongr hmod).toAddEquiv.toMultiplicative⟩

/-- Thus the first stable-stem benchmark is equivalent to the one remaining numerical
calculation: the cardinal modulus of `pi_4(S^3)` is two. -/
theorem piFourSphereThreeModulus_eq_two_iff :
    piFourSphereThreeModulus = 2 ↔
      Nonempty
        (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) := by
  constructor
  · exact piFourSphereThree_mulEquiv_zmod_two_of_modulus_eq
  · rintro ⟨e⟩
    rw [piFourSphereThreeModulus]
    calc
      Nat.card (π_ 4 (Sph 3) (sphereBasepoint 3)) =
          Nat.card (Multiplicative (ZMod 2)) := Nat.card_congr e.toEquiv
      _ = Nat.card (ZMod 2) := Nat.card_congr Multiplicative.toAdd
      _ = 2 := Nat.card_zmod 2

/-- Cap excision is bijective throughout the complete stable range. -/
theorem sphereSuspensionExcisionHomAt_bijective_of_stableRange
    (d q : ℕ) (hrange : q + 3 ≤ 2 * d) :
    Function.Bijective (sphereSuspensionExcisionHomAt d q) :=
  ⟨sphereSuspensionExcisionHomAt_injective_of_stableRange d q hrange,
    sphereSuspensionExcisionHomAt_surjective_of_freudenthalRange d q (by omega)⟩

/-- The named absolute cap-suspension comparison is bijective throughout the stable range. -/
theorem sphereCapSuspensionHomAt_bijective_of_stableRange
    (d q : ℕ) (hd : 1 ≤ d) (hrange : q + 3 ≤ 2 * d) :
    Function.Bijective (sphereCapSuspensionHomAt d q hd) :=
  sphereCapSuspensionHomAt_bijective_of_capExcision d q hd
    (sphereSuspensionExcisionHomAt_bijective_of_stableRange d q hrange)

/-- The stable-range sphere suspension excision assertion is now proved. -/
theorem sphereSuspensionExcisionStableRange_proved :
    SphereSuspensionExcisionStableRange := by
  intro m q _hm hrange
  exact sphereSuspensionExcisionHomAt_bijective_of_stableRange m q hrange

end Submission
