/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.EndpointCapSqueeze

/-!
# Source-pair bookkeeping for the endpoint cap squeeze

The stable cell-compression construction first raises the upper cap and then lowers both time
endpoints into the southern half-sphere.  This file performs those same two operations inside
the source lower-cap/overlap pair.  Consequently, the prepared endpoints used by compression
are represented by source loops relatively homotopic to the original source loops.

The second deformation keeps the equatorial vector fixed, interpolates the last coordinate
from `h` to `min h 0`, and radially normalizes.  It preserves the lower cap.  On the overlap it
also preserves the upper cap: nonpositive heights are fixed, while positive heights remain
nonnegative.

## Main results

* `Submission.upperCapSqueezeSourceRelGenLoop`
* `Submission.lowerHalfSqueezeSourceRelGenLoop`
* `Submission.endpointCapSqueezedSourceRelGenLoop`
* `Submission.relGenLoopHomotopic_endpointCapSqueezedSource`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d n q : ℕ}

/-! ### Lowering a lower-cap point into the southern half-sphere -/

theorem endpointCapSqueezeHeight_le_sphHeight
    (u : I) (z : Sph (d + 1)) :
    endpointCapSqueezeHeight u z ≤ sphHeight z := by
  have hmin : min (sphHeight z) 0 ≤ sphHeight z := min_le_left _ _
  have hmul : (u : ℝ) * (min (sphHeight z) 0 - sphHeight z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos u.2.1 (sub_nonpos.mpr hmin)
  rw [endpointCapSqueezeHeight]
  nlinarith

theorem endpointCapSqueezeAmbient_ne_zero_of_mem_lowerCap
    (u : I) {z : Sph (d + 1)} (hz : z ∈ sphLowerCap d) :
    endpointCapSqueezeAmbient u z ≠ 0 := by
  intro hzero
  have hnorth := (endpointCapSqueezeAmbient_eq_zero_imp u z hzero).1
  rw [hnorth, mem_sphLowerCap, sphHeight_sphNorthPole] at hz
  norm_num at hz

/-- The endpoint half-squeeze, restricted and bundled as a deformation of the lower cap. -/
noncomputable def lowerHalfSqueezeSourceDeformation :
    C(I × sphLowerCap d, sphLowerCap d) where
  toFun uz :=
    ⟨radialSpherePoint
        (endpointCapSqueezeAmbient uz.1 uz.2.1)
        (endpointCapSqueezeAmbient_ne_zero_of_mem_lowerCap uz.1 uz.2.2),
      by
        rw [mem_sphLowerCap]
        change radialProj (endpointCapSqueezeAmbient uz.1 uz.2.1)
          (Fin.last (d + 1)) ≤ 1 / 3
        rw [endpointCapSqueezeAmbient]
        apply radialProj_snocLp_last_le_third_of_le_sphHeight uz.2.1
        · exact endpointCapSqueezeAmbient_ne_zero_of_mem_lowerCap uz.1 uz.2.2
        · exact endpointCapSqueezeHeight_le_sphHeight uz.1 uz.2.1
        · have hz := uz.2.2
          rw [mem_sphLowerCap] at hz
          exact hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact continuous_endpointCapSqueezeAmbient.comp
        (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd))
    · intro uz
      exact endpointCapSqueezeAmbient_ne_zero_of_mem_lowerCap uz.1 uz.2.2

@[simp] theorem lowerHalfSqueezeSourceDeformation_zero
    (z : sphLowerCap d) :
    lowerHalfSqueezeSourceDeformation (0, z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change radialProj (endpointCapSqueezeAmbient 0 z.1) = z.1.1
  have hamb : endpointCapSqueezeAmbient 0 z.1 = z.1.1 := by
    rw [endpointCapSqueezeAmbient, endpointCapSqueezeHeight]
    norm_num
    exact snocLp_sphEquator_sphHeight z.1
  rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z.1)]

/-- The lower half-squeeze keeps an overlap point in the upper cap as well. -/
theorem lowerHalfSqueezeSourceDeformation_mem_overlap
    (u : I) {z : sphLowerCap d} (hz : z ∈ sphCapOverlapInLower d) :
    lowerHalfSqueezeSourceDeformation (u, z) ∈ sphCapOverlapInLower d := by
  have hzupper : z.1 ∈ sphUpperCap d := hz
  rw [mem_sphUpperCap] at hzupper
  change (lowerHalfSqueezeSourceDeformation (u, z)).1 ∈ sphUpperCap d
  rw [mem_sphUpperCap]
  change -(1 / 3 : ℝ) ≤ radialProj
    (endpointCapSqueezeAmbient u z.1) (Fin.last (d + 1))
  by_cases hh : sphHeight z.1 ≤ 0
  · have hamb : endpointCapSqueezeAmbient u z.1 = z.1.1 := by
      rw [endpointCapSqueezeAmbient, endpointCapSqueezeHeight,
        min_eq_left hh]
      have hheight :
          (1 - (u : ℝ)) * sphHeight z.1 + (u : ℝ) * sphHeight z.1 =
            sphHeight z.1 := by ring
      rw [hheight, snocLp_sphEquator_sphHeight]
    rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph z.1)]
    exact hzupper
  · apply le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
    apply radialProj_last_nonneg
    rw [endpointCapSqueezeAmbient, snocLp_last,
      endpointCapSqueezeHeight, min_eq_right (le_of_not_ge hh)]
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr u.2.2)
        (le_of_lt (lt_of_not_ge hh)))
      (mul_nonneg u.2.1 (le_refl 0))

@[simp] theorem lowerHalfSqueezeSourceDeformation_base
    (d : ℕ) (u : I) :
    lowerHalfSqueezeSourceDeformation (u, sphLowerCapBase d) =
      sphLowerCapBase d := by
  apply Subtype.ext
  apply Subtype.ext
  change radialProj
      (endpointCapSqueezeAmbient u (sphereBasepoint (d + 1))) =
    ((sphereBasepoint (d + 1) : Sph (d + 1)) :
      EuclideanSpace ℝ (Fin (d + 2)))
  have hamb : endpointCapSqueezeAmbient u (sphereBasepoint (d + 1)) =
      ((sphereBasepoint (d + 1) : Sph (d + 1)) :
        EuclideanSpace ℝ (Fin (d + 2))) := by
    rw [endpointCapSqueezeAmbient, endpointCapSqueezeHeight,
      sphHeight_sphereBasepoint_succ]
    norm_num
    exact snocLp_sphEquator_sphHeight (sphereBasepoint (d + 1))
  rw [hamb, radialProj_of_norm_eq_one
    (norm_coe_sph (sphereBasepoint (d + 1)))]

/-- Apply the full lower half-squeeze to a source relative loop. -/
noncomputable def lowerHalfSqueezeSourceRelGenLoop
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) where
  val := ⟨fun y => lowerHalfSqueezeSourceDeformation (1, p.val y),
    by fun_prop⟩
  property := by
    constructor
    · intro y hy
      exact lowerHalfSqueezeSourceDeformation_mem_overlap 1
        (p.property.1 y hy)
    · intro y hy
      change lowerHalfSqueezeSourceDeformation (1, p.val y) =
        sphLowerCapBase d
      rw [p.property.2 y hy]
      exact lowerHalfSqueezeSourceDeformation_base d 1

/-- The lower half-squeeze is a relative homotopy in the source pair. -/
theorem relGenLoopHomotopic_lowerHalfSqueezeSource
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop.Homotopic p (lowerHalfSqueezeSourceRelGenLoop p) := by
  refine ⟨⟨⟨fun sy => lowerHalfSqueezeSourceDeformation (sy.1, p.val sy.2),
    by fun_prop⟩,
    ?_, ?_⟩, ?_⟩
  · intro y
    exact lowerHalfSqueezeSourceDeformation_zero (p.val y)
  · intro y
    rfl
  · intro u
    constructor
    · intro y hy
      exact lowerHalfSqueezeSourceDeformation_mem_overlap u
        (p.property.1 y hy)
    · intro y hy
      change lowerHalfSqueezeSourceDeformation (u, p.val y) =
        sphLowerCapBase d
      rw [p.property.2 y hy]
      exact lowerHalfSqueezeSourceDeformation_base d u

/-! ### Raising the upper cap inside the source pair -/

/-- Apply the standard upper-cap squeeze while retaining the lower-cap subtype. -/
noncomputable def upperCapSqueezeSourceRelGenLoop
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) where
  val := ⟨fun y =>
      ⟨upperCapSqueezeSphere d (p.val y).1,
        upperCapSqueezeSphere_mem_lowerCap (p.val y).2⟩,
    by fun_prop⟩
  property := by
    constructor
    · intro y hy
      have hnonneg := upperCapSqueezeSphere_boundaryHeightNonneg
        (p.property.1 y hy)
      change upperCapSqueezeSphere d (p.val y).1 ∈ sphUpperCap d
      rw [mem_sphUpperCap]
      exact le_trans (by norm_num) hnonneg
    · intro y hy
      apply Subtype.ext
      have hp := p.property.2 y hy
      change p.val y = sphLowerCapBase d at hp
      change upperCapSqueezeSphere d (p.val y).1 =
        sphereBasepoint (d + 1)
      rw [hp]
      exact upperCapSqueezeSphere_base d

/-- The upper-cap squeeze is a relative homotopy in the source pair as well as in the target
pair. -/
theorem relGenLoopHomotopic_upperCapSqueezeSource
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop.Homotopic p (upperCapSqueezeSourceRelGenLoop p) := by
  refine ⟨⟨⟨fun sy =>
      ⟨upperCapSqueezeSphereHomotopy d (sy.1, (p.val sy.2).1),
        upperCapSqueezeSphereHomotopy_mem_lowerCap (p.val sy.2).2 sy.1⟩,
    ?_⟩, ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    exact (upperCapSqueezeSphereHomotopy d).continuous.comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp (p.val.continuous.comp continuous_snd)))
  · intro y
    apply Subtype.ext
    exact (upperCapSqueezeSphereHomotopy d).map_zero_left (p.val y).1
  · intro y
    apply Subtype.ext
    exact (upperCapSqueezeSphereHomotopy d).map_one_left (p.val y).1
  · intro u
    constructor
    · intro y hy
      exact upperCapSqueezeSphereHomotopy_mem_upperCap
        (p.property.1 y hy) u
    · intro y hy
      apply Subtype.ext
      change upperCapSqueezeSphereHomotopy d (u, (p.val y).1) =
        sphereBasepoint (d + 1)
      have hp := p.property.2 y hy
      change p.val y = sphLowerCapBase d at hp
      rw [hp]
      exact upperCapSqueezeSphereHomotopy_base d u

/-! ### The source representative appearing at a prepared compression endpoint -/

/-- First raise the upper cap and then lower into the southern half-sphere, exactly as at a time
endpoint of `endpointCapSqueezeRelativeSphereHomotopy`. -/
noncomputable def endpointCapSqueezedSourceRelGenLoop
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) :=
  lowerHalfSqueezeSourceRelGenLoop (upperCapSqueezeSourceRelGenLoop p)

/-- Endpoint preparation does not change the source relative homotopy class. -/
theorem relGenLoopHomotopic_endpointCapSqueezedSource
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) :
    RelGenLoop.Homotopic p (endpointCapSqueezedSourceRelGenLoop p) :=
  (relGenLoopHomotopic_upperCapSqueezeSource p).trans
    (relGenLoopHomotopic_lowerHalfSqueezeSource
      (upperCapSqueezeSourceRelGenLoop p))

/-! ### Identification with the endpoints of the prepared target homotopy -/

@[simp] theorem endpointCapSqueezedSourceRelGenLoop_apply
    (p : RelGenLoop n (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d)) (y : I^ Fin n) :
    (endpointCapSqueezedSourceRelGenLoop p).val y =
      lowerHalfSqueezeSourceDeformation
        (1, (upperCapSqueezeSourceRelGenLoop p).val y) :=
  rfl

/-- The time-zero endpoint of the target preparation is the inclusion of the prepared
time-zero source representative. -/
theorem endpointCapSqueezeIncludedSourceHomotopy_zero
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (y : I^ Fin (q + 2)) :
    endpointCapSqueezeRelativeSphereHomotopy
        (upperCapSqueezeRelativeSphereHomotopyMap H₀)
        (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
        (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2
        (0, y) =
      ((endpointCapSqueezedSourceRelGenLoop p).val y).1 := by
  apply Subtype.ext
  change radialProj
      (endpointCapSqueezeAmbient (endpointCapSqueezeWeight 0)
        (upperCapSqueezeSphere d (H₀ (0, y)))) =
    radialProj
      (endpointCapSqueezeAmbient 1
        (upperCapSqueezeSphere d (p.val y).1))
  rw [endpointCapSqueezeWeight_zero]
  have hzero := H₀.toHomotopy.apply_zero y
  change H₀ (0, y) = (p.val y).1 at hzero
  rw [hzero]

/-- The time-one endpoint of the target preparation is the inclusion of the prepared time-one
source representative. -/
theorem endpointCapSqueezeIncludedSourceHomotopy_one
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (y : I^ Fin (q + 2)) :
    endpointCapSqueezeRelativeSphereHomotopy
        (upperCapSqueezeRelativeSphereHomotopyMap H₀)
        (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
        (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2
        (1, y) =
      ((endpointCapSqueezedSourceRelGenLoop r).val y).1 := by
  apply Subtype.ext
  change radialProj
      (endpointCapSqueezeAmbient (endpointCapSqueezeWeight 1)
        (upperCapSqueezeSphere d (H₀ (1, y)))) =
    radialProj
      (endpointCapSqueezeAmbient 1
        (upperCapSqueezeSphere d (r.val y).1))
  rw [endpointCapSqueezeWeight_one]
  have hone := H₀.toHomotopy.apply_one y
  change H₀ (1, y) = (r.val y).1 at hone
  rw [hone]

/-! ### A named prepared homotopy and compression data with identified endpoints -/

/-- The target homotopy obtained by applying both cap preparations to a homotopy between
included source representatives. -/
noncomputable def includedSourcePreparedRelativeSphereHomotopy
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    C(I × I^ Fin (q + 2), Sph (d + 1)) :=
  endpointCapSqueezeRelativeSphereHomotopy
    (upperCapSqueezeRelativeSphereHomotopyMap H₀)
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2

@[simp] theorem includedSourcePreparedRelativeSphereHomotopy_zero
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (y : I^ Fin (q + 2)) :
    includedSourcePreparedRelativeSphereHomotopy H₀ (0, y) =
      ((endpointCapSqueezedSourceRelGenLoop p).val y).1 :=
  endpointCapSqueezeIncludedSourceHomotopy_zero H₀ y

@[simp] theorem includedSourcePreparedRelativeSphereHomotopy_one
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (y : I^ Fin (q + 2)) :
    includedSourcePreparedRelativeSphereHomotopy H₀ (1, y) =
      ((endpointCapSqueezedSourceRelGenLoop r).val y).1 :=
  endpointCapSqueezeIncludedSourceHomotopy_one H₀ y

theorem includedSourcePreparedRelativeSphereHomotopy_boundaryHeightNonneg
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    RelativeSphereHomotopy.BoundaryHeightNonneg
      (includedSourcePreparedRelativeSphereHomotopy H₀) :=
  endpointCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg
    (upperCapSqueezeRelativeSphereHomotopyMap H₀)
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2
    (upperCapSqueezeRelativeSphereHomotopy_boundaryHeightNonneg H₀)

theorem includedSourcePreparedRelativeSphereHomotopy_jarBased
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    RelativeSphereHomotopy.JarBased
      (includedSourcePreparedRelativeSphereHomotopy H₀) :=
  endpointCapSqueezeRelativeSphereHomotopy_jarBased
    (upperCapSqueezeRelativeSphereHomotopyMap H₀)
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2
    (upperCapSqueezeRelativeSphereHomotopy_jarBased H₀)

theorem includedSourcePreparedRelativeSphereHomotopy_endpointHeightNonpos
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d))) :
    RelativeSphereHomotopy.EndpointHeightNonpos
      (includedSourcePreparedRelativeSphereHomotopy H₀) :=
  endpointCapSqueezeRelativeSphereHomotopy_endpointHeightNonpos
    (upperCapSqueezeRelativeSphereHomotopyMap H₀)
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).1
    (upperCapSqueezeIncludedSourceHomotopy_endpoints_mem_lowerCap H₀).2

/-- Stable two-cell compression with the two time endpoints explicitly identified as inclusions
of source representatives homotopic to the original ones. -/
theorem exists_includedSourceHomotopy_cellCompression_with_prepared_endpoints
    {p r : RelGenLoop (q + 2) (sphLowerCap d)
      (sphCapOverlapInLower d) (sphCapOverlapBase d)}
    (H₀ : ContinuousMap.HomotopyWith
      (RelGenLoop.map (sphCapInclusionPairMap d) p).val
      (RelGenLoop.map (sphCapInclusionPairMap d) r).val
      (fun f => f ∈ RelGenLoop (q + 2) (Sph (d + 1))
        (sphUpperCap d) (sphUpperCapBase d)))
    (hrange : q + 3 ≤ 2 * d) :
    ∃ (H' : C(I × I^ Fin (q + 2), Sph (d + 1)))
      (_hzero' : ∀ z, H' (0, z) =
        ((endpointCapSqueezedSourceRelGenLoop p).val z).1)
      (_hone' : ∀ z, H' (1, z) =
        ((endpointCapSqueezedSourceRelGenLoop r).val z).1)
      (hheight' : RelativeSphereHomotopy.BoundaryHeightNonneg H')
      (hjar' : RelativeSphereHomotopy.JarBased H')
      (_hend' : RelativeSphereHomotopy.EndpointHeightNonpos H')
      (A : RelativeSpherePLHomotopyApproximation H' hheight' hjar')
      (x y : Sph (d + 1)),
      x ∉ sphUpperCap d ∧ y ∉ sphLowerCap d ∧
      ∃ g' : C(I^ Fin (q + 3), Sph (d + 1)),
        ∃ K : ContinuousMap.HomotopyRel
            (radialSphereCubeMap
              (cubeGridAffineApprox (q + 3) A.mesh
                (relativeSphereHomotopyToEuclidean H')) A.approx_ne_zero)
            g' (⊔I^(q + 3)),
          (∀ t z, z ∈ relativeSphereHomotopyLid q →
            K.toHomotopy (t, z) ≠ x) ∧
          ∀ z, g' z ≠ y := by
  let H' := includedSourcePreparedRelativeSphereHomotopy H₀
  let hheight' :=
    includedSourcePreparedRelativeSphereHomotopy_boundaryHeightNonneg H₀
  let hjar' := includedSourcePreparedRelativeSphereHomotopy_jarBased H₀
  let hend' :=
    includedSourcePreparedRelativeSphereHomotopy_endpointHeightNonpos H₀
  obtain ⟨A⟩ := exists_relativeSpherePLHomotopyApproximation H' hheight' hjar'
  obtain ⟨x, y, hx, hy, g', K, hK⟩ :=
    exists_relativeSpherePLHomotopy_cellCompression
      H' hheight' hjar' hend' A hrange
  refine ⟨H', ?_, ?_, hheight', hjar', hend', A,
    x, y, hx, hy, g', K, hK⟩
  · intro z
    exact includedSourcePreparedRelativeSphereHomotopy_zero H₀ z
  · intro z
    exact includedSourcePreparedRelativeSphereHomotopy_one H₀ z

end Submission
