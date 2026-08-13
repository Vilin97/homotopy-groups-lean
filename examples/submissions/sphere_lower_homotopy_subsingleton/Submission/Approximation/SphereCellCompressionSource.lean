/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCellPuncture

/-!
# Turning two-cell compression into a source-pair homotopy

After two-cell compression, the resulting sphere-valued cube avoids an upper-cell point `y`
everywhere and a lower-cell point `x` on its spatial lid.  The upper-puncture map therefore
lowers the whole cube into the lower cap without losing `x`-avoidance on the lid.  We then use
the last spatial coordinate as the strength of the lower-puncture raising map.  It is fully
applied exactly on the lid, where `x` is absent, and sends that lid into the cap overlap.  On
the spatial jar the compressed cube is based, so the construction remains based.

This file first packages that geometric operation independently of how the compressed cube was
obtained.  Subsequent results connect it to the PL compression data and its endpoint source
representatives.

## Main results

* `Submission.sphereCellUpperPunctureLowerCubeMap`
* `Submission.sphereCellCompressionSourceHomotopyMap`
* `Submission.sphereCellCompressionSourceSlice`
* `Submission.sphereCellCompressionSourceSlices_homotopic`
-/

open Set
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {d q : ℕ}

theorem sphHeight_lt_neg_third_of_not_mem_upperCap
    {x : Sph (d + 1)} (hx : x ∉ sphUpperCap d) :
    sphHeight x < -(1 / 3 : ℝ) := by
  rw [mem_sphUpperCap] at hx
  exact lt_of_not_ge hx

theorem third_lt_sphHeight_of_not_mem_lowerCap
    {y : Sph (d + 1)} (hy : y ∉ sphLowerCap d) :
    (1 / 3 : ℝ) < sphHeight y := by
  rw [mem_sphLowerCap] at hy
  exact lt_of_not_ge hy

/-- Apply upper-puncture lowering pointwise to a cube that avoids the puncture. -/
noncomputable def sphereCellUpperPunctureLowerCubeMap
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (g : C(I^ Fin (q + 3), Sph (d + 1)))
    (hgy : ∀ z, g z ≠ y) :
    C(I^ Fin (q + 3), sphLowerCap d) where
  toFun z :=
    ⟨upperCellPunctureLower y hy ⟨g z, hgy z⟩,
      upperCellPunctureLower_mem_lowerCap y hy ⟨g z, hgy z⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (upperCellPunctureLower y hy).continuous.comp
      (Continuous.subtype_mk g.continuous hgy)

@[simp] theorem sphereCellUpperPunctureLowerCubeMap_apply
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (g : C(I^ Fin (q + 3), Sph (d + 1)))
    (hgy : ∀ z, g z ≠ y) (z : I^ Fin (q + 3)) :
    (sphereCellUpperPunctureLowerCubeMap y hy g hgy z).1 =
      upperCellPunctureLower y hy ⟨g z, hgy z⟩ :=
  rfl

/-- A time-first full cube lies in the protected spatial lid when its spatial last coordinate
is one. -/
theorem fin_cons_mem_relativeSphereHomotopyLid_of_last_eq_one
    (t : I) (z : I^ Fin (q + 2))
    (hz : z (Fin.last (q + 1)) = 1) :
    (Fin.cons t z : I^ Fin (q + 3)) ∈ relativeSphereHomotopyLid q := by
  change (fun i : Fin (q + 2) =>
    Fin.cons (α := fun _ : Fin (q + 3) => I) t z i.succ) ∈
    Cube.boundaryLid (q + 2)
  change z (Fin.last (q + 1)) = 1
  exact hz

/-- The last spatial coordinate, used as the lower-puncture raising strength. -/
def spatialLidControl (z : I^ Fin (q + 2)) : I :=
  z (Fin.last (q + 1))

theorem continuous_spatialLidControl :
    Continuous (spatialLidControl : (I^ Fin (q + 2)) → I) :=
  continuous_apply (Fin.last (q + 1))

theorem spatialLidControl_eq_one_of_mem_boundaryLid
    {z : I^ Fin (q + 2)} (hz : z ∈ Cube.boundaryLid (q + 2)) :
    spatialLidControl z = 1 :=
  hz

/-- Use lower-puncture raising with the spatial lid coordinate after a cube has already been
lowered into the lower cap. -/
noncomputable def sphereCellCompressionSourceHomotopyMap
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x) :
    C(I × I^ Fin (q + 2), sphLowerCap d) where
  toFun tz :=
    let u := spatialLidControl tz.2
    let z := Fin.cons tz.1 tz.2
    let havoid : u = 1 → (L z).1 ≠ x := fun hu =>
      hLx z (fin_cons_mem_relativeSphereHomotopyLid_of_last_eq_one
        tz.1 tz.2 hu)
    ⟨lowerCellPunctureRaisePoint x hx u (L z).1 havoid,
      lowerCellPunctureRaisePoint_mem_lowerCap x hx u (L z).2 havoid⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
        ((continuous_spatialLidControl.comp continuous_snd).prodMk
          (continuous_subtype_val.comp
            (L.continuous.comp (by fun_prop))))
    · intro tz
      apply lowerCellPunctureRaiseAmbient_ne_zero x (L (Fin.cons tz.1 tz.2)).1 hx
      intro hu
      exact hLx (Fin.cons tz.1 tz.2)
        (fin_cons_mem_relativeSphereHomotopyLid_of_last_eq_one
          tz.1 tz.2 hu)

/-- On the spatial lid, the source homotopy map lands in the cap overlap. -/
theorem sphereCellCompressionSourceHomotopyMap_mem_overlap_of_mem_lid
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x)
    (t : I) {z : I^ Fin (q + 2)} (hz : z ∈ Cube.boundaryLid (q + 2)) :
    sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z) ∈
      sphCapOverlapInLower d := by
  change (sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z)).1 ∈
    sphUpperCap d
  have hu : spatialLidControl z = 1 :=
    spatialLidControl_eq_one_of_mem_boundaryLid hz
  let fullz : I^ Fin (q + 3) := Fin.cons t z
  have hfull : fullz ∈ relativeSphereHomotopyLid q :=
    fin_cons_mem_relativeSphereHomotopyLid_of_last_eq_one t z hu
  let havoid : spatialLidControl z = 1 → (L fullz).1 ≠ x :=
    fun _ => hLx fullz hfull
  change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
      (L fullz).1 havoid ∈ sphUpperCap d
  rw [mem_sphUpperCap]
  apply le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  change 0 ≤ radialProj
    (lowerCellPunctureRaiseAmbient x (spatialLidControl z) (L fullz).1)
      (Fin.last (d + 1))
  apply radialProj_last_nonneg
  rw [lowerCellPunctureRaiseAmbient_last x hx.ne, hu]
  by_cases hheight : sphHeight (L fullz).1 ≤ 0
  · rw [min_eq_left hheight]
    norm_num
  · rw [min_eq_right (le_of_not_ge hheight)]
    simpa using le_of_not_ge hheight

/-- If the lowered cube is based on the spatial jar, the raised source homotopy is based there
as well. -/
theorem sphereCellCompressionSourceHomotopyMap_eq_base_of_mem_jar
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x)
    (hLjar : ∀ t z, (z ∈ (⊔I^(q + 2))) →
      L (Fin.cons t z) = sphLowerCapBase d)
    (t : I) {z : I^ Fin (q + 2)} (hz : z ∈ ⊔I^(q + 2)) :
    sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z) =
      sphLowerCapBase d := by
  let havoid : spatialLidControl z = 1 →
      (L (Fin.cons t z)).1 ≠ x := fun hu =>
    hLx (Fin.cons t z)
      (fin_cons_mem_relativeSphereHomotopyLid_of_last_eq_one t z hu)
  apply Subtype.ext
  change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
      (L (Fin.cons t z)).1 havoid = sphereBasepoint (d + 1)
  have hbase : (L (Fin.cons t z)).1 = sphereBasepoint (d + 1) :=
    congrArg Subtype.val (hLjar t z hz)
  have hheight : 0 ≤ sphHeight (L (Fin.cons t z)).1 := by
    rw [hbase, sphHeight_sphereBasepoint_succ]
  exact (lowerCellPunctureRaisePoint_eq_of_height_nonneg
    x hx (spatialLidControl z) hheight havoid).trans hbase

/-- A time slice of the puncture-adjusted cube, bundled as a loop in the source pair. -/
noncomputable def sphereCellCompressionSourceSlice
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x)
    (hLjar : ∀ t z, (z ∈ (⊔I^(q + 2))) →
      L (Fin.cons t z) = sphLowerCapBase d)
    (t : I) :
    RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) where
  val := ⟨fun z => sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z),
    by fun_prop⟩
  property := by
    constructor
    · intro z hz
      rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary z hz with
        hlid | hjar
      · exact sphereCellCompressionSourceHomotopyMap_mem_overlap_of_mem_lid
          x hx L hLx t hlid
      · have hbase := sphereCellCompressionSourceHomotopyMap_eq_base_of_mem_jar
          x hx L hLx hLjar t hjar
        change sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z) ∈
          sphCapOverlapInLower d
        rw [hbase]
        exact (sphCapOverlapBase d).2
    · intro z hz
      change sphereCellCompressionSourceHomotopyMap x hx L hLx (t, z) =
        sphLowerCapBase d
      exact sphereCellCompressionSourceHomotopyMap_eq_base_of_mem_jar
        x hx L hLx hLjar t hz

/-- The two time slices of the adjusted cube are relatively homotopic in the source pair. -/
theorem sphereCellCompressionSourceSlices_homotopic
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x)
    (hLjar : ∀ t z, (z ∈ (⊔I^(q + 2))) →
      L (Fin.cons t z) = sphLowerCapBase d) :
    RelGenLoop.Homotopic
      (sphereCellCompressionSourceSlice x hx L hLx hLjar 0)
      (sphereCellCompressionSourceSlice x hx L hLx hLjar 1) := by
  refine ⟨⟨⟨fun tz => sphereCellCompressionSourceHomotopyMap x hx L hLx tz,
    (sphereCellCompressionSourceHomotopyMap x hx L hLx).continuous⟩,
    fun _ => rfl, fun _ => rfl⟩, fun t => ?_⟩
  exact (sphereCellCompressionSourceSlice x hx L hLx hLjar t).property

/-! ### Source lifts of the two PL time faces -/

/-- Bundle a target relative loop whose entire image lies in the lower cap as a loop in the
source lower-cap/overlap pair. -/
noncomputable def lowerCapLiftRelGenLoop
    (p : RelGenLoop (q + 2) (Sph (d + 1)) (sphUpperCap d)
      (sphUpperCapBase d))
    (hlower : ∀ z, p.val z ∈ sphLowerCap d) :
    RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) where
  val := ⟨fun z => ⟨p.val z, hlower z⟩, by fun_prop⟩
  property := by
    constructor
    · intro z hz
      exact p.property.1 z hz
    · intro z hz
      apply Subtype.ext
      exact p.property.2 z hz

@[simp] theorem lowerCapLiftRelGenLoop_apply
    (p : RelGenLoop (q + 2) (Sph (d + 1)) (sphUpperCap d)
      (sphUpperCapBase d))
    (hlower : ∀ z, p.val z ∈ sphLowerCap d) (z : I^ Fin (q + 2)) :
    ((lowerCapLiftRelGenLoop p hlower).val z).1 = p.val z :=
  rfl

theorem RelativeSpherePLHomotopyApproximation.approxSlice_zero_height_nonpos
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (z : I^ Fin (q + 2)) :
    sphHeight ((A.approxSlice 0).val z) ≤ 0 := by
  change radialProj
    (cubeGridAffineApprox (q + 3) A.mesh
      (relativeSphereHomotopyToEuclidean H) (Fin.cons 0 z))
      (Fin.last (d + 1)) ≤ 0
  exact radialProj_last_nonpos
    (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_zero
      A.mesh_pos H hend z)

theorem RelativeSpherePLHomotopyApproximation.approxSlice_one_height_nonpos
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (z : I^ Fin (q + 2)) :
    sphHeight ((A.approxSlice 1).val z) ≤ 0 := by
  change radialProj
    (cubeGridAffineApprox (q + 3) A.mesh
      (relativeSphereHomotopyToEuclidean H) (Fin.cons 1 z))
      (Fin.last (d + 1)) ≤ 0
  exact radialProj_last_nonpos
    (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_one
      A.mesh_pos H hend z)

theorem RelativeSpherePLHomotopyApproximation.approxSlice_boundaryHeightNonneg
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (s : I) {z : I^ Fin (q + 2)} (hz : z ∈ ∂I^(q + 2)) :
    0 ≤ sphHeight ((A.approxSlice s).val z) := by
  change 0 ≤ radialProj
    (cubeGridAffineApprox (q + 3) A.mesh
      (relativeSphereHomotopyToEuclidean H) (Fin.cons s z))
      (Fin.last (d + 1))
  exact radialProj_last_nonneg
    (cubeGridAffineApprox_relativeSphereHomotopy_last_nonneg
      A.mesh_pos H hheight s hz)

/-- The PL time-zero face, regarded as a source-pair representative. -/
noncomputable def RelativeSpherePLHomotopyApproximation.sourceZero
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H) :
    RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) :=
  lowerCapLiftRelGenLoop (A.approxSlice 0) fun z => by
    rw [mem_sphLowerCap]
    exact (A.approxSlice_zero_height_nonpos hend z).trans (by norm_num)

/-- The PL time-one face, regarded as a source-pair representative. -/
noncomputable def RelativeSpherePLHomotopyApproximation.sourceOne
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H) :
    RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) :=
  lowerCapLiftRelGenLoop (A.approxSlice 1) fun z => by
    rw [mem_sphLowerCap]
    exact (A.approxSlice_one_height_nonpos hend z).trans (by norm_num)

theorem RelativeSpherePLHomotopyApproximation.sourceZero_height_nonpos
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (z : I^ Fin (q + 2)) :
    sphHeight ((A.sourceZero hend).val z).1 ≤ 0 :=
  A.approxSlice_zero_height_nonpos hend z

theorem RelativeSpherePLHomotopyApproximation.sourceOne_height_nonpos
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (z : I^ Fin (q + 2)) :
    sphHeight ((A.sourceOne hend).val z).1 ≤ 0 :=
  A.approxSlice_one_height_nonpos hend z

theorem RelativeSpherePLHomotopyApproximation.sourceZero_boundaryHeightNonneg
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    {z : I^ Fin (q + 2)} (hz : z ∈ ∂I^(q + 2)) :
    0 ≤ sphHeight ((A.sourceZero hend).val z).1 :=
  A.approxSlice_boundaryHeightNonneg 0 hz

theorem RelativeSpherePLHomotopyApproximation.sourceOne_boundaryHeightNonneg
    {H : C(I × I^ Fin (q + 2), Sph (d + 1))}
    {hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H}
    {hjar : RelativeSphereHomotopy.JarBased H}
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    {z : I^ Fin (q + 2)} (hz : z ∈ ∂I^(q + 2)) :
    0 ≤ sphHeight ((A.sourceOne hend).val z).1 :=
  A.approxSlice_boundaryHeightNonneg 1 hz

/-! ### The endpoint collar deformation in the source pair -/

theorem mem_boundary_of_spatialLidControl_eq_one
    {z : I^ Fin (q + 2)} (hz : spatialLidControl z = 1) :
    z ∈ ∂I^(q + 2) :=
  ⟨Fin.last (q + 1), Or.inr hz⟩

theorem unitInterval_right_eq_one_of_mul_eq_one
    (s u : I) (h : s * u = 1) : u = 1 := by
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change (s : ℝ) * (u : ℝ) = 1 at hval
  have hle : (s : ℝ) * (u : ℝ) ≤ (u : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr s.2.2) u.2.1]
  have hu_ge : (1 : ℝ) ≤ (u : ℝ) := by
    calc
      (1 : ℝ) = (s : ℝ) * (u : ℝ) := hval.symm
      _ ≤ (u : ℝ) := hle
  exact le_antisymm u.2.2 hu_ge

/-- Raise a nonpositive source representative only according to the last spatial coordinate.
If its boundary has nonnegative height, that boundary has height zero and is fixed. -/
noncomputable def lowerCellCollarRaiseSourceRelGenLoop
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (p : RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d))
    (hpboundary : ∀ z, (z ∈ (∂I^(q + 2))) →
      0 ≤ sphHeight (p.val z).1) :
    RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d) where
  val := ⟨fun z =>
      let u := spatialLidControl z
      let havoid : u = 1 → (p.val z).1 ≠ x := fun hu hpx => by
        have hnonneg := hpboundary z
          (mem_boundary_of_spatialLidControl_eq_one hu)
        rw [hpx] at hnonneg
        linarith
      ⟨lowerCellPunctureRaisePoint x hx u (p.val z).1 havoid,
        lowerCellPunctureRaisePoint_mem_lowerCap x hx u (p.val z).2 havoid⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply continuous_radialProj
      · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
          (continuous_spatialLidControl.prodMk
            (continuous_subtype_val.comp p.val.continuous))
      · intro z
        apply lowerCellPunctureRaiseAmbient_ne_zero x (p.val z).1 hx
        intro hu hpx
        have hnonneg := hpboundary z
          (mem_boundary_of_spatialLidControl_eq_one hu)
        rw [hpx] at hnonneg
        linarith⟩
  property := by
    constructor
    · intro z hz
      have hnonneg := hpboundary z hz
      have havoid : spatialLidControl z = 1 → (p.val z).1 ≠ x :=
        fun _ hpx => by rw [hpx] at hnonneg; linarith
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (p.val z).1 havoid ∈ sphUpperCap d
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg havoid]
      exact p.property.1 z hz
    · intro z hz
      have hboundary := Cube.boundaryJar_subset_boundary (q + 2) hz
      have hnonneg := hpboundary z hboundary
      have havoid : spatialLidControl z = 1 → (p.val z).1 ≠ x :=
        fun _ hpx => by rw [hpx] at hnonneg; linarith
      apply Subtype.ext
      change lowerCellPunctureRaisePoint x hx (spatialLidControl z)
          (p.val z).1 havoid = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (spatialLidControl z) hnonneg havoid]
      exact congrArg Subtype.val (p.property.2 z hz)

/-- The spatial collar raise does not change the source relative homotopy class. -/
theorem relGenLoopHomotopic_lowerCellCollarRaiseSource
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (p : RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d))
    (hpboundary : ∀ z, (z ∈ (∂I^(q + 2))) →
      0 ≤ sphHeight (p.val z).1) :
    RelGenLoop.Homotopic p
      (lowerCellCollarRaiseSourceRelGenLoop x hx p hpboundary) := by
  let control : (I × (I^ Fin (q + 2))) → I :=
    fun (sz : I × (I^ Fin (q + 2))) =>
      sz.1 * spatialLidControl sz.2
  have hcontrol : Continuous control := by
    dsimp only [control]
    exact continuous_fst.mul
      (continuous_spatialLidControl.comp continuous_snd)
  have havoid : ∀ sz : I × I^ Fin (q + 2),
      control sz = 1 → (p.val sz.2).1 ≠ x := by
    intro sz hu hpx
    have hlast : spatialLidControl sz.2 = 1 :=
      unitInterval_right_eq_one_of_mul_eq_one sz.1
        (spatialLidControl sz.2) hu
    have hnonneg := hpboundary sz.2
      (mem_boundary_of_spatialLidControl_eq_one hlast)
    rw [hpx] at hnonneg
    linarith
  refine ⟨⟨⟨fun sz =>
      ⟨lowerCellPunctureRaisePoint x hx (control sz) (p.val sz.2).1
          (havoid sz),
        lowerCellPunctureRaisePoint_mem_lowerCap x hx (control sz)
          (p.val sz.2).2 (havoid sz)⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_radialProj
    · exact (continuous_lowerCellPunctureRaiseAmbient x).comp
        (hcontrol.prodMk
          (continuous_subtype_val.comp (p.val.continuous.comp continuous_snd)))
    · intro sz
      exact lowerCellPunctureRaiseAmbient_ne_zero x (p.val sz.2).1 hx
        (control sz) (havoid sz)
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj
      (lowerCellPunctureRaiseAmbient x (control (0, z)) (p.val z).1) =
        (p.val z).1.1
    have hcontrolzero : control (0, z) = 0 := by
      apply Subtype.ext
      simp [control]
    rw [hcontrolzero]
    have hamb : lowerCellPunctureRaiseAmbient x 0 (p.val z).1 =
        (p.val z).1.1 := by
      rw [lowerCellPunctureRaiseAmbient]
      norm_num
    rw [hamb, radialProj_of_norm_eq_one (norm_coe_sph (p.val z).1)]
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj
      (lowerCellPunctureRaiseAmbient x (control (1, z)) (p.val z).1) =
      radialProj
        (lowerCellPunctureRaiseAmbient x (spatialLidControl z) (p.val z).1)
    have hcontrolone : control (1, z) = spatialLidControl z := by
      apply Subtype.ext
      simp [control]
    rw [hcontrolone]
  · intro s
    constructor
    · intro z hz
      have hnonneg := hpboundary z hz
      change lowerCellPunctureRaisePoint x hx (control (s, z))
          (p.val z).1 (havoid (s, z)) ∈ sphUpperCap d
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (control (s, z)) hnonneg (havoid (s, z))]
      exact p.property.1 z hz
    · intro z hz
      have hnonneg := hpboundary z
        (Cube.boundaryJar_subset_boundary (q + 2) hz)
      apply Subtype.ext
      change lowerCellPunctureRaisePoint x hx (control (s, z))
          (p.val z).1 (havoid (s, z)) = sphereBasepoint (d + 1)
      rw [lowerCellPunctureRaisePoint_eq_of_height_nonneg
        x hx (control (s, z)) hnonneg (havoid (s, z))]
      exact congrArg Subtype.val (p.property.2 z hz)

/-- If a lowered full cube has a prescribed time face, then its adjusted source slice is exactly
the collar raise of that prescribed source representative. -/
theorem sphereCellCompressionSourceSlice_eq_lowerCellCollarRaiseSource
    (x : Sph (d + 1)) (hx : sphHeight x < 0)
    (L : C(I^ Fin (q + 3), sphLowerCap d))
    (hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x)
    (hLjar : ∀ t z, (z ∈ (⊔I^(q + 2))) →
      L (Fin.cons t z) = sphLowerCapBase d)
    (t : I)
    (p : RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d))
    (hpboundary : ∀ z, (z ∈ (∂I^(q + 2))) →
      0 ≤ sphHeight (p.val z).1)
    (hface : ∀ z, L (Fin.cons t z) = p.val z) :
    sphereCellCompressionSourceSlice x hx L hLx hLjar t =
      lowerCellCollarRaiseSourceRelGenLoop x hx p hpboundary := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Subtype.ext
  change radialProj
      (lowerCellPunctureRaiseAmbient x (spatialLidControl z)
        (L (Fin.cons t z)).1) =
    radialProj
      (lowerCellPunctureRaiseAmbient x (spatialLidControl z) (p.val z).1)
  rw [hface z]

/-! ### Applying the construction to PL cell-compression data -/

theorem compressedMap_ne_on_lid
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (x : Sph (d + 1))
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (hKx : ∀ t z, z ∈ relativeSphereHomotopyLid q →
      K.toHomotopy (t, z) ≠ x)
    (z : I^ Fin (q + 3)) (hz : z ∈ relativeSphereHomotopyLid q) :
    g' z ≠ x := by
  intro hgx
  exact hKx 1 z hz ((K.map_one_left z).trans hgx)

theorem compressedMap_eq_approxSlice_zero
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (z : I^ Fin (q + 2)) :
    g' (Fin.cons 0 z) = (A.approxSlice 0).val z := by
  let fullz : I^ Fin (q + 3) := Fin.cons 0 z
  calc
    g' fullz = radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero fullz :=
      (K.map_one_left fullz).symm.trans
        (K.prop' 1 fullz (Cube.mem_boundaryJar_cons_zero z))
    _ = (A.approxSlice 0).val z := by
      simpa only [fullz, Fin.cons_zero, Fin.cons_succ] using
        (radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
          H hheight hjar A fullz)

theorem compressedMap_eq_approxSlice_one
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (z : I^ Fin (q + 2)) :
    g' (Fin.cons 1 z) = (A.approxSlice 1).val z := by
  let fullz : I^ Fin (q + 3) := Fin.cons 1 z
  calc
    g' fullz = radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero fullz :=
      (K.map_one_left fullz).symm.trans
        (K.prop' 1 fullz (Cube.mem_boundaryJar_cons_one z))
    _ = (A.approxSlice 1).val z := by
      simpa only [fullz, Fin.cons_zero, Fin.cons_succ] using
        (radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
          H hheight hjar A fullz)

theorem compressedMap_eq_base_of_spatialJar
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (t : I) (z : I^ Fin (q + 2)) (hz : z ∈ ⊔I^(q + 2)) :
    g' (Fin.cons t z) = sphereBasepoint (d + 1) := by
  let fullz : I^ Fin (q + 3) := Fin.cons t z
  calc
    g' fullz = radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero fullz :=
      (K.map_one_left fullz).symm.trans
        (K.prop' 1 fullz (Cube.mem_boundaryJar_cons t hz))
    _ = (A.approxSlice t).val z := by
      simpa only [fullz, Fin.cons_zero, Fin.cons_succ] using
        (radialSphereCubeMap_eq_relativeSpherePLHomotopyApproximation_approxSlice
          H hheight hjar A fullz)
    _ = sphereBasepoint (d + 1) := (A.approxSlice t).property.2 z hz

/-- Upper-puncture lowering of the compressed map has the expected source PL time-zero face. -/
theorem sphereCellUpperPunctureLowerCubeMap_eq_sourceZero
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (hgy : ∀ z, g' z ≠ y)
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (z : I^ Fin (q + 2)) :
    sphereCellUpperPunctureLowerCubeMap y hy g' hgy (Fin.cons 0 z) =
      (A.sourceZero hend).val z := by
  let w := (A.approxSlice 0).val z
  have hw : sphHeight w ≤ 0 := A.approxSlice_zero_height_nonpos hend z
  have hwy : w ≠ y := by
    intro heq
    rw [heq] at hw
    linarith
  have hface : g' (Fin.cons 0 z) = w :=
    compressedMap_eq_approxSlice_zero H hheight hjar A g' K z
  have hcompl : (⟨g' (Fin.cons 0 z), hgy (Fin.cons 0 z)⟩ : SphPointCompl y) =
      ⟨w, hwy⟩ := Subtype.ext hface
  apply Subtype.ext
  change upperCellPunctureLower y hy
      ⟨g' (Fin.cons 0 z), hgy (Fin.cons 0 z)⟩ = w
  rw [hcompl]
  exact upperCellPunctureLower_eq_of_height_nonpos y hy hwy hw

/-- Upper-puncture lowering of the compressed map has the expected source PL time-one face. -/
theorem sphereCellUpperPunctureLowerCubeMap_eq_sourceOne
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (y : Sph (d + 1)) (hy : 0 < sphHeight y)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (hgy : ∀ z, g' z ≠ y)
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (z : I^ Fin (q + 2)) :
    sphereCellUpperPunctureLowerCubeMap y hy g' hgy (Fin.cons 1 z) =
      (A.sourceOne hend).val z := by
  let w := (A.approxSlice 1).val z
  have hw : sphHeight w ≤ 0 := A.approxSlice_one_height_nonpos hend z
  have hwy : w ≠ y := by
    intro heq
    rw [heq] at hw
    linarith
  have hface : g' (Fin.cons 1 z) = w :=
    compressedMap_eq_approxSlice_one H hheight hjar A g' K z
  have hcompl : (⟨g' (Fin.cons 1 z), hgy (Fin.cons 1 z)⟩ : SphPointCompl y) =
      ⟨w, hwy⟩ := Subtype.ext hface
  apply Subtype.ext
  change upperCellPunctureLower y hy
      ⟨g' (Fin.cons 1 z), hgy (Fin.cons 1 z)⟩ = w
  rw [hcompl]
  exact upperCellPunctureLower_eq_of_height_nonpos y hy hwy hw

/-- The complete puncture bridge: two-cell compression makes the two source PL endpoint
representatives relatively homotopic inside the lower-cap/overlap pair. -/
theorem relativeSpherePLHomotopy_cellCompression_sourceEndpoints_homotopic
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (x y : Sph (d + 1))
    (hx : x ∉ sphUpperCap d) (hy : y ∉ sphLowerCap d)
    (g' : C(I^ Fin (q + 3), Sph (d + 1)))
    (K : ContinuousMap.HomotopyRel
      (radialSphereCubeMap
        (cubeGridAffineApprox (q + 3) A.mesh
          (relativeSphereHomotopyToEuclidean H)) A.approx_ne_zero)
      g' (⊔I^(q + 3)))
    (hKx : ∀ t z, z ∈ relativeSphereHomotopyLid q →
      K.toHomotopy (t, z) ≠ x)
    (hgy : ∀ z, g' z ≠ y) :
    RelGenLoop.Homotopic (A.sourceZero hend) (A.sourceOne hend) := by
  have hxneg : sphHeight x < 0 :=
    (sphHeight_lt_neg_third_of_not_mem_upperCap hx).trans_le (by norm_num)
  have hypos : 0 < sphHeight y :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans
      (third_lt_sphHeight_of_not_mem_lowerCap hy)
  let L := sphereCellUpperPunctureLowerCubeMap y hypos g' hgy
  have hLx : ∀ z, z ∈ relativeSphereHomotopyLid q → (L z).1 ≠ x := by
    intro z hz
    exact upperCellPunctureLower_ne_of_ne hypos hxneg (hgy z)
      (compressedMap_ne_on_lid H hheight hjar A x g' K hKx z hz)
  have hLjar : ∀ t z, (z ∈ (⊔I^(q + 2))) →
      L (Fin.cons t z) = sphLowerCapBase d := by
    intro t z hz
    have hgbase := compressedMap_eq_base_of_spatialJar
      H hheight hjar A g' K t z hz
    have hybase : sphereBasepoint (d + 1) ≠ y := by
      intro heq
      have := congrArg sphHeight heq
      rw [sphHeight_sphereBasepoint_succ] at this
      linarith
    have hcompl :
        (⟨g' (Fin.cons t z), hgy (Fin.cons t z)⟩ : SphPointCompl y) =
          ⟨sphereBasepoint (d + 1), hybase⟩ := Subtype.ext hgbase
    apply Subtype.ext
    change upperCellPunctureLower y hypos
      ⟨g' (Fin.cons t z), hgy (Fin.cons t z)⟩ = sphereBasepoint (d + 1)
    rw [hcompl]
    exact upperCellPunctureLower_base y hypos hybase
  have hLzero : ∀ z, L (Fin.cons 0 z) = (A.sourceZero hend).val z :=
    sphereCellUpperPunctureLowerCubeMap_eq_sourceZero
      H hheight hjar A hend y hypos g' hgy K
  have hLone : ∀ z, L (Fin.cons 1 z) = (A.sourceOne hend).val z :=
    sphereCellUpperPunctureLowerCubeMap_eq_sourceOne
      H hheight hjar A hend y hypos g' hgy K
  have hzero := relGenLoopHomotopic_lowerCellCollarRaiseSource
    x hxneg (A.sourceZero hend)
      (fun z hz => A.sourceZero_boundaryHeightNonneg hend hz)
  have hone := relGenLoopHomotopic_lowerCellCollarRaiseSource
    x hxneg (A.sourceOne hend)
      (fun z hz => A.sourceOne_boundaryHeightNonneg hend hz)
  have hslices := sphereCellCompressionSourceSlices_homotopic
    x hxneg L hLx hLjar
  rw [sphereCellCompressionSourceSlice_eq_lowerCellCollarRaiseSource
      x hxneg L hLx hLjar 0 (A.sourceZero hend)
      (fun z hz => A.sourceZero_boundaryHeightNonneg hend hz) hLzero,
    sphereCellCompressionSourceSlice_eq_lowerCellCollarRaiseSource
      x hxneg L hLx hLjar 1 (A.sourceOne hend)
      (fun z hz => A.sourceOne_boundaryHeightNonneg hend hz) hLone] at hslices
  exact hzero.trans (hslices.trans hone.symm)

/-! ### Comparing the original prepared endpoints with their PL source lifts -/

theorem cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonpos_zero
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (N : ℕ) (hN : 1 ≤ N) (u : I) (z : I^ Fin (q + 2)) :
    cubeGridAffineApproxHomotopy (q + 3) N
      (relativeSphereHomotopyToEuclidean H) (u, Fin.cons 0 z)
        (Fin.last (d + 1)) ≤ 0 := by
  rw [cubeGridAffineApproxHomotopy_apply]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ),
    map_add, map_smul, map_smul]
  simp only [PiLp.projₗ_apply, smul_eq_mul,
    relativeSphereHomotopyToEuclidean_apply]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr u.2.2) (hend.1 z))
    (mul_nonpos_of_nonneg_of_nonpos u.2.1
      (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_zero
        hN H hend z))

theorem cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonpos_one
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (N : ℕ) (hN : 1 ≤ N) (u : I) (z : I^ Fin (q + 2)) :
    cubeGridAffineApproxHomotopy (q + 3) N
      (relativeSphereHomotopyToEuclidean H) (u, Fin.cons 1 z)
        (Fin.last (d + 1)) ≤ 0 := by
  rw [cubeGridAffineApproxHomotopy_apply]
  rw [← PiLp.projₗ_apply (𝕜 := ℝ) 2 (fun _ : Fin (d + 2) => ℝ),
    map_add, map_smul, map_smul]
  simp only [PiLp.projₗ_apply, smul_eq_mul,
    relativeSphereHomotopyToEuclidean_apply]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr u.2.2) (hend.2 z))
    (mul_nonpos_of_nonneg_of_nonpos u.2.1
      (cubeGridAffineApprox_relativeSphereHomotopy_last_nonpos_one
        hN H hend z))

/-- A prepared time-zero source representative is relatively homotopic, within the source pair,
to the source lift of its PL approximation. -/
theorem relativeSpherePLHomotopy_sourceZero_homotopic
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (p : RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d))
    (hzero : ∀ z, H (0, z) = (p.val z).1) :
    RelGenLoop.Homotopic p (A.sourceZero hend) := by
  let raw : C(I × I^ Fin (q + 2), EuclideanSpace ℝ (Fin (d + 2))) :=
    ⟨fun uz => cubeGridAffineApproxHomotopy (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H) (uz.1, Fin.cons 0 uz.2),
      (cubeGridAffineApproxHomotopy (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H)).continuous.comp (by fun_prop)⟩
  have hrawne : ∀ uz, raw uz ≠ 0 := fun uz =>
    A.comparison_ne_zero (uz.1, Fin.cons 0 uz.2)
  refine ⟨⟨⟨fun uz =>
      ⟨radialSpherePoint (raw uz) (hrawne uz), by
        rw [mem_sphLowerCap]
        change radialProj (raw uz) (Fin.last (d + 1)) ≤ 1 / 3
        exact (radialProj_last_nonpos
          (cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonpos_zero
            H hend A.mesh A.mesh_pos uz.1 uz.2)).trans (by norm_num)⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_radialProj raw.continuous hrawne⟩, ?_, ?_⟩, ?_⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (raw (0, z)) = (p.val z).1.1
    rw [show raw (0, z) = relativeSphereHomotopyToEuclidean H (Fin.cons 0 z) by
      exact cubeGridAffineApproxHomotopy_zero _ _]
    rw [relativeSphereHomotopyToEuclidean_apply, hzero,
      radialProj_of_norm_eq_one (norm_coe_sph (p.val z).1)]
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (raw (1, z)) = radialProj
      (cubeGridAffineApprox (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 0 z))
    exact congrArg radialProj (cubeGridAffineApproxHomotopy_one _ _)
  · intro u
    constructor
    · intro z hz
      change radialSpherePoint (raw (u, z)) (hrawne (u, z)) ∈ sphUpperCap d
      rw [mem_sphUpperCap]
      apply le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
      change 0 ≤ radialProj (raw (u, z)) (Fin.last (d + 1))
      apply radialProj_last_nonneg
      exact cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonneg
        A.mesh_pos H hheight u 0 hz
    · intro z hz
      apply Subtype.ext
      apply Subtype.ext
      change radialProj (raw (u, z)) =
        ((sphereBasepoint (d + 1) : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))
      have hrawbase :=
        cubeGridAffineApproxHomotopy_relativeSphereHomotopy_eq_on_boundaryJar
          A.mesh_pos H hjar u 0 hz
      change raw (u, z) = _ at hrawbase
      rw [hrawbase, radialProj_of_norm_eq_one
        (norm_coe_sph (sphereBasepoint (d + 1)))]

/-- The analogous source-pair comparison at time one. -/
theorem relativeSpherePLHomotopy_sourceOne_homotopic
    (H : C(I × I^ Fin (q + 2), Sph (d + 1)))
    (hheight : RelativeSphereHomotopy.BoundaryHeightNonneg H)
    (hjar : RelativeSphereHomotopy.JarBased H)
    (hend : RelativeSphereHomotopy.EndpointHeightNonpos H)
    (A : RelativeSpherePLHomotopyApproximation H hheight hjar)
    (p : RelGenLoop (q + 2) (sphLowerCap d) (sphCapOverlapInLower d)
      (sphCapOverlapBase d))
    (hone : ∀ z, H (1, z) = (p.val z).1) :
    RelGenLoop.Homotopic p (A.sourceOne hend) := by
  let raw : C(I × I^ Fin (q + 2), EuclideanSpace ℝ (Fin (d + 2))) :=
    ⟨fun uz => cubeGridAffineApproxHomotopy (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H) (uz.1, Fin.cons 1 uz.2),
      (cubeGridAffineApproxHomotopy (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H)).continuous.comp (by fun_prop)⟩
  have hrawne : ∀ uz, raw uz ≠ 0 := fun uz =>
    A.comparison_ne_zero (uz.1, Fin.cons 1 uz.2)
  refine ⟨⟨⟨fun uz =>
      ⟨radialSpherePoint (raw uz) (hrawne uz), by
        rw [mem_sphLowerCap]
        change radialProj (raw uz) (Fin.last (d + 1)) ≤ 1 / 3
        exact (radialProj_last_nonpos
          (cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonpos_one
            H hend A.mesh A.mesh_pos uz.1 uz.2)).trans (by norm_num)⟩,
    by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_radialProj raw.continuous hrawne⟩, ?_, ?_⟩, ?_⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (raw (0, z)) = (p.val z).1.1
    rw [show raw (0, z) = relativeSphereHomotopyToEuclidean H (Fin.cons 1 z) by
      exact cubeGridAffineApproxHomotopy_zero _ _]
    rw [relativeSphereHomotopyToEuclidean_apply, hone,
      radialProj_of_norm_eq_one (norm_coe_sph (p.val z).1)]
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (raw (1, z)) = radialProj
      (cubeGridAffineApprox (q + 3) A.mesh
        (relativeSphereHomotopyToEuclidean H) (Fin.cons 1 z))
    exact congrArg radialProj (cubeGridAffineApproxHomotopy_one _ _)
  · intro u
    constructor
    · intro z hz
      change radialSpherePoint (raw (u, z)) (hrawne (u, z)) ∈ sphUpperCap d
      rw [mem_sphUpperCap]
      apply le_trans (by norm_num : -(1 / 3 : ℝ) ≤ 0)
      change 0 ≤ radialProj (raw (u, z)) (Fin.last (d + 1))
      apply radialProj_last_nonneg
      exact cubeGridAffineApproxHomotopy_relativeSphereHomotopy_last_nonneg
        A.mesh_pos H hheight u 1 hz
    · intro z hz
      apply Subtype.ext
      apply Subtype.ext
      change radialProj (raw (u, z)) =
        ((sphereBasepoint (d + 1) : Sph (d + 1)) :
          EuclideanSpace ℝ (Fin (d + 2)))
      have hrawbase :=
        cubeGridAffineApproxHomotopy_relativeSphereHomotopy_eq_on_boundaryJar
          A.mesh_pos H hjar u 1 hz
      change raw (u, z) = _ at hrawbase
      rw [hrawbase, radialProj_of_norm_eq_one
        (norm_coe_sph (sphereBasepoint (d + 1)))]

end Submission
