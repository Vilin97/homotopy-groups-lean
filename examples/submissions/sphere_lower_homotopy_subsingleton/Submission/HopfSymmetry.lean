/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FirstStableStemPresentation
import Submission.Topology.SphereThreeGroup

/-!
# Reflection symmetry of the Hopf map and its suspension

Complex conjugation in both source coordinates of the quadratic Hopf map covers reflection in
one target coordinate.  The source conjugation is a based rotation through two real coordinates.
After suspension, the target reflection is based-homotopic to inversion on the unit-quaternion
three-sphere.  Thus the geometric suspension of the Hopf class is self-inverse.
-/

open scoped Topology Topology.Homotopy unitInterval
open unitInterval

noncomputable section

namespace Submission

/-! ### Complex conjugation symmetry of the quadratic Hopf map -/

/-- Simultaneous complex conjugation on the two complex coordinates of the Hopf source. -/
noncomputable def hopfSourceConjugationVec
    (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 0, -x 1, x 2, -x 3]

theorem norm_hopfSourceConjugationVec (x : EuclideanSpace ℝ (Fin 4)) :
    ‖hopfSourceConjugationVec x‖ = ‖x‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfSourceConjugationVec, Fin.sum_univ_succ]

theorem continuous_hopfSourceConjugationVec : Continuous hopfSourceConjugationVec := by
  unfold hopfSourceConjugationVec
  fun_prop

/-- Simultaneous complex conjugation as a based self-map of the exact three-sphere. -/
noncomputable def hopfSourceConjugation : C(Sph 3, Sph 3) where
  toFun x := ⟨hopfSourceConjugationVec x, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfSourceConjugationVec]
    exact mem_sphere_zero_iff_norm.mp x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_hopfSourceConjugationVec.comp continuous_subtype_val) _

@[simp]
theorem hopfSourceConjugation_basepoint :
    hopfSourceConjugation (sphereBasepoint 3) = sphereBasepoint 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hopfSourceConjugation, hopfSourceConjugationVec, sphereBasepoint]

/-- Reflection in the final coordinate of the Hopf target. -/
noncomputable def hopfTargetReflectionVec
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x 0, x 1, -x 2]

theorem norm_hopfTargetReflectionVec (x : EuclideanSpace ℝ (Fin 3)) :
    ‖hopfTargetReflectionVec x‖ = ‖x‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfTargetReflectionVec, Fin.sum_univ_succ]

theorem continuous_hopfTargetReflectionVec : Continuous hopfTargetReflectionVec := by
  unfold hopfTargetReflectionVec
  fun_prop

/-- Reflection in the final coordinate as a based self-map of the exact two-sphere. -/
noncomputable def hopfTargetReflection : C(Sph 2, Sph 2) where
  toFun x := ⟨hopfTargetReflectionVec x, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_hopfTargetReflectionVec]
    exact mem_sphere_zero_iff_norm.mp x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_hopfTargetReflectionVec.comp continuous_subtype_val) _

@[simp]
theorem hopfTargetReflection_basepoint :
    hopfTargetReflection (sphereBasepoint 2) = sphereBasepoint 2 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [hopfTargetReflection, hopfTargetReflectionVec, sphereBasepoint]

/-- Simultaneous source conjugation covers final-coordinate reflection under the quadratic Hopf
map. -/
theorem hopfMap_conjugation_equivariant :
    hopfMap.comp hopfSourceConjugation = hopfTargetReflection.comp hopfMap := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [hopfMap, hopfVec, hopfSourceConjugation, hopfSourceConjugationVec,
      hopfTargetReflection, hopfTargetReflectionVec]
  all_goals ring

/-! ### The source conjugation is based-homotopic to the identity -/

/-- Rotate the two conjugated coordinates simultaneously through an angle `πt`. -/
noncomputable def hopfSourceConjugationHomotopyVec
    (p : I × EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  let c := Real.cos (Real.pi * (p.1 : ℝ))
  let s := Real.sin (Real.pi * (p.1 : ℝ))
  WithLp.toLp 2 ![
    p.2 0,
    c * p.2 1 - s * p.2 3,
    p.2 2,
    s * p.2 1 + c * p.2 3]

theorem norm_hopfSourceConjugationHomotopyVec
    (p : I × EuclideanSpace ℝ (Fin 4)) :
    ‖hopfSourceConjugationHomotopyVec p‖ = ‖p.2‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [hopfSourceConjugationHomotopyVec, Fin.sum_univ_succ]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (p.1 : ℝ))]

theorem continuous_hopfSourceConjugationHomotopyVec :
    Continuous hopfSourceConjugationHomotopyVec := by
  unfold hopfSourceConjugationHomotopyVec
  fun_prop

/-- A based rotation from the identity of `S³` to simultaneous complex conjugation. -/
noncomputable def hopfSourceConjugationHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id (Sph 3)) hopfSourceConjugation where
  toFun p := ⟨hopfSourceConjugationHomotopyVec (p.1, p.2.1),
    mem_sphere_zero_iff_norm.mpr <| by
      rw [norm_hopfSourceConjugationHomotopyVec]
      exact mem_sphere_zero_iff_norm.mp p.2.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_hopfSourceConjugationHomotopyVec.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  map_zero_left x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [hopfSourceConjugationHomotopyVec]
  map_one_left x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [hopfSourceConjugationHomotopyVec, hopfSourceConjugation,
        hopfSourceConjugationVec]

/-- The source rotation fixes the standard sphere basepoint throughout. -/
theorem hopfSourceConjugationHomotopy_basepoint (t : I) :
    hopfSourceConjugationHomotopy (t, sphereBasepoint 3) = sphereBasepoint 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change hopfSourceConjugationHomotopyVec
      (t, (sphereBasepoint 3 : Sph 3)) i =
    ((sphereBasepoint 3 : Sph 3) : EuclideanSpace ℝ (Fin 4)) i
  fin_cases i <;>
    simp [hopfSourceConjugationHomotopyVec, sphereBasepoint]

/-- The Hopf map is based-homotopic to its postcomposition with target reflection. -/
noncomputable def hopfReflectionHomotopy :
    ContinuousMap.Homotopy hopfMap
      (hopfTargetReflection.comp hopfMap) :=
  ((ContinuousMap.Homotopy.refl hopfMap).comp
      hopfSourceConjugationHomotopy).cast rfl
    hopfMap_conjugation_equivariant

/-- The Hopf reflection homotopy fixes the standard source basepoint throughout. -/
theorem hopfReflectionHomotopy_basepoint (t : I) :
    hopfReflectionHomotopy (t, sphereBasepoint 3) = sphereBasepoint 2 := by
  change hopfMap
      (hopfSourceConjugationHomotopy (t, sphereBasepoint 3)) =
    sphereBasepoint 2
  rw [hopfSourceConjugationHomotopy_basepoint]
  exact hopfMap_basepoint

/-- Target reflection fixes the canonical Hopf generator in `π₃(S²)`. -/
theorem hopfTargetReflection_map_piThreeSphereTwoHopfGenerator :
    HomotopyGroup.map hopfTargetReflection hopfTargetReflection_basepoint
        piThreeSphereTwoHopfGenerator =
      piThreeSphereTwoHopfGenerator := by
  rw [piThreeSphereTwoHopfGenerator_eq_hopfMapClass,
    ← sphereTargetMapClass_comp 3 hopfMap hopfMap_basepoint
      hopfTargetReflection hopfTargetReflection_basepoint]
  exact (sphereTargetMapClass_eq_of_homotopy 3
    hopfMap_basepoint (by simp) hopfReflectionHomotopy
    hopfReflectionHomotopy_basepoint).symm

/-! ### The suspended target reflection and quaternionic inversion -/

/-- The coordinate reflection on `S³` obtained by suspending final-coordinate reflection on
`S²`. -/
noncomputable def sphereThreeHopfReflectionVec
    (x : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 0, x 1, -x 2, x 3]

theorem norm_sphereThreeHopfReflectionVec (x : EuclideanSpace ℝ (Fin 4)) :
    ‖sphereThreeHopfReflectionVec x‖ = ‖x‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [sphereThreeHopfReflectionVec, Fin.sum_univ_succ]

theorem continuous_sphereThreeHopfReflectionVec :
    Continuous sphereThreeHopfReflectionVec := by
  unfold sphereThreeHopfReflectionVec
  fun_prop

/-- The suspended Hopf-target reflection as an explicit based map of the exact three-sphere. -/
noncomputable def sphereThreeHopfReflection : C(Sph 3, Sph 3) where
  toFun x := ⟨sphereThreeHopfReflectionVec x, mem_sphere_zero_iff_norm.mpr <| by
    rw [norm_sphereThreeHopfReflectionVec]
    exact mem_sphere_zero_iff_norm.mp x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_sphereThreeHopfReflectionVec.comp continuous_subtype_val) _

@[simp]
theorem sphereThreeHopfReflection_basepoint :
    sphereThreeHopfReflection (sphereBasepoint 3) = sphereBasepoint 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphereThreeHopfReflection, sphereThreeHopfReflectionVec, sphereBasepoint]

/-- Suspending final-coordinate reflection on `S²` gives the displayed single-coordinate
reflection on `S³` exactly. -/
theorem sphereSuspensionMap_hopfTargetReflection :
    sphereSuspensionMap 2 2 hopfTargetReflection = sphereThreeHopfReflection := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨q, rfl⟩ := (suspSphHomeo 2).surjective z
  induction q using Susp.ind with
  | h p =>
      rcases p with ⟨t, x⟩
      rw [sphereSuspensionMap_apply_susp]
      apply Subtype.ext
      apply PiLp.ext
      intro i
      induction i using Fin.lastCases with
      | last =>
          change suspSphFun (t, hopfTargetReflection x) (Fin.last 3) =
            sphereThreeHopfReflectionVec (suspSphFun (t, x)) (Fin.last 3)
          simp [suspSphFun, sphereThreeHopfReflectionVec, snocLp, Fin.snoc]
      | cast j =>
          change suspSphFun (t, hopfTargetReflection x) j.castSucc =
            sphereThreeHopfReflectionVec (suspSphFun (t, x)) j.castSucc
          fin_cases j <;> simp [suspSphFun, sphereThreeHopfReflectionVec, snocLp, Fin.snoc,
            hopfTargetReflection, hopfTargetReflectionVec]

/-! ### Reflection naturality of the cap suspension comparison -/

/-- The chosen cap-overlap equivalence intertwines the suspended overlap reflection with the
original Hopf-target reflection. -/
theorem sphCapOverlapHomotopyEquiv_hopfTargetReflection
    (z : sphCapOverlapInLower 2) :
    sphCapOverlapHomotopyEquiv 2
        ((sphCapSourcePairMap 2 hopfTargetReflection
          hopfTargetReflection_basepoint).subspaceMap z) =
      hopfTargetReflection (sphCapOverlapHomotopyEquiv 2 z) := by
  change
    (sphBeltHomeo 2
      (sphCapOverlapHomeoBelt 2
        ((sphCapSourcePairMap 2 hopfTargetReflection
          hopfTargetReflection_basepoint).subspaceMap z))).1 =
      hopfTargetReflection
        (sphBeltHomeo 2 (sphCapOverlapHomeoBelt 2 z)).1
  let p := sphBeltHomeo 2 (sphCapOverlapHomeoBelt 2 z)
  have hpair :
      sphBeltHomeo 2
          (sphCapOverlapHomeoBelt 2
            ((sphCapSourcePairMap 2 hopfTargetReflection
              hopfTargetReflection_basepoint).subspaceMap z)) =
        (hopfTargetReflection p.1, p.2) := by
    apply (sphBeltHomeo 2).symm.injective
    rw [Homeomorph.symm_apply_apply]
    change sphCapOverlapHomeoBelt 2
        ((sphCapSourcePairMap 2 hopfTargetReflection
          hopfTargetReflection_basepoint).subspaceMap z) =
      beltOfProd (hopfTargetReflection p.1, p.2)
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hz : sphCapOverlapHomeoBelt 2 z = beltOfProd p := by
      change sphCapOverlapHomeoBelt 2 z = (sphBeltHomeo 2).symm p
      exact ((sphBeltHomeo 2).symm_apply_apply
        (sphCapOverlapHomeoBelt 2 z)).symm
    have hzval := congrArg
      (fun w : sphBelt 2 ↦ (((w : Sph 3) : EuclideanSpace ℝ (Fin 4)) i)) hz
    change
      (((sphereSuspensionMap 2 2 hopfTargetReflection z.1.1 : Sph 3) :
        EuclideanSpace ℝ (Fin 4)) i) =
      (((beltOfProd (hopfTargetReflection p.1, p.2) : sphBelt 2) : Sph 3) :
        EuclideanSpace ℝ (Fin 4)) i
    rw [sphereSuspensionMap_hopfTargetReflection]
    fin_cases i <;>
      simp [sphCapOverlapHomeoBelt, sphereThreeHopfReflection,
        sphereThreeHopfReflectionVec, beltOfProd, beltVec,
        hopfTargetReflection, hopfTargetReflectionVec, snocLp, Fin.snoc] at hzval ⊢ <;>
      exact hzval
  exact congrArg Prod.fst hpair

/-- The raw cap suspension comparison commutes with Hopf-target reflection. -/
theorem sphereCapSuspensionRawHomAt_hopfTargetReflection
    (a : π_ 3 (Sph 2)
      (sphCapOverlapHomotopyEquiv 2 (sphCapOverlapBase 2))) :
    HomotopyGroup.map sphereThreeHopfReflection
        sphereThreeHopfReflection_basepoint
        (sphereCapSuspensionRawHomAt 2 2 a) =
      sphereCapSuspensionRawHomAt 2 2
        (HomotopyGroup.map hopfTargetReflection (by simp) a) := by
  have hsource : (sphCapOverlapHomotopyEquiv 2).toFun.comp
        (sphCapSourcePairMap 2 hopfTargetReflection
          hopfTargetReflection_basepoint).subspaceMap =
      hopfTargetReflection.comp (sphCapOverlapHomotopyEquiv 2).toFun := by
    apply ContinuousMap.ext
    exact sphCapOverlapHomotopyEquiv_hopfTargetReflection
  simpa only [sphereSuspensionMap_hopfTargetReflection] using
    sphereCapSuspensionRawHomAt_natural 2 2 hopfTargetReflection
      hopfTargetReflection_basepoint hsource a

/-- Reflection commutes with transport along the explicitly constant overlap basepoint path. -/
theorem hopfTargetReflection_map_transport_sphCapOverlapBasePath
    (a : π_ 3 (Sph 2) (sphereBasepoint 2)) :
    HomotopyGroup.map hopfTargetReflection (by simp)
        (HomotopyGroup.transport (sphCapOverlapBasePath 2) a) =
      HomotopyGroup.transport (sphCapOverlapBasePath 2)
        (HomotopyGroup.map hopfTargetReflection
          hopfTargetReflection_basepoint a) := by
  induction a using Quotient.ind with
  | _ p =>
      rw [HomotopyGroup.transport_mk, HomotopyGroup.map_mk,
        HomotopyGroup.map_mk, HomotopyGroup.transport_mk]
      apply congrArg Quotient.mk'
      apply GenLoop.ext
      intro t
      simp only [GenLoop.map_apply, GenLoop.transport_apply]
      unfold transportFun
      split_ifs
      · rfl
      · rw [sphCapOverlapBasePath_apply]
        exact hopfTargetReflection_basepoint

/-- The based cap suspension comparison commutes with Hopf-target reflection. -/
theorem sphereCapSuspensionHomAt_hopfTargetReflection
    (a : π_ 3 (Sph 2) (sphereBasepoint 2)) :
    HomotopyGroup.map sphereThreeHopfReflection
        sphereThreeHopfReflection_basepoint
        (sphereCapSuspensionHomAt 2 2 (by omega) a) =
      sphereCapSuspensionHomAt 2 2 (by omega)
        (HomotopyGroup.map hopfTargetReflection
          hopfTargetReflection_basepoint a) := by
  change HomotopyGroup.map sphereThreeHopfReflection
      sphereThreeHopfReflection_basepoint
      (sphereCapSuspensionRawHomAt 2 2
        (HomotopyGroup.transportMulEquiv (sphCapOverlapBasePath 2) a)) =
    sphereCapSuspensionRawHomAt 2 2
      (HomotopyGroup.transportMulEquiv (sphCapOverlapBasePath 2)
        (HomotopyGroup.map hopfTargetReflection
          hopfTargetReflection_basepoint a))
  rw [sphereCapSuspensionRawHomAt_hopfTargetReflection]
  exact congrArg (sphereCapSuspensionRawHomAt 2 2)
    (hopfTargetReflection_map_transport_sphCapOverlapBasePath a)

/-- Quaternionic inversion as a continuous based self-map of the exact three-sphere. -/
noncomputable def sphereThreeInversion : C(Sph 3, Sph 3) where
  toFun x := x⁻¹
  continuous_toFun := continuous_inv

@[simp]
theorem sphereThreeInversion_basepoint :
    sphereThreeInversion (sphereBasepoint 3) = sphereBasepoint 3 := by
  rw [← sphereThree_one_eq_basepoint]
  exact inv_one

/-- Rotate the first and third imaginary coordinates while keeping the second one reflected. -/
noncomputable def sphereThreeHopfReflectionInvHomotopyVec
    (p : I × EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  let c := Real.cos (Real.pi * (p.1 : ℝ))
  let s := Real.sin (Real.pi * (p.1 : ℝ))
  WithLp.toLp 2 ![
    p.2 0,
    c * p.2 1 - s * p.2 3,
    -p.2 2,
    s * p.2 1 + c * p.2 3]

theorem norm_sphereThreeHopfReflectionInvHomotopyVec
    (p : I × EuclideanSpace ℝ (Fin 4)) :
    ‖sphereThreeHopfReflectionInvHomotopyVec p‖ = ‖p.2‖ := by
  apply eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [sphereThreeHopfReflectionInvHomotopyVec, Fin.sum_univ_succ]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (p.1 : ℝ))]

theorem continuous_sphereThreeHopfReflectionInvHomotopyVec :
    Continuous sphereThreeHopfReflectionInvHomotopyVec := by
  unfold sphereThreeHopfReflectionInvHomotopyVec
  fun_prop

/-- The suspended target reflection is based-homotopic to quaternionic inversion. -/
noncomputable def sphereThreeHopfReflectionInvHomotopy :
    ContinuousMap.Homotopy sphereThreeHopfReflection sphereThreeInversion where
  toFun p := ⟨sphereThreeHopfReflectionInvHomotopyVec (p.1, p.2.1),
    mem_sphere_zero_iff_norm.mpr <| by
      rw [norm_sphereThreeHopfReflectionInvHomotopyVec]
      exact mem_sphere_zero_iff_norm.mp p.2.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_sphereThreeHopfReflectionInvHomotopyVec.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  map_zero_left x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [sphereThreeHopfReflectionInvHomotopyVec,
        sphereThreeHopfReflection, sphereThreeHopfReflectionVec]
  map_one_left x := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    change sphereThreeHopfReflectionInvHomotopyVec
        (1, (x : EuclideanSpace ℝ (Fin 4))) i =
      (((x⁻¹ : Sph 3) : EuclideanSpace ℝ (Fin 4))) i
    rw [sphereThree_inv_apply]
    fin_cases i <;>
      simp [sphereThreeHopfReflectionInvHomotopyVec]

/-- The reflection-to-inversion rotation fixes the standard basepoint throughout. -/
theorem sphereThreeHopfReflectionInvHomotopy_basepoint (t : I) :
    sphereThreeHopfReflectionInvHomotopy (t, sphereBasepoint 3) = sphereBasepoint 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change sphereThreeHopfReflectionInvHomotopyVec
      (t, (sphereBasepoint 3 : Sph 3)) i =
    ((sphereBasepoint 3 : Sph 3) : EuclideanSpace ℝ (Fin 4)) i
  fin_cases i <;>
    simp [sphereThreeHopfReflectionInvHomotopyVec, sphereBasepoint]

/-! ### The suspended Hopf map is fixed by target reflection -/

/-- Suspending the conjugation symmetry expresses postcomposition by the displayed reflection
as precomposition by the suspended source conjugation. -/
theorem suspendedHopfMap_reflection_equivariant :
    (sphereSuspensionMap 3 2 hopfMap).comp
        (sphereSuspensionMap 3 3 hopfSourceConjugation) =
      sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap) := by
  calc
    (sphereSuspensionMap 3 2 hopfMap).comp
          (sphereSuspensionMap 3 3 hopfSourceConjugation) =
        sphereSuspensionMap 3 2 (hopfMap.comp hopfSourceConjugation) :=
      (sphereSuspensionMap_comp 3 3 2 hopfMap hopfSourceConjugation).symm
    _ = sphereSuspensionMap 3 2 (hopfTargetReflection.comp hopfMap) :=
      congrArg (sphereSuspensionMap 3 2) hopfMap_conjugation_equivariant
    _ = (sphereSuspensionMap 2 2 hopfTargetReflection).comp
          (sphereSuspensionMap 3 2 hopfMap) :=
      sphereSuspensionMap_comp 3 2 2 hopfTargetReflection hopfMap
    _ = sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap) := by
      rw [sphereSuspensionMap_hopfTargetReflection]

/-- Rotating the suspended source conjugation to the identity gives a based homotopy from the
suspended Hopf map to its postcomposition with target reflection. -/
noncomputable def suspendedHopfReflectionHomotopy :
    ContinuousMap.Homotopy
      (sphereSuspensionMap 3 2 hopfMap)
      (sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap)) :=
  ((ContinuousMap.Homotopy.refl (sphereSuspensionMap 3 2 hopfMap)).comp
      (sphereSuspensionMapHomotopy 3 3 hopfSourceConjugationHomotopy)).cast
    (by
      rw [← sphereSuspensionSelfMap_eq_sphereSuspensionMap,
        sphereSuspensionSelfMap_id]
      rfl)
    suspendedHopfMap_reflection_equivariant

/-- The reflection symmetry homotopy fixes the standard source basepoint throughout. -/
theorem suspendedHopfReflectionHomotopy_basepoint (t : I) :
    suspendedHopfReflectionHomotopy (t, sphereBasepoint 4) = sphereBasepoint 3 := by
  change sphereSuspensionMap 3 2 hopfMap
      (sphereSuspensionMapHomotopy 3 3 hopfSourceConjugationHomotopy
        (t, sphereBasepoint 4)) = sphereBasepoint 3
  rw [sphereSuspensionMapHomotopy_basepoint 3 3 hopfSourceConjugationHomotopy
      hopfSourceConjugationHomotopy_basepoint]
  exact sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint

@[simp]
theorem sphereThreeHopfReflection_comp_suspendedHopfMap_basepoint :
    (sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap))
        (sphereBasepoint 4) = sphereBasepoint 3 := by
  rw [ContinuousMap.comp_apply,
    sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint,
    sphereThreeHopfReflection_basepoint]

@[simp]
theorem sphereThreeInversion_comp_suspendedHopfMap_basepoint :
    (sphereThreeInversion.comp (sphereSuspensionMap 3 2 hopfMap))
        (sphereBasepoint 4) = sphereBasepoint 3 := by
  rw [ContinuousMap.comp_apply,
    sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint,
    sphereThreeInversion_basepoint]

/-- Postcomposing the suspended Hopf map with the reflection-to-inversion rotation. -/
noncomputable def suspendedHopfInversionHomotopy :
    ContinuousMap.Homotopy
      (sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap))
      (sphereThreeInversion.comp (sphereSuspensionMap 3 2 hopfMap)) :=
  sphereThreeHopfReflectionInvHomotopy.compContinuousMap
    (sphereSuspensionMap 3 2 hopfMap)

/-- The postcomposition homotopy also fixes the standard source basepoint. -/
theorem suspendedHopfInversionHomotopy_basepoint (t : I) :
    suspendedHopfInversionHomotopy (t, sphereBasepoint 4) = sphereBasepoint 3 := by
  change sphereThreeHopfReflectionInvHomotopy
      (t, sphereSuspensionMap 3 2 hopfMap (sphereBasepoint 4)) = sphereBasepoint 3
  rw [sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint]
  exact sphereThreeHopfReflectionInvHomotopy_basepoint t

/-- The suspended Hopf representative and its pointwise quaternionic inverse determine the
same based homotopy class. -/
theorem suspendedHopfMapClass_eq_inversionClass :
    sphereTargetMapClass 4 (sphereSuspensionMap 3 2 hopfMap)
        (sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint) =
      sphereTargetMapClass 4
        (sphereThreeInversion.comp (sphereSuspensionMap 3 2 hopfMap))
        sphereThreeInversion_comp_suspendedHopfMap_basepoint := by
  calc
    sphereTargetMapClass 4 (sphereSuspensionMap 3 2 hopfMap)
          (sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint) =
        sphereTargetMapClass 4
          (sphereThreeHopfReflection.comp (sphereSuspensionMap 3 2 hopfMap))
          sphereThreeHopfReflection_comp_suspendedHopfMap_basepoint :=
      sphereTargetMapClass_eq_of_homotopy 4
        (sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint)
        sphereThreeHopfReflection_comp_suspendedHopfMap_basepoint
        suspendedHopfReflectionHomotopy suspendedHopfReflectionHomotopy_basepoint
    _ = sphereTargetMapClass 4
          (sphereThreeInversion.comp (sphereSuspensionMap 3 2 hopfMap))
          sphereThreeInversion_comp_suspendedHopfMap_basepoint :=
      sphereTargetMapClass_eq_of_homotopy 4
        sphereThreeHopfReflection_comp_suspendedHopfMap_basepoint
        sphereThreeInversion_comp_suspendedHopfMap_basepoint
        suspendedHopfInversionHomotopy suspendedHopfInversionHomotopy_basepoint

/-! ### The geometric first-stem generator has square one -/

/-- Inversion postcomposition preserves a sphere map based at the quaternionic identity. -/
theorem sphereThreeInversion_comp_basepoint_one (f : C(Sph 4, Sph 3))
    (hf : f (sphereBasepoint 4) = (1 : Sph 3)) :
    (sphereThreeInversion.comp f) (sphereBasepoint 4) = (1 : Sph 3) := by
  rw [ContinuousMap.comp_apply, hf]
  exact inv_one

/-- A class represented by a map into the quaternionic three-sphere, multiplied on the left by
the class of its pointwise inverse, is trivial. -/
theorem sphereThreeInversionClass_mul_self (f : C(Sph 4, Sph 3))
    (hf : f (sphereBasepoint 4) = (1 : Sph 3)) :
      sphereTargetMapClass (x := (1 : Sph 3)) 4 (sphereThreeInversion.comp f)
        (sphereThreeInversion_comp_basepoint_one f hf) *
      sphereTargetMapClass (x := (1 : Sph 3)) 4 f hf = 1 := by
  let p : Ω^ (Fin 4) (Sph 3) (1 : Sph 3) := sphereTargetMapGenLoop 4 f hf
  have hinv :
      sphereTargetMapGenLoop 4 (sphereThreeInversion.comp f)
          (sphereThreeInversion_comp_basepoint_one f hf) =
        GenLoop.pointwiseInv p := by
    apply GenLoop.ext
    intro u
    rfl
  have hmul :=
    (HomotopyGroup.pointwiseMulClass_pointwiseInv p).trans
      _root_.HomotopyGroup.one_def.symm
  rw [HomotopyGroup.pointwiseMulClass_eq_mul] at hmul
  simpa only [sphereTargetMapClass, hinv] using hmul

/-- Inversion preserves any chosen target basepoint that is identified with the quaternionic
identity. -/
theorem sphereThreeInversion_comp_basepoint_of_eq_one (x : Sph 3)
    (hx : x = (1 : Sph 3)) (f : C(Sph 4, Sph 3))
    (hf : f (sphereBasepoint 4) = x) :
    (sphereThreeInversion.comp f) (sphereBasepoint 4) = x := by
  rw [ContinuousMap.comp_apply, hf, hx]
  exact inv_one

/-- The pointwise-inverse cancellation formula transported to a basepoint identified with the
quaternionic identity. -/
theorem sphereThreeInversionClass_mul_self_of_eq_one (x : Sph 3)
    (hx : x = (1 : Sph 3)) (f : C(Sph 4, Sph 3))
    (hf : f (sphereBasepoint 4) = x) :
    sphereTargetMapClass (x := x) 4 (sphereThreeInversion.comp f)
        (sphereThreeInversion_comp_basepoint_of_eq_one x hx f hf) *
      sphereTargetMapClass (x := x) 4 f hf = 1 := by
  subst x
  exact sphereThreeInversionClass_mul_self f hf

/-- Postcomposition by quaternionic inversion sends every class in `π₄(S³)` to a
left inverse. -/
theorem sphereThreeInversion_map_mul_self
    (a : π_ 4 (Sph 3) (sphereBasepoint 3)) :
    HomotopyGroup.map sphereThreeInversion sphereThreeInversion_basepoint a * a = 1 := by
  obtain ⟨f, hf, hfa⟩ := homotopyGroup_exists_sphereTargetMapRepresentative 3 a
  rw [← hfa, ← sphereTargetMapClass_comp 4 f hf sphereThreeInversion
    sphereThreeInversion_basepoint]
  exact sphereThreeInversionClass_mul_self_of_eq_one
    (sphereBasepoint 3) sphereThree_one_eq_basepoint.symm f hf

/-- The suspended reflection and quaternionic inversion induce the same map on `π₄(S³)`. -/
theorem sphereThreeHopfReflection_map_eq_inversion
    (a : π_ 4 (Sph 3) (sphereBasepoint 3)) :
    HomotopyGroup.map sphereThreeHopfReflection
        sphereThreeHopfReflection_basepoint a =
      HomotopyGroup.map sphereThreeInversion
        sphereThreeInversion_basepoint a := by
  obtain ⟨f, hf, hfa⟩ := homotopyGroup_exists_sphereTargetMapRepresentative 3 a
  rw [← hfa, ← sphereTargetMapClass_comp 4 f hf sphereThreeHopfReflection
    sphereThreeHopfReflection_basepoint,
    ← sphereTargetMapClass_comp 4 f hf sphereThreeInversion
      sphereThreeInversion_basepoint]
  exact sphereTargetMapClass_eq_of_homotopy 4 (by simp [hf]) (by simp [hf])
    (sphereThreeHopfReflectionInvHomotopy.compContinuousMap f) (fun t ↦ by
      change sphereThreeHopfReflectionInvHomotopy
        (t, f (sphereBasepoint 4)) = sphereBasepoint 3
      rw [hf]
      exact sphereThreeHopfReflectionInvHomotopy_basepoint t)

/-- Postcomposition by the suspended reflection sends every class in `π₄(S³)` to a
left inverse. -/
theorem sphereThreeHopfReflection_map_mul_self
    (a : π_ 4 (Sph 3) (sphereBasepoint 3)) :
    HomotopyGroup.map sphereThreeHopfReflection
        sphereThreeHopfReflection_basepoint a * a = 1 := by
  rw [sphereThreeHopfReflection_map_eq_inversion]
  exact sphereThreeInversion_map_mul_self a

/-! ### The cap-excision first-stem generator has square one -/

/-- The reflection fixes the distinguished Freudenthal-edge generator. -/
theorem piFourSphereThreeEdgeGenerator_reflection :
    HomotopyGroup.map sphereThreeHopfReflection
        sphereThreeHopfReflection_basepoint piFourSphereThreeEdgeGenerator =
      piFourSphereThreeEdgeGenerator := by
  rw [piFourSphereThreeEdgeGenerator,
    sphereCapSuspensionHomAt_hopfTargetReflection,
    hopfTargetReflection_map_piThreeSphereTwoHopfGenerator]

/-- The distinguished Freudenthal-edge generator in `π₄(S³)` has square one. -/
theorem piFourSphereThreeEdgeGenerator_sq :
    piFourSphereThreeEdgeGenerator ^ 2 = 1 := by
  rw [pow_two]
  calc
    piFourSphereThreeEdgeGenerator * piFourSphereThreeEdgeGenerator =
        HomotopyGroup.map sphereThreeHopfReflection
            sphereThreeHopfReflection_basepoint piFourSphereThreeEdgeGenerator *
          piFourSphereThreeEdgeGenerator := by
      rw [piFourSphereThreeEdgeGenerator_reflection]
    _ = 1 := sphereThreeHopfReflection_map_mul_self piFourSphereThreeEdgeGenerator

/-- The cardinal modulus of `π₄(S³)` divides two. -/
theorem piFourSphereThreeModulus_dvd_two :
    piFourSphereThreeModulus ∣ 2 := by
  rw [← orderOf_piFourSphereThreeEdgeGenerator]
  exact orderOf_dvd_of_pow_eq_one piFourSphereThreeEdgeGenerator_sq

/-- The only remaining possibilities for the first-stem modulus are one and two. -/
theorem piFourSphereThreeModulus_eq_one_or_two :
    piFourSphereThreeModulus = 1 ∨ piFourSphereThreeModulus = 2 :=
  (Nat.dvd_prime Nat.prime_two).mp piFourSphereThreeModulus_dvd_two

/-- In particular, the first-stem group is finite. -/
theorem piFourSphereThreeModulus_ne_zero :
    piFourSphereThreeModulus ≠ 0 := by
  rcases piFourSphereThreeModulus_eq_one_or_two with h | h <;> omega

/-- The cardinal modulus of the first stable representative is at most two. -/
theorem piFourSphereThreeModulus_le_two :
    piFourSphereThreeModulus ≤ 2 := by
  rcases piFourSphereThreeModulus_eq_one_or_two with h | h <;> omega

/-- Every class of `π₄(S³)` is either the identity or the distinguished edge generator. -/
theorem piFourSphereThree_eq_one_or_eq_edge
    (x : π_ 4 (Sph 3) (sphereBasepoint 3)) :
    x = 1 ∨ x = piFourSphereThreeEdgeGenerator :=
  piFourSphereThree_eq_one_or_eq_edge_of_edge_square
    piFourSphereThreeEdgeGenerator_sq x

/-- Every class of `π₄(S³)` has square one. -/
theorem piFourSphereThree_exponent_two
    (x : π_ 4 (Sph 3) (sphereBasepoint 3)) : x ^ 2 = 1 := by
  rcases piFourSphereThree_eq_one_or_eq_edge x with rfl | rfl
  · simp
  · exact piFourSphereThreeEdgeGenerator_sq

/-- The geometrically suspended Hopf generator in `π₄(S³)` has square equal to the identity. -/
theorem piFourSphereThreeGeometricHopfGenerator_sq :
    piFourSphereThreeGeometricHopfGenerator ^ 2 = 1 := by
  have hmulBasepoint := sphereThreeInversionClass_mul_self_of_eq_one
    (sphereBasepoint 3) sphereThree_one_eq_basepoint.symm
    (sphereSuspensionMap 3 2 hopfMap)
    (sphereSuspensionMap_basepoint 3 2 hopfMap hopfMap_basepoint)
  rw [← suspendedHopfMapClass_eq_inversionClass] at hmulBasepoint
  rw [pow_two, piFourSphereThreeGeometricHopfGenerator_eq_suspensionMapClass]
  exact hmulBasepoint

end Submission
