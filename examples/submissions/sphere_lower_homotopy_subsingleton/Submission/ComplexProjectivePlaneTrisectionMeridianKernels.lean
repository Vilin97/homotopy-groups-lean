/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianCoordinates

/-!
# Exact kernels of the trisection interface maps

A general integral-algebra lemma identifies the kernel of a surjection from a group isomorphic
to `ℤ × ℤ` onto a group isomorphic to `ℤ`: any killed element on which a second integer
coordinate takes the unit value generates the entire kernel.

The three previously constructed meridian classes satisfy this criterion.  Their boundary
classes map to the named central classes, their disk fillings kill them in the corresponding
pairwise interfaces, and their unit universal-cover coordinates prove that the kernels are
exactly their cyclic subgroups.
-/

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

/-- Every homomorphism from `ℤ × ℤ` to `ℤ` is the integral linear form given by
its values on the two standard generators. -/
theorem multiplicativeInt_prod_hom_apply
    (f : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ)
    (x : Multiplicative ℤ × Multiplicative ℤ) :
    (f x).toAdd =
      (f (Multiplicative.ofAdd 1, 1)).toAdd * x.1.toAdd +
        (f (1, Multiplicative.ofAdd 1)).toAdd * x.2.toAdd := by
  let f₁ := f.comp (MonoidHom.inl (Multiplicative ℤ) (Multiplicative ℤ))
  let f₂ := f.comp (MonoidHom.inr (Multiplicative ℤ) (Multiplicative ℤ))
  have h₁ := MonoidHom.apply_mint (Multiplicative ℤ) f₁ x.1
  have h₂ := MonoidHom.apply_mint (Multiplicative ℤ) f₂ x.2
  change f (x.1, 1) = f (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd at h₁
  change f (1, x.2) = f (1, Multiplicative.ofAdd 1) ^ x.2.toAdd at h₂
  rw [show x = (x.1, 1) * (1, x.2) by ext <;> simp,
    map_mul, h₁, h₂]
  simp [mul_comm]
  ring

/-- A killed class with a unit auxiliary coordinate generates the kernel of any
surjection from a rank-two free group to a rank-one free group. -/
theorem monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int
    {G H : Type*} [Group G] [Group H]
    (sourceEquiv : G ≃* Multiplicative ℤ × Multiplicative ℤ)
    (targetEquiv : H ≃* Multiplicative ℤ)
    (f : G →* H) (hf : Function.Surjective f)
    (coordinate : G →* Multiplicative ℤ) (g : G)
    (hfg : f g = 1)
    (hcoordinate : coordinate g = Multiplicative.ofAdd (1 : ℤ)) :
    f.ker = Subgroup.zpowers g := by
  let F : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ :=
    targetEquiv.toMonoidHom.comp
      (f.comp sourceEquiv.symm.toMonoidHom)
  let C : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ :=
    coordinate.comp sourceEquiv.symm.toMonoidHom
  have hFsurjective : Function.Surjective F :=
    targetEquiv.surjective.comp (hf.comp sourceEquiv.symm.surjective)
  let p : ℤ := (F (Multiplicative.ofAdd 1, 1)).toAdd
  let q : ℤ := (F (1, Multiplicative.ofAdd 1)).toAdd
  obtain ⟨w, hw⟩ := hFsurjective (Multiplicative.ofAdd (1 : ℤ))
  have hbezout : p * w.1.toAdd + q * w.2.toAdd = 1 := by
    rw [← multiplicativeInt_prod_hom_apply F w, hw]
    rfl
  let v : Multiplicative ℤ × Multiplicative ℤ :=
    (Multiplicative.ofAdd (-q), Multiplicative.ofAdd p)
  have hkernelParam (x : Multiplicative ℤ × Multiplicative ℤ)
      (hx : F x = 1) :
      ∃ n : ℤ, v ^ n = x := by
    have hkernel : p * x.1.toAdd + q * x.2.toAdd = 0 := by
      rw [← multiplicativeInt_prod_hom_apply F x, hx]
      rfl
    let n : ℤ := -w.2.toAdd * x.1.toAdd + w.1.toAdd * x.2.toAdd
    have hfirst : (-q) * n = x.1.toAdd := by
      calc
        (-q) * n = x.1.toAdd +
            (-w.1.toAdd * (p * x.1.toAdd + q * x.2.toAdd) +
              x.1.toAdd * (p * w.1.toAdd + q * w.2.toAdd - 1)) := by
                simp only [n]
                ring
        _ = x.1.toAdd := by rw [hkernel, hbezout]; ring
    have hsecond : p * n = x.2.toAdd := by
      calc
        p * n = x.2.toAdd +
            (-w.2.toAdd * (p * x.1.toAdd + q * x.2.toAdd) +
              x.2.toAdd * (p * w.1.toAdd + q * w.2.toAdd - 1)) := by
                simp only [n]
                ring
        _ = x.2.toAdd := by rw [hkernel, hbezout]; ring
    refine ⟨n, ?_⟩
    apply Prod.ext
    · change (v ^ n).1.toAdd = x.1.toAdd
      simpa [v, mul_comm] using hfirst
    · change (v ^ n).2.toAdd = x.2.toAdd
      simpa [v, mul_comm] using hsecond
  have hFg : F (sourceEquiv g) = 1 := by
    simp [F, hfg]
  obtain ⟨m, hm⟩ := hkernelParam (sourceEquiv g) hFg
  have hCg : C (sourceEquiv g) = Multiplicative.ofAdd (1 : ℤ) := by
    simpa [C] using hcoordinate
  have hmUnit : m = 1 ∨ m = -1 := by
    have hmul : m * (C v).toAdd = 1 := by
      rw [← hm] at hCg
      rw [map_zpow] at hCg
      have := congrArg Multiplicative.toAdd hCg
      simpa [mul_comm] using this
    exact Int.eq_one_or_neg_one_of_mul_eq_one hmul
  have hzpowers :
      Subgroup.zpowers (sourceEquiv g) = Subgroup.zpowers v := by
    rcases hmUnit with rfl | rfl
    · simpa using (congrArg Subgroup.zpowers hm).symm
    · have hginv : sourceEquiv g = v⁻¹ := by simpa using hm.symm
      rw [hginv, Subgroup.zpowers_inv]
  ext x
  constructor
  · intro hx
    have hFx : F (sourceEquiv x) = 1 := by
      change f x = 1 at hx
      simp [F, hx]
    obtain ⟨n, hn⟩ := hkernelParam (sourceEquiv x) hFx
    have hxmem : sourceEquiv x ∈ Subgroup.zpowers v :=
      Subgroup.mem_zpowers_iff.mpr ⟨n, hn⟩
    rw [← hzpowers] at hxmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨k, sourceEquiv.injective ?_⟩
    rw [map_zpow]
    exact hk
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    change f (g ^ n) = 1
    rw [map_zpow, hfg, one_zpow]

/-- The kernel-generator criterion with auxiliary coordinate `-1`. -/
theorem monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int_neg_one
    {G H : Type*} [Group G] [Group H]
    (sourceEquiv : G ≃* Multiplicative ℤ × Multiplicative ℤ)
    (targetEquiv : H ≃* Multiplicative ℤ)
    (f : G →* H) (hf : Function.Surjective f)
    (coordinate : G →* Multiplicative ℤ) (g : G)
    (hfg : f g = 1)
    (hcoordinate : coordinate g = Multiplicative.ofAdd (-1 : ℤ)) :
    f.ker = Subgroup.zpowers g := by
  rw [← Subgroup.zpowers_inv]
  apply monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int
    sourceEquiv targetEquiv f hf coordinate g⁻¹
  · rw [map_inv, hfg, inv_one]
  · rw [map_inv, hcoordinate]
    rfl

namespace ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The zero-five boundary class maps to the named central meridian class. -/
theorem zeroFiveBoundaryInclCentral_piOne_map_eq_central_class :
    HomotopyGroup.map
        (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
        zeroFiveBoundaryRealizationBase_map_central_eq
        zeroFiveBoundaryRealizationPiOneClass =
      zeroFiveCentralRealizationPiOneClass := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simp only [zeroFiveBoundaryRealizationPiOneClass,
    zeroFiveCentralRealizationPiOneClass]
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk zeroFiveBoundaryRealizationLoop)
        (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom).cast
          zeroFiveBoundaryRealizationBase_map_central_eq.symm
          zeroFiveBoundaryRealizationBase_map_central_eq.symm =
    Path.Homotopic.Quotient.mk zeroFiveCentralRealizationLoop
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    zeroFiveBoundaryRealizationLoop_map_central_cast]

/-- The zero-five central-to-pairwise map kills its named meridian class. -/
theorem zeroFiveCentralInterfaceInclPairwise_piOne_map_class_eq_one :
    HomotopyGroup.map
        (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
        zeroFiveCentralRealizationBase_map_pairwise_eq
        zeroFiveCentralRealizationPiOneClass = 1 := by
  rw [← zeroFiveBoundaryInclCentral_piOne_map_eq_central_class]
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
    zeroFiveCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom
    zeroFiveBoundaryRealizationBase_map_central_eq
    zeroFiveBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp zeroFiveMeridianBoundaryInclCentral
        zeroFiveCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map zeroFiveMeridianBoundaryInclCentral).hom)
          zeroFiveBoundaryRealizationBase =
        (SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom
          zeroFiveBoundaryRealizationBase :=
    congrArg (fun k ↦ k zeroFiveBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl zeroFiveBoundaryRealizationPiOneClass
  exact hcomp.trans (hcongr.trans
    (zeroFiveMeridianViaCentralInclPairwise_piOne_trivial
      zeroFiveBoundaryRealizationBase
      zeroFiveBoundaryRealizationPiOneClass))

/-- The kernel of the zero-five central-to-pairwise map is generated exactly by its
meridian class. -/
theorem zeroFiveCentralInterfaceInclPairwise_piOne_ker_eq_zpowers :
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq).ker =
        Subgroup.zpowers zeroFiveCentralRealizationPiOneClass := by
  obtain ⟨sourceEquiv⟩ :=
    centralInterface_piOne_mulEquiv_int_prod_int
      zeroFiveCentralRealizationBase
  obtain ⟨targetEquiv⟩ :=
    pairwiseInterface_piOne_mulEquiv_int
      0 (by decide) 5 (by decide) (by decide)
      ((SSet.toTop.map
        (zeroFiveMeridianBoundaryInclCentral ≫
          zeroFiveCentralInterfaceInclPairwise)).hom
        zeroFiveBoundaryRealizationBase)
  apply monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int
    sourceEquiv targetEquiv
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq)
    zeroFiveCentralInterfaceInclPairwise_piOne_map_surjective
    zeroFiveCentralRealizationPiOneFirstCoordinate
    zeroFiveCentralRealizationPiOneClass
    zeroFiveCentralInterfaceInclPairwise_piOne_map_class_eq_one
    zeroFiveCentralRealizationPiOneFirstCoordinate_class

/-- The five-four boundary class maps to the named central meridian class. -/
theorem fiveFourBoundaryInclCentral_piOne_map_eq_central_class :
    HomotopyGroup.map
        (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
        fiveFourBoundaryRealizationBase_map_central_eq
        fiveFourBoundaryRealizationPiOneClass =
      fiveFourCentralRealizationPiOneClass := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simp only [fiveFourBoundaryRealizationPiOneClass,
    fiveFourCentralRealizationPiOneClass]
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk fiveFourBoundaryRealizationLoop)
        (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom).cast
          fiveFourBoundaryRealizationBase_map_central_eq.symm
          fiveFourBoundaryRealizationBase_map_central_eq.symm =
    Path.Homotopic.Quotient.mk fiveFourCentralRealizationLoop
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    fiveFourBoundaryRealizationLoop_map_central_cast]

/-- The five-four central-to-pairwise map kills its named meridian class. -/
theorem fiveFourCentralInterfaceInclPairwise_piOne_map_class_eq_one :
    HomotopyGroup.map
        (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
        fiveFourCentralRealizationBase_map_pairwise_eq
        fiveFourCentralRealizationPiOneClass = 1 := by
  rw [← fiveFourBoundaryInclCentral_piOne_map_eq_central_class]
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
    fiveFourCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom
    fiveFourBoundaryRealizationBase_map_central_eq
    fiveFourBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp fiveFourMeridianBoundaryInclCentral
        fiveFourCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fiveFourMeridianBoundaryInclCentral).hom)
          fiveFourBoundaryRealizationBase =
        (SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom
          fiveFourBoundaryRealizationBase :=
    congrArg (fun k ↦ k fiveFourBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl fiveFourBoundaryRealizationPiOneClass
  exact hcomp.trans (hcongr.trans
    (fiveFourMeridianViaCentralInclPairwise_piOne_trivial
      fiveFourBoundaryRealizationBase
      fiveFourBoundaryRealizationPiOneClass))

/-- The kernel of the five-four central-to-pairwise map is generated exactly by its
meridian class. -/
theorem fiveFourCentralInterfaceInclPairwise_piOne_ker_eq_zpowers :
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq).ker =
        Subgroup.zpowers fiveFourCentralRealizationPiOneClass := by
  obtain ⟨sourceEquiv⟩ :=
    centralInterface_piOne_mulEquiv_int_prod_int
      fiveFourCentralRealizationBase
  obtain ⟨targetEquiv⟩ :=
    pairwiseInterface_piOne_mulEquiv_int
      5 (by decide) 4 (by decide) (by decide)
      ((SSet.toTop.map
        (fiveFourMeridianBoundaryInclCentral ≫
          fiveFourCentralInterfaceInclPairwise)).hom
        fiveFourBoundaryRealizationBase)
  apply monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int
    sourceEquiv targetEquiv
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq)
    fiveFourCentralInterfaceInclPairwise_piOne_map_surjective
    fiveFourCentralRealizationPiOneSecondCoordinate
    fiveFourCentralRealizationPiOneClass
    fiveFourCentralInterfaceInclPairwise_piOne_map_class_eq_one
    fiveFourCentralRealizationPiOneSecondCoordinate_class

/-- The four-zero boundary class maps to the named central meridian class. -/
theorem fourZeroBoundaryInclCentral_piOne_map_eq_central_class :
    HomotopyGroup.map
        (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
        fourZeroBoundaryRealizationBase_map_central_eq
        fourZeroBoundaryRealizationPiOneClass =
      fourZeroCentralRealizationPiOneClass := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simp only [fourZeroBoundaryRealizationPiOneClass,
    fourZeroCentralRealizationPiOneClass]
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change (Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk fourZeroBoundaryRealizationLoop)
        (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom).cast
          fourZeroBoundaryRealizationBase_map_central_eq.symm
          fourZeroBoundaryRealizationBase_map_central_eq.symm =
    Path.Homotopic.Quotient.mk fourZeroCentralRealizationLoop
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    fourZeroBoundaryRealizationLoop_map_central_cast]

/-- The four-zero central-to-pairwise map kills its named meridian class. -/
theorem fourZeroCentralInterfaceInclPairwise_piOne_map_class_eq_one :
    HomotopyGroup.map
        (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
        fourZeroCentralRealizationBase_map_pairwise_eq
        fourZeroCentralRealizationPiOneClass = 1 := by
  rw [← fourZeroBoundaryInclCentral_piOne_map_eq_central_class]
  have hcomp := HomotopyGroup.map_comp_apply (N := Fin 1)
    (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
    fourZeroCentralRealizationBase_map_pairwise_eq
    (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom
    fourZeroBoundaryRealizationBase_map_central_eq
    fourZeroBoundaryRealizationPiOneClass
  have hcontinuous :
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom =
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (ConcreteCategory.congr_hom
      (SSet.toTop.map_comp fourZeroMeridianBoundaryInclCentral
        fourZeroCentralInterfaceInclPairwise) z).symm
  have hcontinuousBase :
      ((SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom.comp
          (SSet.toTop.map fourZeroMeridianBoundaryInclCentral).hom)
          fourZeroBoundaryRealizationBase =
        (SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom
          fourZeroBoundaryRealizationBase :=
    congrArg (fun k ↦ k fourZeroBoundaryRealizationBase) hcontinuous
  have hcongr := HomotopyGroup.map_congr (N := Fin 1)
    hcontinuous hcontinuousBase rfl fourZeroBoundaryRealizationPiOneClass
  exact hcomp.trans (hcongr.trans
    (fourZeroMeridianViaCentralInclPairwise_piOne_trivial
      fourZeroBoundaryRealizationBase
      fourZeroBoundaryRealizationPiOneClass))

/-- The kernel of the four-zero central-to-pairwise map is generated exactly by its
meridian class. -/
theorem fourZeroCentralInterfaceInclPairwise_piOne_ker_eq_zpowers :
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq).ker =
        Subgroup.zpowers fourZeroCentralRealizationPiOneClass := by
  obtain ⟨sourceEquiv⟩ :=
    centralInterface_piOne_mulEquiv_int_prod_int
      fourZeroCentralRealizationBase
  obtain ⟨targetEquiv⟩ :=
    pairwiseInterface_piOne_mulEquiv_int
      4 (by decide) 0 (by decide) (by decide)
      ((SSet.toTop.map
        (fourZeroMeridianBoundaryInclCentral ≫
          fourZeroCentralInterfaceInclPairwise)).hom
        fourZeroBoundaryRealizationBase)
  apply monoidHom_ker_eq_zpowers_of_surjective_of_int_prod_int_neg_one
    sourceEquiv targetEquiv
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq)
    fourZeroCentralInterfaceInclPairwise_piOne_map_surjective
    fourZeroCentralRealizationPiOneFirstCoordinate
    fourZeroCentralRealizationPiOneClass
    fourZeroCentralInterfaceInclPairwise_piOne_map_class_eq_one
    fourZeroCentralRealizationPiOneFirstCoordinate_class

end ComplexProjectivePlaneTriangulation

end Submission
