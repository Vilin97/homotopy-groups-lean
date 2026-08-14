/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionInterfacePiOne

/-!
# Integral fundamental-group coordinates for the trisection meridians

The real universal cover of the unit additive circle identifies its fundamental group with the
multiplicative integers.  The equivalence is normalized so that the standard winding-`n` loop
maps exactly to `n`.  Composing it with the two integral cocycle maps on the central trisection
torus gives explicit integer-valued homomorphisms on fundamental groups.

The zero-five and five-four meridian classes map to `1`; the four-zero class maps to `-1`.
Consequently each displayed coordinate homomorphism is surjective.  This strengthens the earlier
nontriviality certificates: every concrete meridian has a unit integral coordinate.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

open FiniteOrderedComplex

def intCastRealZMultiplesOne :
    ℤ →+ AddSubgroup.zmultiples (1 : ℝ) :=
  (Int.castAddHom ℝ).codRestrict (AddSubgroup.zmultiples (1 : ℝ))
    (fun n ↦ by
      exact ⟨n, by simp⟩)

theorem intCastRealZMultiplesOne_bijective :
    Function.Bijective intCastRealZMultiplesOne := by
  constructor
  · intro m n h
    have hval := congrArg Subtype.val h
    change (m : ℝ) = (n : ℝ) at hval
    exact_mod_cast hval
  · intro z
    obtain ⟨n, hn⟩ := z.property
    refine ⟨n, Subtype.ext ?_⟩
    change (n : ℝ) = z.1
    simpa using hn

noncomputable def intAddEquivRealZMultiplesOne :
    ℤ ≃+ AddSubgroup.zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective intCastRealZMultiplesOne
    intCastRealZMultiplesOne_bijective

def mulOppositeMulEquivOfComm (G : Type*) [CommGroup G] : Gᵐᵒᵖ ≃* G where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op
  map_mul' x y := by simp [mul_comm]

def unitAddCircleCoveringFiberZero :
    ((fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' ({0} : Set UnitAddCircle)) :=
  ⟨0, by simp⟩

theorem unitAddCircleQuotientCoveringMap :
    IsAddQuotientCoveringMap
      ((fun x : ℝ ↦ (x : UnitAddCircle)))
      (AddSubgroup.zmultiples (1 : ℝ)) :=
  AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)

noncomputable def unitAddCircleFundamentalGroupMulEquivInt :
    FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ :=
  (unitAddCircleQuotientCoveringMap.fundamentalGroupEquiv
      unitAddCircleCoveringFiberZero).trans
    ((mulOppositeMulEquivOfComm
      (Multiplicative (AddSubgroup.zmultiples (1 : ℝ)))).trans
      (AddEquiv.toMultiplicative intAddEquivRealZMultiplesOne.symm))

theorem unitAddCircle_fundamentalGroupToMulOpposite_integerPath (n : ℤ) :
    unitAddCircleQuotientCoveringMap.fundamentalGroupToMulOpposite
        unitAddCircleCoveringFiberZero
        (Path.Homotopic.Quotient.mk (addCircleIntegerPath n) :
          FundamentalGroup UnitAddCircle 0) =
      MulOpposite.op (Multiplicative.ofAdd
        (intAddEquivRealZMultiplesOne n)) := by
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  change ((intAddEquivRealZMultiplesOne n :
      AddSubgroup.zmultiples (1 : ℝ)) : ℝ) + 0 = _
  rw [add_zero]
  change (n : ℝ) = _
  rw [show unitAddCircleQuotientCoveringMap.isCoveringMap =
      AddCircle.isCoveringMap_coe (1 : ℝ) by rfl]
  exact (addCircleIntegerPath_liftPath_one n).symm

theorem unitAddCircleFundamentalGroupMulEquivInt_integerPath (n : ℤ) :
    unitAddCircleFundamentalGroupMulEquivInt
        (Path.Homotopic.Quotient.mk (addCircleIntegerPath n) :
          FundamentalGroup UnitAddCircle 0) =
      Multiplicative.ofAdd n := by
  change (AddEquiv.toMultiplicative intAddEquivRealZMultiplesOne.symm)
      (mulOppositeMulEquivOfComm (Multiplicative
        (AddSubgroup.zmultiples (1 : ℝ)))
        (unitAddCircleQuotientCoveringMap.fundamentalGroupToMulOpposite
          unitAddCircleCoveringFiberZero
          (Path.Homotopic.Quotient.mk (addCircleIntegerPath n) :
            FundamentalGroup UnitAddCircle 0))) = _
  rw [unitAddCircle_fundamentalGroupToMulOpposite_integerPath]
  exact congrArg Multiplicative.ofAdd
    (intAddEquivRealZMultiplesOne.symm_apply_apply n)

theorem monoidHom_multiplicativeInt_surjective_of_apply_eq_one
    {G : Type*} [Group G] (f : G →* Multiplicative ℤ) (g : G)
    (h : f g = Multiplicative.ofAdd (1 : ℤ)) :
    Function.Surjective f := by
  intro z
  let n : ℤ := z.toAdd
  refine ⟨g ^ n, ?_⟩
  calc
    f (g ^ n) = (f g) ^ n := map_zpow f g n
    _ = Multiplicative.ofAdd n := by
      rw [h]
      simpa using (Int.ofAdd_mul (1 : ℤ) n).symm
    _ = z := rfl

theorem monoidHom_multiplicativeInt_surjective_of_apply_eq_neg_one
    {G : Type*} [Group G] (f : G →* Multiplicative ℤ) (g : G)
    (h : f g = Multiplicative.ofAdd (-1 : ℤ)) :
    Function.Surjective f := by
  apply monoidHom_multiplicativeInt_surjective_of_apply_eq_one f g⁻¹
  rw [map_inv, h]
  rfl

namespace ComplexProjectivePlaneTriangulation

noncomputable def zeroFiveCentralCarrierFirstCoordinate :
    FundamentalGroup (FiniteOrderedComplex.facetFamilyCarrier centralInterfaceFacets)
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
          (isFace_singleton_left_of_pair centralEdge_one_seven)) →*
      Multiplicative ℤ :=
  unitAddCircleFundamentalGroupMulEquivInt.toMonoidHom.comp
    (FundamentalGroup.mapOfEq
      (integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
      centralFirstCircleMap_vertex_one_eq_zero)

theorem zeroFiveCentralCarrierFirstCoordinate_class :
    zeroFiveCentralCarrierFirstCoordinate
        zeroFiveCentralCarrierFundamentalClass =
      Multiplicative.ofAdd (1 : ℤ) := by
  change unitAddCircleFundamentalGroupMulEquivInt
      (FundamentalGroup.mapOfEq
        (integralCocycleCircleMap centralTorusFirstCochain
          centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
        centralFirstCircleMap_vertex_one_eq_zero
        zeroFiveCentralCarrierFundamentalClass) = _
  rw [FundamentalGroup.mapOfEq_apply]
  change unitAddCircleFundamentalGroupMulEquivInt
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk zeroFiveCentralCarrierLoop)
          (integralCocycleCircleMap centralTorusFirstCochain
            centralTorusFirstCochain_alternating
            centralTorusFirstCochain_closed)).cast
        centralFirstCircleMap_vertex_one_eq_zero.symm
        centralFirstCircleMap_vertex_one_eq_zero.symm) = _
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    zeroFiveCentralCarrierLoop_map_first_cast]
  have hquot :
      Path.Homotopic.Quotient.mk zeroFiveFirstCirclePath =
        Path.Homotopic.Quotient.mk (addCircleIntegerPath 1) :=
    Path.Homotopic.Quotient.eq.mpr zeroFiveFirstCirclePath_homotopic_one
  rw [hquot]
  exact unitAddCircleFundamentalGroupMulEquivInt_integerPath 1

noncomputable def fiveFourCentralCarrierSecondCoordinate :
    FundamentalGroup (FiniteOrderedComplex.facetFamilyCarrier centralInterfaceFacets)
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
          (isFace_singleton_left_of_pair centralEdge_seven_three)) →*
      Multiplicative ℤ :=
  unitAddCircleFundamentalGroupMulEquivInt.toMonoidHom.comp
    (FundamentalGroup.mapOfEq
      (integralCocycleCircleMap centralTorusSecondCochain
        centralTorusSecondCochain_alternating centralTorusSecondCochain_closed)
      centralSecondCircleMap_vertex_seven_eq_zero)

theorem fiveFourCentralCarrierSecondCoordinate_class :
    fiveFourCentralCarrierSecondCoordinate
        fiveFourCentralCarrierFundamentalClass =
      Multiplicative.ofAdd (1 : ℤ) := by
  change unitAddCircleFundamentalGroupMulEquivInt
      (FundamentalGroup.mapOfEq
        (integralCocycleCircleMap centralTorusSecondCochain
          centralTorusSecondCochain_alternating centralTorusSecondCochain_closed)
        centralSecondCircleMap_vertex_seven_eq_zero
        fiveFourCentralCarrierFundamentalClass) = _
  rw [FundamentalGroup.mapOfEq_apply]
  change unitAddCircleFundamentalGroupMulEquivInt
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk fiveFourCentralCarrierLoop)
          (integralCocycleCircleMap centralTorusSecondCochain
            centralTorusSecondCochain_alternating
            centralTorusSecondCochain_closed)).cast
        centralSecondCircleMap_vertex_seven_eq_zero.symm
        centralSecondCircleMap_vertex_seven_eq_zero.symm) = _
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    fiveFourCentralCarrierLoop_map_second_cast]
  have hquot :
      Path.Homotopic.Quotient.mk fiveFourSecondCirclePath =
        Path.Homotopic.Quotient.mk (addCircleIntegerPath 1) :=
    Path.Homotopic.Quotient.eq.mpr fiveFourSecondCirclePath_homotopic_one
  rw [hquot]
  exact unitAddCircleFundamentalGroupMulEquivInt_integerPath 1

noncomputable def fourZeroCentralCarrierFirstCoordinate :
    FundamentalGroup (FiniteOrderedComplex.facetFamilyCarrier centralInterfaceFacets)
        (facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
          (isFace_singleton_left_of_pair centralEdge_three_one)) →*
      Multiplicative ℤ :=
  unitAddCircleFundamentalGroupMulEquivInt.toMonoidHom.comp
    (FundamentalGroup.mapOfEq
      (integralCocycleCircleMap centralTorusFirstCochain
        centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
      centralFirstCircleMap_vertex_three_eq_zero)

theorem fourZeroCentralCarrierFirstCoordinate_class :
    fourZeroCentralCarrierFirstCoordinate
        fourZeroCentralCarrierFundamentalClass =
      Multiplicative.ofAdd (-1 : ℤ) := by
  change unitAddCircleFundamentalGroupMulEquivInt
      (FundamentalGroup.mapOfEq
        (integralCocycleCircleMap centralTorusFirstCochain
          centralTorusFirstCochain_alternating centralTorusFirstCochain_closed)
        centralFirstCircleMap_vertex_three_eq_zero
        fourZeroCentralCarrierFundamentalClass) = _
  rw [FundamentalGroup.mapOfEq_apply]
  change unitAddCircleFundamentalGroupMulEquivInt
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk fourZeroCentralCarrierLoop)
          (integralCocycleCircleMap centralTorusFirstCochain
            centralTorusFirstCochain_alternating
            centralTorusFirstCochain_closed)).cast
        centralFirstCircleMap_vertex_three_eq_zero.symm
        centralFirstCircleMap_vertex_three_eq_zero.symm) = _
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast,
    fourZeroCentralCarrierLoop_map_first_cast]
  have hquot :
      Path.Homotopic.Quotient.mk fourZeroFirstCirclePath =
        Path.Homotopic.Quotient.mk (addCircleIntegerPath (-1)) :=
    Path.Homotopic.Quotient.eq.mpr fourZeroFirstCirclePath_homotopic_neg_one
  rw [hquot]
  exact unitAddCircleFundamentalGroupMulEquivInt_integerPath (-1)

theorem zeroFiveCentralCarrierFirstCoordinate_surjective :
    Function.Surjective zeroFiveCentralCarrierFirstCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_one
    zeroFiveCentralCarrierFirstCoordinate
    zeroFiveCentralCarrierFundamentalClass
    zeroFiveCentralCarrierFirstCoordinate_class

theorem fiveFourCentralCarrierSecondCoordinate_surjective :
    Function.Surjective fiveFourCentralCarrierSecondCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_one
    fiveFourCentralCarrierSecondCoordinate
    fiveFourCentralCarrierFundamentalClass
    fiveFourCentralCarrierSecondCoordinate_class

theorem fourZeroCentralCarrierFirstCoordinate_surjective :
    Function.Surjective fourZeroCentralCarrierFirstCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_neg_one
    fourZeroCentralCarrierFirstCoordinate
    fourZeroCentralCarrierFundamentalClass
    fourZeroCentralCarrierFirstCoordinate_class

/-! Integral coordinates on the actual simplicial-realization meridians. -/

theorem zeroFiveCentralRealizationBase_map_carrier_eq :
    orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets
        zeroFiveCentralRealizationBase =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 1
        (isFace_singleton_left_of_pair centralEdge_one_seven) := by
  simp [zeroFiveCentralRealizationBase]

noncomputable def zeroFiveCentralRealizationPiOneFirstCoordinate :
    HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        zeroFiveCentralRealizationBase →*
      Multiplicative ℤ :=
  zeroFiveCentralCarrierFirstCoordinate.comp
    (HomotopyGroup.pi1MulEquivFundamentalGroup.toMonoidHom.comp
      (HomotopyGroup.mapHom (N := Fin 1)
        ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets).continuous⟩
        zeroFiveCentralRealizationBase_map_carrier_eq))

theorem zeroFiveCentralRealizationPiOneFirstCoordinate_class :
    zeroFiveCentralRealizationPiOneFirstCoordinate
        zeroFiveCentralRealizationPiOneClass =
      Multiplicative.ofAdd (1 : ℤ) := by
  change zeroFiveCentralCarrierFirstCoordinate
      (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map
          ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
            (orderedRealizationHomeomorphFacetFamilyCarrier
              centralInterfaceFacets).continuous⟩
          zeroFiveCentralRealizationBase_map_carrier_eq
          (piOneClassOfPath zeroFiveCentralRealizationLoop))) = _
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change zeroFiveCentralCarrierFirstCoordinate
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk zeroFiveCentralRealizationLoop)
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets)).cast
        zeroFiveCentralRealizationBase_map_carrier_eq.symm
        zeroFiveCentralRealizationBase_map_carrier_eq.symm) = _
  have hpath :
      ((zeroFiveCentralRealizationLoop.map
        (orderedRealizationHomeomorphFacetFamilyCarrier
          centralInterfaceFacets).continuous).cast
        zeroFiveCentralRealizationBase_map_carrier_eq.symm
        zeroFiveCentralRealizationBase_map_carrier_eq.symm) =
      zeroFiveCentralCarrierLoop := by
    ext t x
    simp [zeroFiveCentralRealizationLoop]
    exact congrArg
      (fun p : facetFamilyCarrier centralInterfaceFacets ↦ p.1 x)
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        centralInterfaceFacets).apply_symm_apply
          (zeroFiveCentralCarrierLoop t))
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hpath]
  exact zeroFiveCentralCarrierFirstCoordinate_class

theorem zeroFiveCentralRealizationPiOneFirstCoordinate_surjective :
    Function.Surjective zeroFiveCentralRealizationPiOneFirstCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_one
    zeroFiveCentralRealizationPiOneFirstCoordinate
    zeroFiveCentralRealizationPiOneClass
    zeroFiveCentralRealizationPiOneFirstCoordinate_class

theorem fiveFourCentralRealizationBase_map_carrier_eq :
    orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets
        fiveFourCentralRealizationBase =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 7
        (isFace_singleton_left_of_pair centralEdge_seven_three) := by
  simp [fiveFourCentralRealizationBase]

noncomputable def fiveFourCentralRealizationPiOneSecondCoordinate :
    HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fiveFourCentralRealizationBase →*
      Multiplicative ℤ :=
  fiveFourCentralCarrierSecondCoordinate.comp
    (HomotopyGroup.pi1MulEquivFundamentalGroup.toMonoidHom.comp
      (HomotopyGroup.mapHom (N := Fin 1)
        ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets).continuous⟩
        fiveFourCentralRealizationBase_map_carrier_eq))

theorem fiveFourCentralRealizationPiOneSecondCoordinate_class :
    fiveFourCentralRealizationPiOneSecondCoordinate
        fiveFourCentralRealizationPiOneClass =
      Multiplicative.ofAdd (1 : ℤ) := by
  change fiveFourCentralCarrierSecondCoordinate
      (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map
          ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
            (orderedRealizationHomeomorphFacetFamilyCarrier
              centralInterfaceFacets).continuous⟩
          fiveFourCentralRealizationBase_map_carrier_eq
          (piOneClassOfPath fiveFourCentralRealizationLoop))) = _
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change fiveFourCentralCarrierSecondCoordinate
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk fiveFourCentralRealizationLoop)
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets)).cast
        fiveFourCentralRealizationBase_map_carrier_eq.symm
        fiveFourCentralRealizationBase_map_carrier_eq.symm) = _
  have hpath :
      ((fiveFourCentralRealizationLoop.map
        (orderedRealizationHomeomorphFacetFamilyCarrier
          centralInterfaceFacets).continuous).cast
        fiveFourCentralRealizationBase_map_carrier_eq.symm
        fiveFourCentralRealizationBase_map_carrier_eq.symm) =
      fiveFourCentralCarrierLoop := by
    ext t x
    simp [fiveFourCentralRealizationLoop]
    exact congrArg
      (fun p : facetFamilyCarrier centralInterfaceFacets ↦ p.1 x)
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        centralInterfaceFacets).apply_symm_apply
          (fiveFourCentralCarrierLoop t))
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hpath]
  exact fiveFourCentralCarrierSecondCoordinate_class

theorem fiveFourCentralRealizationPiOneSecondCoordinate_surjective :
    Function.Surjective fiveFourCentralRealizationPiOneSecondCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_one
    fiveFourCentralRealizationPiOneSecondCoordinate
    fiveFourCentralRealizationPiOneClass
    fiveFourCentralRealizationPiOneSecondCoordinate_class

theorem fourZeroCentralRealizationBase_map_carrier_eq :
    orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets
        fourZeroCentralRealizationBase =
      facetFamilyVertexOfIsFace (facets := centralInterfaceFacets) 3
        (isFace_singleton_left_of_pair centralEdge_three_one) := by
  simp [fourZeroCentralRealizationBase]

noncomputable def fourZeroCentralRealizationPiOneFirstCoordinate :
    HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fourZeroCentralRealizationBase →*
      Multiplicative ℤ :=
  fourZeroCentralCarrierFirstCoordinate.comp
    (HomotopyGroup.pi1MulEquivFundamentalGroup.toMonoidHom.comp
      (HomotopyGroup.mapHom (N := Fin 1)
        ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets).continuous⟩
        fourZeroCentralRealizationBase_map_carrier_eq))

theorem fourZeroCentralRealizationPiOneFirstCoordinate_class :
    fourZeroCentralRealizationPiOneFirstCoordinate
        fourZeroCentralRealizationPiOneClass =
      Multiplicative.ofAdd (-1 : ℤ) := by
  change fourZeroCentralCarrierFirstCoordinate
      (HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map
          ⟨orderedRealizationHomeomorphFacetFamilyCarrier centralInterfaceFacets,
            (orderedRealizationHomeomorphFacetFamilyCarrier
              centralInterfaceFacets).continuous⟩
          fourZeroCentralRealizationBase_map_carrier_eq
          (piOneClassOfPath fourZeroCentralRealizationLoop))) = _
  rw [pi1MulEquivFundamentalGroup_map_piOneClassOfPath]
  rw [FundamentalGroup.mapOfEq_apply]
  change fourZeroCentralCarrierFirstCoordinate
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk fourZeroCentralRealizationLoop)
          (orderedRealizationHomeomorphFacetFamilyCarrier
            centralInterfaceFacets)).cast
        fourZeroCentralRealizationBase_map_carrier_eq.symm
        fourZeroCentralRealizationBase_map_carrier_eq.symm) = _
  have hpath :
      ((fourZeroCentralRealizationLoop.map
        (orderedRealizationHomeomorphFacetFamilyCarrier
          centralInterfaceFacets).continuous).cast
        fourZeroCentralRealizationBase_map_carrier_eq.symm
        fourZeroCentralRealizationBase_map_carrier_eq.symm) =
      fourZeroCentralCarrierLoop := by
    ext t x
    simp [fourZeroCentralRealizationLoop]
    exact congrArg
      (fun p : facetFamilyCarrier centralInterfaceFacets ↦ p.1 x)
      ((orderedRealizationHomeomorphFacetFamilyCarrier
        centralInterfaceFacets).apply_symm_apply
          (fourZeroCentralCarrierLoop t))
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hpath]
  exact fourZeroCentralCarrierFirstCoordinate_class

theorem fourZeroCentralRealizationPiOneFirstCoordinate_surjective :
    Function.Surjective fourZeroCentralRealizationPiOneFirstCoordinate :=
  monoidHom_multiplicativeInt_surjective_of_apply_eq_neg_one
    fourZeroCentralRealizationPiOneFirstCoordinate
    fourZeroCentralRealizationPiOneClass
    fourZeroCentralRealizationPiOneFirstCoordinate_class

end ComplexProjectivePlaneTriangulation

end Submission
