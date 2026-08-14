/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianSplittings

/-!
# Meridian normal forms in the central trisection torus

The split product equivalences give a direct formula for every central fundamental-group class.
It is the product of the named meridian raised to its normalized integral coordinate and the
chosen lift of its image in the corresponding pairwise interface.

This records three concrete longitude-meridian normal forms rather than only an abstract product
classification.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

/-- The inverse normal form for a multiplicative equivalence jointly defined by an integer
coordinate and a quotient map. -/
theorem eq_zpow_mul_section_of_monoidHom_prod_mulEquiv
    {G H : Type*} [Group G] [Group H]
    (coordinate : G →* Multiplicative ℤ) (f : G →* H)
    (g : G) (e : G ≃* Multiplicative ℤ × H)
    (he : ∀ x, e x = (coordinate x, f x))
    (hg : e g = (Multiplicative.ofAdd (1 : ℤ), 1))
    (s : H →* G) (hs : ∀ h, e (s h) = (1, h))
    (x : G) :
    x = g ^ (coordinate x).toAdd * s (f x) := by
  apply e.injective
  rw [he, map_mul, map_zpow, hg, hs]
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    simp
  · simp

end Submission

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The zero-five meridian class expressed at the exact named central basepoint. -/
noncomputable def zeroFiveCentralRealizationPiOneMeridianAtBase :
    HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      zeroFiveCentralRealizationBase :=
  zeroFiveCentralRealizationPiOneClass

/-- Every central class at the zero-five basepoint is its meridian power times the canonical
lift of its pairwise image. -/
theorem zeroFiveCentralInterfacePiOne_meridian_normalForm
    (x : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      zeroFiveCentralRealizationBase) :
    x = zeroFiveCentralRealizationPiOneMeridianAtBase ^
          (zeroFiveCentralRealizationPiOneFirstCoordinate x).toAdd *
        zeroFiveCentralInterfaceInclPairwisePiOneSection
          ((HomotopyGroup.mapHom (N := Fin 1)
            (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
            zeroFiveCentralRealizationBase_map_pairwise_eq) x) := by
  apply eq_zpow_mul_section_of_monoidHom_prod_mulEquiv
    zeroFiveCentralRealizationPiOneFirstCoordinate
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq)
    zeroFiveCentralRealizationPiOneMeridianAtBase
    zeroFiveCentralInterfacePiOneMeridianProdEquiv
  · intro y
    rfl
  · exact zeroFiveCentralInterfacePiOneMeridianProdEquiv_meridian
  · intro h
    exact zeroFiveCentralInterfacePiOneMeridianProdEquiv.apply_symm_apply (1, h)

/-- The five-four meridian class expressed at the exact named central basepoint. -/
noncomputable def fiveFourCentralRealizationPiOneMeridianAtBase :
    HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      fiveFourCentralRealizationBase :=
  fiveFourCentralRealizationPiOneClass

/-- Every central class at the five-four basepoint is its meridian power times the canonical
lift of its pairwise image. -/
theorem fiveFourCentralInterfacePiOne_meridian_normalForm
    (x : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      fiveFourCentralRealizationBase) :
    x = fiveFourCentralRealizationPiOneMeridianAtBase ^
          (fiveFourCentralRealizationPiOneSecondCoordinate x).toAdd *
        fiveFourCentralInterfaceInclPairwisePiOneSection
          ((HomotopyGroup.mapHom (N := Fin 1)
            (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
            fiveFourCentralRealizationBase_map_pairwise_eq) x) := by
  apply eq_zpow_mul_section_of_monoidHom_prod_mulEquiv
    fiveFourCentralRealizationPiOneSecondCoordinate
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq)
    fiveFourCentralRealizationPiOneMeridianAtBase
    fiveFourCentralInterfacePiOneMeridianProdEquiv
  · intro y
    rfl
  · exact fiveFourCentralInterfacePiOneMeridianProdEquiv_meridian
  · intro h
    exact fiveFourCentralInterfacePiOneMeridianProdEquiv.apply_symm_apply (1, h)

/-- The four-zero meridian class expressed at the exact named central basepoint. -/
noncomputable def fourZeroCentralRealizationPiOneMeridianAtBase :
    HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      fourZeroCentralRealizationBase :=
  fourZeroCentralRealizationPiOneClass

/-- Every central class at the four-zero basepoint is its normalized meridian power times the
canonical lift of its pairwise image. -/
theorem fourZeroCentralInterfacePiOne_meridian_normalForm
    (x : HomotopyGroup.Pi 1
      (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
      fourZeroCentralRealizationBase) :
    x = fourZeroCentralRealizationPiOneMeridianAtBase ^
          (fourZeroCentralRealizationPiOneMeridianCoordinate x).toAdd *
        fourZeroCentralInterfaceInclPairwisePiOneSection
          ((HomotopyGroup.mapHom (N := Fin 1)
            (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
            fourZeroCentralRealizationBase_map_pairwise_eq) x) := by
  apply eq_zpow_mul_section_of_monoidHom_prod_mulEquiv
    fourZeroCentralRealizationPiOneMeridianCoordinate
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq)
    fourZeroCentralRealizationPiOneMeridianAtBase
    fourZeroCentralInterfacePiOneMeridianProdEquiv
  · intro y
    rfl
  · exact fourZeroCentralInterfacePiOneMeridianProdEquiv_meridian
  · intro h
    exact fourZeroCentralInterfacePiOneMeridianProdEquiv.apply_symm_apply (1, h)

end Submission.ComplexProjectivePlaneTriangulation
