/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.GroupTheory.GroupExtension.Basic
import Submission.ComplexProjectivePlaneTrisectionMeridianNormalForms

/-!
# Split group extensions from the trisection meridians

This file promotes the three explicit short exact sequences to Mathlib's `GroupExtension`
structure.  Their previously constructed homomorphic sections then become certified
`GroupExtension.Splitting` objects.

The result packages each central-to-pairwise fundamental-group map as a split extension of an
infinite cyclic pairwise group by its infinite cyclic meridian subgroup.
-/

noncomputable section

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission

/-- Package injectivity, multiplicative exactness, and surjectivity as a group extension. -/
def groupExtensionOfInjectiveMulExactSurjective
    {N E G : Type*} [Group N] [Group E] [Group G]
    (i : N →* E) (p : E →* G)
    (hi : Function.Injective i) (hexact : Function.MulExact i p)
    (hp : Function.Surjective p) :
    GroupExtension N E G where
  inl := i
  rightHom := p
  inl_injective := hi
  range_inl_eq_ker_rightHom := (MonoidHom.mulExact_iff.mp hexact).symm
  rightHom_surjective := hp

/-- A homomorphic right inverse promotes a short exact sequence to a splitting of the
corresponding group extension. -/
def groupExtensionSplittingOfSection
    {N E G : Type*} [Group N] [Group E] [Group G]
    (i : N →* E) (p : E →* G)
    (hi : Function.Injective i) (hexact : Function.MulExact i p)
    (hp : Function.Surjective p)
    (s : G →* E) (hs : p.comp s = MonoidHom.id G) :
    (groupExtensionOfInjectiveMulExactSurjective i p hi hexact hp).Splitting where
  toMonoidHom := s
  rightInverse_rightHom x := DFunLike.congr_fun hs x

end Submission

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The zero-five central-to-pairwise map as an extension by its integral meridian. -/
noncomputable def zeroFiveCentralInterfacePiOneGroupExtension :
    GroupExtension
      (Multiplicative ℤ)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        zeroFiveCentralRealizationBase)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 0 5)))
        ((SSet.toTop.map
          (zeroFiveMeridianBoundaryInclCentral ≫
            zeroFiveCentralInterfaceInclPairwise)).hom
          zeroFiveBoundaryRealizationBase)) :=
  groupExtensionOfInjectiveMulExactSurjective
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        zeroFiveCentralRealizationBase)
      zeroFiveCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq)
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.1
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.2.1
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.2.2

/-- The zero-five group extension split by its explicit homomorphic section. -/
noncomputable def zeroFiveCentralInterfacePiOneGroupExtensionSplitting :
    zeroFiveCentralInterfacePiOneGroupExtension.Splitting :=
  groupExtensionSplittingOfSection
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        zeroFiveCentralRealizationBase)
      zeroFiveCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map zeroFiveCentralInterfaceInclPairwise).hom
      zeroFiveCentralRealizationBase_map_pairwise_eq)
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.1
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.2.1
    zeroFiveCentralInterfaceInclPairwise_piOne_shortExact.2.2
    zeroFiveCentralInterfaceInclPairwisePiOneSection
    zeroFiveCentralInterfaceInclPairwisePiOneSection_rightInverse

/-- The five-four central-to-pairwise map as an extension by its integral meridian. -/
noncomputable def fiveFourCentralInterfacePiOneGroupExtension :
    GroupExtension
      (Multiplicative ℤ)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fiveFourCentralRealizationBase)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 5 4)))
        ((SSet.toTop.map
          (fiveFourMeridianBoundaryInclCentral ≫
            fiveFourCentralInterfaceInclPairwise)).hom
          fiveFourBoundaryRealizationBase)) :=
  groupExtensionOfInjectiveMulExactSurjective
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fiveFourCentralRealizationBase)
      fiveFourCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq)
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.1
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.2.1
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.2.2

/-- The five-four group extension split by its explicit homomorphic section. -/
noncomputable def fiveFourCentralInterfacePiOneGroupExtensionSplitting :
    fiveFourCentralInterfacePiOneGroupExtension.Splitting :=
  groupExtensionSplittingOfSection
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fiveFourCentralRealizationBase)
      fiveFourCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fiveFourCentralInterfaceInclPairwise).hom
      fiveFourCentralRealizationBase_map_pairwise_eq)
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.1
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.2.1
    fiveFourCentralInterfaceInclPairwise_piOne_shortExact.2.2
    fiveFourCentralInterfaceInclPairwisePiOneSection
    fiveFourCentralInterfaceInclPairwisePiOneSection_rightInverse

/-- The four-zero central-to-pairwise map as an extension by its integral meridian. -/
noncomputable def fourZeroCentralInterfacePiOneGroupExtension :
    GroupExtension
      (Multiplicative ℤ)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fourZeroCentralRealizationBase)
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet (pairwiseInterfaceFacets 4 0)))
        ((SSet.toTop.map
          (fourZeroMeridianBoundaryInclCentral ≫
            fourZeroCentralInterfaceInclPairwise)).hom
          fourZeroBoundaryRealizationBase)) :=
  groupExtensionOfInjectiveMulExactSurjective
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fourZeroCentralRealizationBase)
      fourZeroCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq)
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.1
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.2.1
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.2.2

/-- The four-zero group extension split by its explicit homomorphic section. -/
noncomputable def fourZeroCentralInterfacePiOneGroupExtensionSplitting :
    fourZeroCentralInterfacePiOneGroupExtension.Splitting :=
  groupExtensionSplittingOfSection
    (zpowersHom
      (HomotopyGroup.Pi 1
        (SSet.toTop.obj (orderedSSet centralInterfaceFacets))
        fourZeroCentralRealizationBase)
      fourZeroCentralRealizationPiOneClass)
    (HomotopyGroup.mapHom (N := Fin 1)
      (SSet.toTop.map fourZeroCentralInterfaceInclPairwise).hom
      fourZeroCentralRealizationBase_map_pairwise_eq)
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.1
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.2.1
    fourZeroCentralInterfaceInclPairwise_piOne_shortExact.2.2
    fourZeroCentralInterfaceInclPairwisePiOneSection
    fourZeroCentralInterfaceInclPairwisePiOneSection_rightInverse

end Submission.ComplexProjectivePlaneTriangulation
