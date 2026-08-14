/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.ComplexProjectivePlaneTrisectionMeridianGroupExtensions

/-!
# Triviality of the split trisection group extensions

The product decompositions respect both arrows of the three short exact sequences.  Consequently
each trisection group extension is equivalent to the semidirect product for the trivial action of
the pairwise fundamental group on the integral meridian group.

These are equivalences of `GroupExtension` structures: they commute with the meridian inclusions
on the left and the central-to-pairwise maps on the right.
-/

noncomputable section

namespace Submission

/-- A product equivalence compatible with both arrows identifies a group extension with the
extension associated to the trivial-action semidirect product. -/
noncomputable def groupExtensionEquivTrivialOfProdMulEquiv
    {N E G : Type*} [Group N] [Group E] [Group G]
    (S : GroupExtension N E G)
    (e : E ≃* N × G)
    (hinl : e.toMonoidHom.comp S.inl = MonoidHom.inl N G)
    (hright : (MonoidHom.snd N G).comp e.toMonoidHom = S.rightHom) :
    S.Equiv
      (SemidirectProduct.toGroupExtension
        (1 : G →* MulAut N)) := by
  apply GroupExtension.Equiv.ofMonoidHom
    (SemidirectProduct.mulEquivProd.symm.toMonoidHom.comp
      e.toMonoidHom)
  · apply MonoidHom.ext
    intro n
    apply SemidirectProduct.mulEquivProd.injective
    change e (S.inl n) = (n, 1)
    exact DFunLike.congr_fun hinl n
  · ext x
    change (e x).2 = S.rightHom x
    exact DFunLike.congr_fun hright x

/-- If a product equivalence sends a class to the positive integer generator, then it sends the
associated integral power homomorphism to the first-factor inclusion. -/
theorem mulEquiv_comp_zpowersHom_eq_inl_of_apply_eq_generator
    {E G : Type*} [Group E] [Group G]
    (e : E ≃* Multiplicative ℤ × G) (g : E)
    (hg : e g = (Multiplicative.ofAdd (1 : ℤ), 1)) :
    e.toMonoidHom.comp (zpowersHom E g) =
      MonoidHom.inl (Multiplicative ℤ) G := by
  apply MonoidHom.ext
  intro n
  change e (g ^ n.toAdd) = (n, 1)
  rw [map_zpow, hg]
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    simp
  · simp

end Submission

open CategoryTheory Simplicial
open scoped Topology Topology.Homotopy

namespace Submission.ComplexProjectivePlaneTriangulation

open FiniteOrderedComplex

/-- The zero-five group extension is equivalent to the trivial-action semidirect product. -/
noncomputable def zeroFiveCentralInterfacePiOneGroupExtensionEquivTrivial :
    zeroFiveCentralInterfacePiOneGroupExtension.Equiv
      (SemidirectProduct.toGroupExtension
        (1 :
          HomotopyGroup.Pi 1
              (SSet.toTop.obj
                (orderedSSet (pairwiseInterfaceFacets 0 5)))
              ((SSet.toTop.map
                (zeroFiveMeridianBoundaryInclCentral ≫
                  zeroFiveCentralInterfaceInclPairwise)).hom
                zeroFiveBoundaryRealizationBase) →*
            MulAut (Multiplicative ℤ))) := by
  apply groupExtensionEquivTrivialOfProdMulEquiv
    zeroFiveCentralInterfacePiOneGroupExtension
    zeroFiveCentralInterfacePiOneMeridianProdEquiv
  · apply mulEquiv_comp_zpowersHom_eq_inl_of_apply_eq_generator
    have hg : zeroFiveCentralInterfacePiOneMeridianProdEquiv
        zeroFiveCentralRealizationPiOneMeridianAtBase =
      (Multiplicative.ofAdd (1 : ℤ), 1) :=
        zeroFiveCentralInterfacePiOneMeridianProdEquiv_meridian
    exact hg
  · rfl

/-- The five-four group extension is equivalent to the trivial-action semidirect product. -/
noncomputable def fiveFourCentralInterfacePiOneGroupExtensionEquivTrivial :
    fiveFourCentralInterfacePiOneGroupExtension.Equiv
      (SemidirectProduct.toGroupExtension
        (1 :
          HomotopyGroup.Pi 1
              (SSet.toTop.obj
                (orderedSSet (pairwiseInterfaceFacets 5 4)))
              ((SSet.toTop.map
                (fiveFourMeridianBoundaryInclCentral ≫
                  fiveFourCentralInterfaceInclPairwise)).hom
                fiveFourBoundaryRealizationBase) →*
            MulAut (Multiplicative ℤ))) := by
  apply groupExtensionEquivTrivialOfProdMulEquiv
    fiveFourCentralInterfacePiOneGroupExtension
    fiveFourCentralInterfacePiOneMeridianProdEquiv
  · apply mulEquiv_comp_zpowersHom_eq_inl_of_apply_eq_generator
    have hg : fiveFourCentralInterfacePiOneMeridianProdEquiv
        fiveFourCentralRealizationPiOneMeridianAtBase =
      (Multiplicative.ofAdd (1 : ℤ), 1) :=
        fiveFourCentralInterfacePiOneMeridianProdEquiv_meridian
    exact hg
  · rfl

/-- The four-zero group extension is equivalent to the trivial-action semidirect product. -/
noncomputable def fourZeroCentralInterfacePiOneGroupExtensionEquivTrivial :
    fourZeroCentralInterfacePiOneGroupExtension.Equiv
      (SemidirectProduct.toGroupExtension
        (1 :
          HomotopyGroup.Pi 1
              (SSet.toTop.obj
                (orderedSSet (pairwiseInterfaceFacets 4 0)))
              ((SSet.toTop.map
                (fourZeroMeridianBoundaryInclCentral ≫
                  fourZeroCentralInterfaceInclPairwise)).hom
                fourZeroBoundaryRealizationBase) →*
            MulAut (Multiplicative ℤ))) := by
  apply groupExtensionEquivTrivialOfProdMulEquiv
    fourZeroCentralInterfacePiOneGroupExtension
    fourZeroCentralInterfacePiOneMeridianProdEquiv
  · apply mulEquiv_comp_zpowersHom_eq_inl_of_apply_eq_generator
    have hg : fourZeroCentralInterfacePiOneMeridianProdEquiv
        fourZeroCentralRealizationPiOneMeridianAtBase =
      (Multiplicative.ofAdd (1 : ℤ), 1) :=
        fourZeroCentralInterfacePiOneMeridianProdEquiv_meridian
    exact hg
  · rfl

end Submission.ComplexProjectivePlaneTriangulation
