/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.CupOne
import Submission.Cohomology.DualBridge
import Submission.Homology.Homotopy

/-!
# The degree-three second square on singular cohomology

This file specializes the simplicial operation constructed in
`Submission/Cohomology/CupOne.lean` to the singular simplicial set of a topological space.  It
also proves homotopy invariance of the custom singular-cohomology functor by dualizing the chain
homotopy on singular chains.  These are the functorial ingredients needed to use the operation on
mapping cones.

## Main results

* `Submission.sqTwoHsingDegreeThree` is `Sq² : H³(X; F₂) → H⁵(X; F₂)`.
* `Submission.sqTwoHsingDegreeThree_natural` proves naturality under continuous maps.
* `Submission.Hsing.map_congr` proves that homotopic maps induce the same pullback.
* `Submission.hsingLinearEquivOfHomotopyEquiv` packages homotopy invariance as a linear
  equivalence.
-/

open CategoryTheory AlgebraicTopology

noncomputable section

namespace Submission

/-- The degree-three instance of the second Steenrod square on singular cohomology. -/
def sqTwoHsingDegreeThree {X : TopCat.{0}}
    (x : Hsing 3 X (ZMod 2)) : Hsing 5 X (ZMod 2) :=
  sqTwoDegreeThree x

@[simp]
theorem sqTwoHsingDegreeThree_mk {X : TopCat.{0}}
    (f : cocycles (TopCat.toSSet.obj X) (ZMod 2) 3) :
    sqTwoHsingDegreeThree (Hcoh.mk f) = Hcoh.mk (cupOneThreeSelfCocycle f) :=
  sqTwoDegreeThree_mk f

/-- The singular operation `Sq² : H³ → H⁵` is natural under continuous maps. -/
theorem sqTwoHsingDegreeThree_natural {X Y : TopCat.{0}} (f : X ⟶ Y)
    (x : Hsing 3 Y (ZMod 2)) :
    Hsing.map f 5 (sqTwoHsingDegreeThree x) =
      sqTwoHsingDegreeThree (Hsing.map f 3 x) :=
  sqTwoDegreeThree_natural (TopCat.toSSet.map f) x

variable {R : Type} [CommRing R]

/-- Homotopic continuous maps induce the same pullback on the custom singular cohomology. -/
theorem Hsing.map_congr {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (n : ℕ) : Hsing.map (R := R) f n = Hsing.map g n := by
  let Hchain := H.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
  change Homotopy (CsingMap f) (CsingMap g) at Hchain
  ext x
  apply (HsingEquivDualHomology R X n).injective
  rw [HsingEquivDualHomology_naturality, HsingEquivDualHomology_naturality]
  rw [(homDualHomotopy Hchain (AddCommGrpCat.of R)).homologyMap_eq n]

/-- A homotopy equivalence induces a linear equivalence on singular cohomology, contravariantly. -/
def hsingLinearEquivOfHomotopyEquiv {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X)) (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y))
    (n : ℕ) : Hsing n Y R ≃ₗ[R] Hsing n X R where
  toLinearMap := Hsing.map f n
  invFun := Hsing.map g n
  left_inv x := by
    change Hsing.map g n (Hsing.map f n x) = x
    have hcomp := LinearMap.congr_fun (Hsing.map_comp (R := R) g f n) x
    rw [LinearMap.comp_apply] at hcomp
    rw [← hcomp, Hsing.map_congr H₂, Hsing.map_id]
    rfl
  right_inv x := by
    change Hsing.map f n (Hsing.map g n x) = x
    have hcomp := LinearMap.congr_fun (Hsing.map_comp (R := R) f g n) x
    rw [LinearMap.comp_apply] at hcomp
    rw [← hcomp, Hsing.map_congr H₁, Hsing.map_id]
    rfl

end Submission
