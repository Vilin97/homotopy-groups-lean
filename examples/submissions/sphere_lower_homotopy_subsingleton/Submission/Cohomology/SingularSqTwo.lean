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
* `Submission.sqTwoHsingDegreeThree_evaluation_homologyMk` identifies evaluation of the square
  with its explicit cup-one representative.
* `Submission.sqTwoHsingDegreeThree_mk_ne_zero_of_eval_cycle` detects a nonzero square by
  evaluating its representing cocycle on a cycle.
* `Submission.Hsing.map_congr` proves that homotopic maps induce the same pullback.
* `Submission.hsingLinearEquivOfHomotopyEquiv` packages homotopy invariance as a linear
  equivalence.
-/

open CategoryTheory AlgebraicTopology Simplicial

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

/-- The chain functional represented by the cup-one square of a degree-three singular
cocycle. -/
def sqTwoHsingDegreeThreeRepresentativeEvaluation {X : TopCat.{0}}
    (f : cocycles (TopCat.toSSet.obj X) (ZMod 2) 3) :
    (Csing X).X 5 ⟶ AddCommGrpCat.of (ZMod 2) :=
  (dualXEquiv (TopCat.toSSet.obj X) (ZMod 2) 5).symm
    (cupOneThreeSelfCocycle f : Cochain (TopCat.toSSet.obj X) (ZMod 2) 5)

/-- The square representative evaluates on a singular simplex by the explicit cup-one
formula. -/
@[simp]
theorem sqTwoHsingDegreeThreeRepresentativeEvaluation_gen {X : TopCat.{0}}
    (f : cocycles (TopCat.toSSet.obj X) (ZMod 2) 3)
    (σ : (TopCat.toSSet.obj X) _⦋5⦌) :
    sqTwoHsingDegreeThreeRepresentativeEvaluation f (gen σ) =
      cupOne (by omega : 1 ≤ 3)
        (f : Cochain (TopCat.toSSet.obj X) (ZMod 2) 3) f σ := by
  exact dualXEquiv_symm_apply (TopCat.toSSet.obj X) (ZMod 2) 5
    (cupOneThreeSelfCocycle f : Cochain (TopCat.toSSet.obj X) (ZMod 2) 5) σ

/-- Pulling a degree-three cocycle back and evaluating its cup-one square on a source chain
agrees with evaluating the original square on the pushed-forward chain. -/
theorem sqTwoHsingDegreeThreeRepresentativeEvaluation_natural
    {X Y : TopCat.{0}} (F : X ⟶ Y)
    (f : cocycles (TopCat.toSSet.obj Y) (ZMod 2) 3)
    (z : (Csing X).X 5) :
    sqTwoHsingDegreeThreeRepresentativeEvaluation
        (cocyclesMap (ZMod 2) (TopCat.toSSet.map F) 3 f) z =
      sqTwoHsingDegreeThreeRepresentativeEvaluation f
        ((CsingMap F).f 5 z) := by
  have hhom :
      (dualXEquiv (TopCat.toSSet.obj X) (ZMod 2) 5).symm
          (cupOneThreeSelfCocycle
            (cocyclesMap (ZMod 2) (TopCat.toSSet.map F) 3 f) :
              Cochain (TopCat.toSSet.obj X) (ZMod 2) 5) =
        (CsingMap F).f 5 ≫
          (dualXEquiv (TopCat.toSSet.obj Y) (ZMod 2) 5).symm
            (cupOneThreeSelfCocycle f :
              Cochain (TopCat.toSSet.obj Y) (ZMod 2) 5) := by
    apply chainComplexX_hom_ext
    intro σ
    change _ = (dualXEquiv (TopCat.toSSet.obj Y) (ZMod 2) 5).symm
      (cupOne (by omega : 1 ≤ 3)
        (f : Cochain (TopCat.toSSet.obj Y) (ZMod 2) 3) f)
      ((CsingMap F).f 5 (gen σ))
    rw [dualXEquiv_symm_apply]
    change cupOne (by omega : 1 ≤ 3)
        (Cochain.pullback (TopCat.toSSet.map F) 3
          (f : Cochain (TopCat.toSSet.obj Y) (ZMod 2) 3))
        (Cochain.pullback (TopCat.toSSet.map F) 3
          (f : Cochain (TopCat.toSSet.obj Y) (ZMod 2) 3)) σ = _
    rw [← pullback_cupOne, Cochain.pullback_apply]
    change _ = (dualXEquiv (TopCat.toSSet.obj Y) (ZMod 2) 5).symm
      (cupOne (by omega : 1 ≤ 3)
        (f : Cochain (TopCat.toSSet.obj Y) (ZMod 2) 3) f)
      ((CsingMap F).f 5 (gen σ))
    have hmap :
        (CsingMap F).f 5 (gen σ) =
          gen ((TopCat.toSSet.map F).app _ σ) :=
      chainComplexMap_gen (TopCat.toSSet.map F) σ
    rw [hmap, dualXEquiv_symm_apply]
  exact ConcreteCategory.congr_hom hhom z

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a represented degree-three square is its explicit cup-one chain
functional. -/
theorem sqTwoHsingDegreeThree_evaluation_homologyMk {X : TopCat.{0}}
    (f : cocycles (TopCat.toSSet.obj X) (ZMod 2) 3)
    (z : (Csing X).X 5)
    (hz : (Csing X).d 5 ((ComplexShape.down ℕ).next 5) z = 0) :
    ev (Csing X) (AddCommGrpCat.of (ZMod 2)) 5
        (HsingEquivDualHomology (ZMod 2) X 5
          (sqTwoHsingDegreeThree (Hcoh.mk f)))
        (homologyMk z hz) =
      sqTwoHsingDegreeThreeRepresentativeEvaluation f z := by
  rw [sqTwoHsingDegreeThree_mk]
  change ev (Csing X) (AddCommGrpCat.of (ZMod 2)) 5
      (HcohEquivDualHomology (TopCat.toSSet.obj X) (ZMod 2) 5
        (Hcoh.mk (cupOneThreeSelfCocycle f)))
      (homologyMk z hz) =
    (dualXEquiv (TopCat.toSSet.obj X) (ZMod 2) 5).symm
      (cupOneThreeSelfCocycle f :
        Cochain (TopCat.toSSet.obj X) (ZMod 2) 5) z
  rw [HcohEquivDualHomology_mk, ev_homologyMk, evCocycle_homologyMk,
    dualCocyclesEquiv_coe]
  rfl

/-- A nonzero evaluation of the cup-one square on a degree-five cycle proves that the
corresponding singular `Sq²` class is nonzero. -/
theorem sqTwoHsingDegreeThree_mk_ne_zero_of_eval_cycle {X : TopCat.{0}}
    (f : cocycles (TopCat.toSSet.obj X) (ZMod 2) 3)
    (z : (Csing X).X 5)
    (hz : (Csing X).d 5 ((ComplexShape.down ℕ).next 5) z = 0)
    (heval : sqTwoHsingDegreeThreeRepresentativeEvaluation f z ≠ 0) :
    sqTwoHsingDegreeThree (Hcoh.mk f) ≠ 0 := by
  rw [sqTwoHsingDegreeThree_mk]
  exact Hcoh.mk_ne_zero_of_eval_cycle
    (S := TopCat.toSSet.obj X) (R := ZMod 2)
    (cupOneThreeSelfCocycle f) z hz heval

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
