/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.DualBridge

/-!
# Chain-level evaluation of singular cup products

The cup product on the custom singular-cohomology model is represented by the explicit
Alexander--Whitney cup cochain.  This file identifies its evaluation under the cohomology/dual
homology bridge with direct evaluation of that cochain on a singular cycle.
-/

open CategoryTheory

noncomputable section

namespace Submission

variable {R : Type} [CommRing R]

/-- The chain functional represented by the cup product of two singular cocycles. -/
noncomputable def cupHsingRepresentativeEvaluation {X : TopCat.{0}} {p q n : ℕ}
    (h : p + q = n)
    (f : cocycles (TopCat.toSSet.obj X) R p)
    (g : cocycles (TopCat.toSSet.obj X) R q)
    (z : (Csing X).X n) : R :=
  (dualXEquiv (TopCat.toSSet.obj X) R n).symm
    (cupCocyclesₗ (TopCat.toSSet.obj X) R h f g :
      Cochain (TopCat.toSSet.obj X) R n) z

/-- Pulling both cocycles back and evaluating on a source chain agrees with evaluating the
original cup product on the pushed-forward chain. -/
theorem cupHsingRepresentativeEvaluation_natural {X Y : TopCat.{0}}
    (F : X ⟶ Y) {p q n : ℕ} (h : p + q = n)
    (f : cocycles (TopCat.toSSet.obj Y) R p)
    (g : cocycles (TopCat.toSSet.obj Y) R q)
    (z : (Csing X).X n) :
    cupHsingRepresentativeEvaluation h
        (cocyclesMap R (TopCat.toSSet.map F) p f)
        (cocyclesMap R (TopCat.toSSet.map F) q g) z =
      cupHsingRepresentativeEvaluation h f g ((CsingMap F).f n z) := by
  have hhom :
      (dualXEquiv (TopCat.toSSet.obj X) R n).symm
          (cupCocyclesₗ (TopCat.toSSet.obj X) R h
            (cocyclesMap R (TopCat.toSSet.map F) p f)
            (cocyclesMap R (TopCat.toSSet.map F) q g) :
              Cochain (TopCat.toSSet.obj X) R n) =
        (CsingMap F).f n ≫
          (dualXEquiv (TopCat.toSSet.obj Y) R n).symm
            (cupCocyclesₗ (TopCat.toSSet.obj Y) R h f g :
              Cochain (TopCat.toSSet.obj Y) R n) := by
    apply chainComplexX_hom_ext
    intro σ
    change _ = (dualXEquiv (TopCat.toSSet.obj Y) R n).symm
      (cupOfEq h (f : Cochain (TopCat.toSSet.obj Y) R p)
        (g : Cochain (TopCat.toSSet.obj Y) R q))
      ((CsingMap F).f n (gen σ))
    rw [dualXEquiv_symm_apply]
    change cupOfEq h
        (Cochain.pullback (TopCat.toSSet.map F) p
          (f : Cochain (TopCat.toSSet.obj Y) R p))
        (Cochain.pullback (TopCat.toSSet.map F) q
          (g : Cochain (TopCat.toSSet.obj Y) R q)) σ =
      (dualXEquiv (TopCat.toSSet.obj Y) R n).symm
        (cupOfEq h (f : Cochain (TopCat.toSSet.obj Y) R p)
          (g : Cochain (TopCat.toSSet.obj Y) R q))
        ((CsingMap F).f n (gen σ))
    rw [← pullback_cupOfEq, Cochain.pullback_apply]
    change _ = (dualXEquiv (TopCat.toSSet.obj Y) R n).symm
      (cupOfEq h (f : Cochain (TopCat.toSSet.obj Y) R p)
        (g : Cochain (TopCat.toSSet.obj Y) R q))
      ((CsingMap F).f n (gen σ))
    have hmap :
        (CsingMap F).f n (gen σ) =
          gen ((TopCat.toSSet.map F).app _ σ) :=
      chainComplexMap_gen (TopCat.toSSet.map F) σ
    rw [hmap, dualXEquiv_symm_apply]
  exact ConcreteCategory.congr_hom hhom z

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a represented cup product is its explicit Alexander--Whitney chain
functional. -/
theorem cupHsing_evaluation_homologyMk {X : TopCat.{0}} {p q n : ℕ}
    (h : p + q = n)
    (f : cocycles (TopCat.toSSet.obj X) R p)
    (g : cocycles (TopCat.toSSet.obj X) R q)
    (z : (Csing X).X n)
    (hz : (Csing X).d n ((ComplexShape.down ℕ).next n) z = 0) :
    ev (Csing X) (AddCommGrpCat.of R) n
        (HsingEquivDualHomology R X n
          (cupHsing h (Hcoh.mk f) (Hcoh.mk g)))
        (homologyMk z hz) =
      cupHsingRepresentativeEvaluation h f g z := by
  change ev (Csing X) (AddCommGrpCat.of R) n
      (HcohEquivDualHomology (TopCat.toSSet.obj X) R n
        (Hcoh.mk (cupCocyclesₗ (TopCat.toSSet.obj X) R h f g)))
      (homologyMk z hz) =
    (dualXEquiv (TopCat.toSSet.obj X) R n).symm
      (cupCocyclesₗ (TopCat.toSSet.obj X) R h f g :
        Cochain (TopCat.toSSet.obj X) R n) z
  rw [HcohEquivDualHomology_mk, ev_homologyMk, evCocycle_homologyMk,
    dualCocyclesEquiv_coe]
  rfl

/-- A nonzero Alexander--Whitney evaluation on a cycle proves that the represented singular
cup product is nonzero. -/
theorem cupHsing_mk_ne_zero_of_eval_cycle {X : TopCat.{0}} {p q n : ℕ}
    (h : p + q = n)
    (f : cocycles (TopCat.toSSet.obj X) R p)
    (g : cocycles (TopCat.toSSet.obj X) R q)
    (z : (Csing X).X n)
    (hz : (Csing X).d n ((ComplexShape.down ℕ).next n) z = 0)
    (heval : cupHsingRepresentativeEvaluation h f g z ≠ 0) :
    cupHsing h (Hcoh.mk f) (Hcoh.mk g) ≠ 0 := by
  intro hzero
  have hvalue := cupHsing_evaluation_homologyMk h f g z hz
  rw [hzero, map_zero, map_zero] at hvalue
  exact heval hvalue.symm

end Submission
