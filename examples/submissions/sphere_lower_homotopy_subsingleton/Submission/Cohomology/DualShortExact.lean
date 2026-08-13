/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Homology.UCT.Dual
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Duals of degreewise split short exact sequences

If a short complex of chain complexes is split in every degree, applying `Hom(-, G)` reverses its
arrows and again gives a degreewise split short exact sequence of cochain complexes.  This is the
algebraic input needed for cohomological Mayer--Vietoris: unlike a general contravariant Hom
functor, no injectivity assumption on `G` is needed because the original sequence is split before
dualizing.

## Main definitions

* `Submission.homDualShortComplex` -- the reversed short complex of dual complexes;
* `Submission.homDualSplitting` -- the induced splitting in one degree;
* `Submission.homDualShortComplex_shortExact` -- short exactness from degreewise splittings.
-/

open CategoryTheory Limits Opposite

noncomputable section

namespace Submission

variable {ι : Type*} {c : ComplexShape ι}

/-- Applying `Hom(-, G)` to `K₁ ⟶ K₂ ⟶ K₃` gives the reversed short complex
`Hom(K₃,G) ⟶ Hom(K₂,G) ⟶ Hom(K₁,G)`. -/
def homDualShortComplex
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0}) :
    ShortComplex (HomologicalComplex AddCommGrpCat.{0} c.symm) :=
  ShortComplex.mk (homDualMap S.g G) (homDualMap S.f G) (by
    rw [← homDualMap_comp, S.zero]
    ext i φ
    simp)

@[simp]
theorem homDualShortComplex_X₁
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0}) :
    (homDualShortComplex S G).X₁ = homDual S.X₃ G := rfl

@[simp]
theorem homDualShortComplex_X₂
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0}) :
    (homDualShortComplex S G).X₂ = homDual S.X₂ G := rfl

@[simp]
theorem homDualShortComplex_X₃
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0}) :
    (homDualShortComplex S G).X₃ = homDual S.X₁ G := rfl

/-- The dual of a binary biproduct is the binary biproduct of the duals. -/
def homDualBiprodIso
    (K L : HomologicalComplex AddCommGrpCat.{0} c) (G : AddCommGrpCat.{0}) :
    homDual (K ⊞ L) G ≅ homDual K G ⊞ homDual L G where
  hom := biprod.lift (homDualMap (biprod.inl : K ⟶ K ⊞ L) G)
    (homDualMap (biprod.inr : L ⟶ K ⊞ L) G)
  inv := biprod.desc (homDualMap (biprod.fst : K ⊞ L ⟶ K) G)
    (homDualMap (biprod.snd : K ⊞ L ⟶ L) G)
  hom_inv_id := by
    rw [biprod.lift_desc, ← homDualMap_comp, ← homDualMap_comp, ← homDualMap_id,
      ← homDualMap_add, biprod.total]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← homDualMap_comp]

/-- Dualizing reverses a chain-homotopy equivalence. -/
def homDualHomotopyEquiv
    {K L : HomologicalComplex AddCommGrpCat.{0} c}
    (e : HomotopyEquiv K L) (G : AddCommGrpCat.{0}) :
    HomotopyEquiv (homDual L G) (homDual K G) where
  hom := homDualMap e.hom G
  inv := homDualMap e.inv G
  homotopyHomInvId := by
    rw [← homDualMap_comp]
    simpa using homDualHomotopy e.homotopyInvHomId G
  homotopyInvHomId := by
    rw [← homDualMap_comp]
    simpa using homDualHomotopy e.homotopyHomInvId G

/-- A degreewise splitting dualizes to a splitting of the reversed degreewise short complex. -/
def homDualSplitting
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0}) (i : ι)
    (s : ShortComplex.Splitting
      (S.map (HomologicalComplex.eval AddCommGrpCat.{0} c i))) :
    ShortComplex.Splitting
      ((homDualShortComplex S G).map
        (HomologicalComplex.eval AddCommGrpCat.{0} c.symm i)) := by
  exact s.op.map (preadditiveYoneda.obj G)

/-- The reversed dual of a degreewise split short complex is short exact. -/
theorem homDualShortComplex_shortExact
    (S : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c))
    (G : AddCommGrpCat.{0})
    (hS : ∀ i : ι, ShortComplex.Splitting
      (S.map (HomologicalComplex.eval AddCommGrpCat.{0} c i))) :
    (homDualShortComplex S G).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
    (homDualSplitting S G i (hS i)).shortExact

end Submission
