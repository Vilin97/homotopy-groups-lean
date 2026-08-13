/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Homology.UCT.Dual
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas

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

open CategoryTheory Limits Opposite ComposableArrows Abelian

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

/-- A morphism of short complexes dualizes contravariantly, reversing both its direction and its
three components. -/
def homDualShortComplexMap
    {S T : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c)}
    (f : S ⟶ T) (G : AddCommGrpCat.{0}) :
    homDualShortComplex T G ⟶ homDualShortComplex S G where
  τ₁ := homDualMap f.τ₃ G
  τ₂ := homDualMap f.τ₂ G
  τ₃ := homDualMap f.τ₁ G
  comm₁₂ := by
    change homDualMap f.τ₃ G ≫ homDualMap S.g G =
      homDualMap T.g G ≫ homDualMap f.τ₂ G
    rw [← homDualMap_comp, ← homDualMap_comp, f.comm₂₃]
  comm₂₃ := by
    change homDualMap f.τ₂ G ≫ homDualMap S.f G =
      homDualMap T.f G ≫ homDualMap f.τ₁ G
    rw [← homDualMap_comp, ← homDualMap_comp, f.comm₁₂]

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

/-- Dualizing an isomorphism reverses its direction. -/
def homDualIso {K L : HomologicalComplex AddCommGrpCat.{0} c}
    (e : K ≅ L) (G : AddCommGrpCat.{0}) : homDual L G ≅ homDual K G where
  hom := homDualMap e.hom G
  inv := homDualMap e.inv G
  hom_inv_id := by
    rw [← homDualMap_comp, e.inv_hom_id, homDualMap_id]
  inv_hom_id := by
    rw [← homDualMap_comp, e.hom_inv_id, homDualMap_id]

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

/-! ### The missing left-hand form of the five lemma -/

/-- In a morphism of homology long exact sequences, the map on the first term in degree `j` is an
isomorphism when the maps on the second and third terms are isomorphisms in two adjacent degrees
`i` and `j`. -/
theorem isIso_homologyMap_τ₁_of_rel
    {S T : ShortComplex (HomologicalComplex AddCommGrpCat.{0} c)}
    (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (i j : ι) (hij : c.Rel i j)
    [IsIso (HomologicalComplex.homologyMap f.τ₂ i)]
    [IsIso (HomologicalComplex.homologyMap f.τ₃ i)]
    [IsIso (HomologicalComplex.homologyMap f.τ₂ j)]
    [IsIso (HomologicalComplex.homologyMap f.τ₃ j)] :
    IsIso (HomologicalComplex.homologyMap f.τ₁ j) := by
  let F := HomologicalComplex.HomologySequence.mapComposableArrows₅ f hS hT i j hij
  haveI : Mono (HomologicalComplex.homologyMap f.τ₁ j) := by
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map F)
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS i j hij).δ₀.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hT i j hij).δ₀.δlast
    · change Epi (HomologicalComplex.homologyMap f.τ₂ i)
      infer_instance
    · change Mono (HomologicalComplex.homologyMap f.τ₃ i)
      infer_instance
    · change Mono (HomologicalComplex.homologyMap f.τ₂ j)
      infer_instance
  haveI : Epi (HomologicalComplex.homologyMap f.τ₁ j) := by
    apply epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map F)
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS i j hij).δ₀.δ₀
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hT i j hij).δ₀.δ₀
    · change Epi (HomologicalComplex.homologyMap f.τ₃ i)
      infer_instance
    · change Epi (HomologicalComplex.homologyMap f.τ₂ j)
      infer_instance
    · change Mono (HomologicalComplex.homologyMap f.τ₃ j)
      infer_instance
  exact isIso_of_mono_of_epi _

end Submission
