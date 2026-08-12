/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.DualBridge
import Submission.Homology.UCT.HomologyClass
import Submission.Hurewicz.Vanishing

/-!
# Relative homology classes represented by singular simplices

A singular `(n+1)`-simplex of `X` whose codimension-one faces all factor through a subspace
`A` is a cycle in the relative singular chain complex `C_*(X,A)`.  This file packages the
corresponding chain and relative homology class.

The construction is deliberately chain-level.  It is the bridge needed to compare a normalized
singular simplex with the relative Hurewicz class of its cubical reparametrisation.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite

-- Upstream Mathlib marks these `@[implicit_reducible]`; our pinned revision does not, and without
-- it rewriting between the two presentations of singular chains fails at `instances` transparency.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor
  CategoryTheory.Functor.postcompose₂ CategoryTheory.SimplicialObject.whiskering
  CategoryTheory.Functor.whiskeringLeft CategoryTheory.Functor.comp

noncomputable section

namespace Submission

variable {X Y : TopCat.{0}} {A : Set X} {B : Set Y}

/-- A singular-chain map sends a generator to the generator indexed by the composite simplex. -/
@[simp]
theorem CsingMap_gen (f : X ⟶ Y) {n : ℕ} (s : Sng X _⦋n⦌) :
    (CsingMap f).f n (gen s) = gen ((TopCat.toSSet.map f).app _ s) := by
  rw [CsingMap_f_eq_simpMap, apply_gen, ι_simpMap]
  rfl

/-- The image of a singular simplex in the relative chain complex. -/
def relativeSimplexChain (A : Set X) {n : ℕ} (s : Sng X _⦋n⦌) :
    (relComplex (subIncl A)).X n :=
  (relProj (subIncl A)).f n (gen s)

/-- A simplex whose faces factor through `A` is a relative cycle. -/
theorem relativeSimplexChain_cycle {n : ℕ} (s : Sng X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), ∃ t : Sng (TopCat.of A) _⦋n⦌,
      (sngIncl A).app _ t = SSet.face (Sng X) i s) :
    (relComplex (subIncl A)).d (n + 1) n (relativeSimplexChain A s) = 0 := by
  have hd : (Csing X).d (n + 1) n (gen s) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • gen (SSet.face (Sng X) i s) :=
    d_gen s
  rw [relativeSimplexChain, ← ConcreteCategory.comp_apply,
    (relProj (subIncl A)).comm (n + 1) n, ConcreteCategory.comp_apply, hd, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_zsmul]
  obtain ⟨t, ht⟩ := hface i
  have hzero :
      (relProj (subIncl A)).f n (gen (SSet.face (Sng X) i s)) = 0 := by
    rw [← ht, ← CsingMap_gen (subIncl A), ← ConcreteCategory.comp_apply,
      CsingMap_comp_relProj_f, zero_hom_apply]
  rw [hzero, smul_zero]

/-- The relative homology class represented by a simplex whose faces lie in the subspace. -/
def relativeSimplexClass {n : ℕ} (s : Sng X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), ∃ t : Sng (TopCat.of A) _⦋n⦌,
      (sngIncl A).app _ t = SSet.face (Sng X) i s) : HrelSet (n + 1) A :=
  homologyMk (relativeSimplexChain A s) (by
    rw [ChainComplex.next_nat_succ]
    exact relativeSimplexChain_cycle s hface)

/-- A map between relative complexes sends an explicit simplex class to another whenever it sends
the representing relative chains to one another. -/
theorem homologyMap_relativeSimplexClass {n : ℕ}
    (F : relComplex (subIncl A) ⟶ relComplex (subIncl B))
    (s : Sng X _⦋n + 1⦌)
    (hs : ∀ i : Fin (n + 2), ∃ u : Sng (TopCat.of A) _⦋n⦌,
      (sngIncl A).app _ u = SSet.face (Sng X) i s)
    (t : Sng Y _⦋n + 1⦌)
    (ht : ∀ i : Fin (n + 2), ∃ v : Sng (TopCat.of B) _⦋n⦌,
      (sngIncl B).app _ v = SSet.face (Sng Y) i t)
    (hst : F.f (n + 1) (relativeSimplexChain A s) = relativeSimplexChain B t) :
    HomologicalComplex.homologyMap F (n + 1) (relativeSimplexClass s hs) =
      relativeSimplexClass t ht := by
  unfold relativeSimplexClass
  exact homologyMap_homologyMk_congr F _ _ _ _ hst

end Submission
