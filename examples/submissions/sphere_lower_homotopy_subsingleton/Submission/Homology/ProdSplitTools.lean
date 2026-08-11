/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.ProdSphereZero

/-!
# Tools for the product formula `H_*(F × Sᵈ)`

Two ingredients of the induction on `d`, both independent of the sphere.

* **A contractible factor is invisible, via the projection.**  If `Y` is contractible then
  `prodFstMap F Y : F × Y ⟶ F` is a homotopy equivalence, and — crucially — the homotopy
  equivalence `Submission.prodHomotopyEquivOfContractible` of
  `Submission/Homotopy/ContractionData.lean` has `Prod.fst` as its underlying map *on the nose*
  (`Submission.prodFstMapIso_hom` is `rfl`).  So no compatibility between a chosen contraction of
  `Y` and the projection has to be checked: the two maps out of `H_k(F × (A ∩ B))` into `H_k(F)`
  coming from the two contractible pieces are both literally `HgrpMap _ (prodFstMap _ _)`.

* **A split epimorphism splits off its kernel.**  `Submission.biprodIsoOfSplitEpi` turns a section
  `σ` of `π : N ⟶ M` into `N ≅ M ⊞ ker π` whose first component is `π` itself.  Applied to
  `π = HgrpMap k (prodFstMap F S)` and `σ = HgrpMap k (prodSectMap F s)`, this already produces an
  isomorphism of exactly the shape `Submission.ProdSphereSplitting` asks for
  (`Submission.hgrpProdSplitIso`, `Submission.hgrpProdSplitIso_hom_comp_fst`), reducing the product
  formula to the identification of `ker (HgrpMap k (prodFstMap F S))`.

## Main definitions

* `Submission.prodFstMapIso` — `Hₖ(F × Y) ≅ Hₖ(F)` for contractible `Y`, via the projection.
* `Submission.biprodIsoOfSplitEpi` — `N ≅ M ⊞ ker π` for a split epimorphism `π`.
* `Submission.hgrpProdSplitIso` — `Hₖ(F × S) ≅ Hₖ(F) ⊞ ker (Hₖ(F × S) ⟶ Hₖ(F))`.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

/-! ### A contractible factor, seen through the projection -/

/-- For contractible `Y`, the projection `F × Y ⟶ F` induces an isomorphism on homology. -/
def prodFstMapIso (F : TopCat.{0}) (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y] (n : ℕ) :
    Hgrp n (TopCat.of (↥F × Y)) ≅ Hgrp n F :=
  hgrpIsoOfHEquiv (prodHomotopyEquivOfContractible ↥F Y) n

/-- The isomorphism of `Submission.prodFstMapIso` **is** the map induced by the projection; this is
true by `rfl`, which is what makes the Mayer–Vietoris comparison in the induction step free. -/
@[simp]
theorem prodFstMapIso_hom (F : TopCat.{0}) (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y]
    (n : ℕ) : (prodFstMapIso F Y n).hom = HgrpMap n (prodFstMap F Y) := rfl

/-- For contractible `Y`, the projection `F × Y ⟶ F` induces an isomorphism on homology. -/
theorem isIso_HgrpMap_prodFstMap_of_contractible (F : TopCat.{0}) (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] (n : ℕ) : IsIso (HgrpMap n (prodFstMap F Y)) :=
  (prodFstMapIso F Y n).isIso_hom

/-! ### Splitting off the kernel of a split epimorphism -/

section SplitEpi

variable {C : Type*} [Category* C] [Abelian C] {N M : C} (π : N ⟶ M) (σ : M ⟶ N)
  (h : σ ≫ π = 𝟙 M)

include h in
theorem splitEpi_aux : (𝟙 N - π ≫ σ) ≫ π = 0 := by
  rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, h, Category.comp_id, sub_self]

/-- If `π : N ⟶ M` admits a section `σ`, then `N` splits as `M ⊞ ker π`, with the first component
of the splitting equal to `π`. -/
def biprodIsoOfSplitEpi : N ≅ M ⊞ kernel π where
  hom := biprod.lift π (kernel.lift π (𝟙 N - π ≫ σ) (splitEpi_aux π σ h))
  inv := biprod.desc σ (kernel.ι π)
  hom_inv_id := by
    rw [biprod.lift_desc, kernel.lift_ι]
    abel
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, biprod.inl_fst, h]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        refine (cancel_mono (kernel.ι π)).1 ?_
        rw [Category.assoc, kernel.lift_ι, Preadditive.comp_sub, Category.comp_id,
          ← Category.assoc, h, Category.id_comp, sub_self, zero_comp]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      refine biprod.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst, kernel.condition]
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine (cancel_mono (kernel.ι π)).1 ?_
        rw [Category.assoc, kernel.lift_ι, Preadditive.comp_sub, Category.comp_id,
          ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.id_comp]

@[simp]
theorem biprodIsoOfSplitEpi_hom_comp_fst : (biprodIsoOfSplitEpi π σ h).hom ≫ biprod.fst = π :=
  biprod.lift_fst _ _

end SplitEpi

/-! ### The product with any pointed space -/

variable (F : TopCat.{0}) {S : Type} [TopologicalSpace S] (s : S) (k : ℕ)

/-- The homology of a product splits off the homology of the base, along the projection: the
remaining summand is the kernel of the projection. -/
def hgrpProdSplitIso :
    Hgrp k (TopCat.of (↥F × S)) ≅ Hgrp k F ⊞ kernel (HgrpMap k (prodFstMap F S)) :=
  biprodIsoOfSplitEpi (HgrpMap k (prodFstMap F S)) (HgrpMap k (prodSectMap F s))
    (by rw [← HgrpMap_comp, prodSectMap_comp_prodFstMap, HgrpMap_id])

@[simp]
theorem hgrpProdSplitIso_hom_comp_fst :
    (hgrpProdSplitIso F s k).hom ≫ biprod.fst = HgrpMap k (prodFstMap F S) :=
  biprodIsoOfSplitEpi_hom_comp_fst _ _ _

end Submission
