/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.RelativeAdditivity
import Submission.Hurewicz.SimplexCubeOrientation

/-!
# Surjectivity of the first relative Hurewicz homomorphism

The normalization deformation expresses every first-nonvanishing relative homology class of a
point pair as an integral linear combination of canonical relative Hurewicz values.  Additivity
of the relative Hurewicz comparison makes its range an additive subgroup, so the whole linear
combination remains in that range.
-/

open CategoryTheory AlgebraicTopology Simplicial Opposite
open scoped Topology

noncomputable section

namespace Submission

namespace IsNConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X]

/-- Lift the normalized relative-Hurewicz chain into the range of the relative Hurewicz
homomorphism. -/
noncomputable def normalizedRelativeHurewiczRangeChain
    (hX : IsNConnected (n + 1) X) (x : X) :
    (CsingSSet (Sng (TopCat.of X))).X (n + 2) ⟶
      AddCommGrpCat.of
        (relativeHurewiczAdd n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))).range :=
  ccDesc fun s ↦ intHom ⟨
    relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
      (⟦(hX.normalizeTopSimplex x s).toRelGenLoop⟧ :
        π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩),
    ⟨Additive.ofMul
      (⟦(hX.normalizeTopSimplex x s).toRelGenLoop⟧ :
        π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩), rfl⟩⟩

@[simp]
theorem normalizedRelativeHurewiczRangeChain_gen
    (hX : IsNConnected (n + 1) X) (x : X)
    (s : Sng (TopCat.of X) _⦋n + 2⦌) :
    (hX.normalizedRelativeHurewiczRangeChain x (gen s) :
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X)) =
      relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        (⟦(hX.normalizeTopSimplex x s).toRelGenLoop⟧ :
          π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩) := by
  rw [normalizedRelativeHurewiczRangeChain, ccDesc_gen, intHom_one]

/-- Forgetting the range lift recovers the normalized relative-Hurewicz chain. -/
theorem normalizedRelativeHurewiczRangeChain_comp_subtype
    (hX : IsNConnected (n + 1) X) (x : X) :
    hX.normalizedRelativeHurewiczRangeChain x ≫
        AddCommGrpCat.ofHom
          (relativeHurewiczAdd n ({x} : Set X)
            (⟨x, rfl⟩ : ({x} : Set X))).range.subtype =
      hX.normalizedRelativeHurewiczChain x := by
  refine chainComplexX_hom_ext fun s ↦ ?_
  rw [ConcreteCategory.comp_apply]
  change (hX.normalizedRelativeHurewiczRangeChain x (gen s) :
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X)) =
    hX.normalizedRelativeHurewiczChain x (gen s)
  rw [normalizedRelativeHurewiczRangeChain_gen,
    normalizedRelativeHurewiczChain_gen]

/-- For an `(n+1)`-connected space, the additive relative Hurewicz homomorphism of the point
pair is surjective in degree `n+2`. -/
theorem relativeHurewiczAdd_surjective
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Surjective
      (relativeHurewiczAdd n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))) := by
  intro z
  obtain ⟨c, hc⟩ := hX.surjective_normalizedRelativeHurewiczChain x z
  let r := hX.normalizedRelativeHurewiczRangeChain x c
  have hr := ConcreteCategory.congr_hom
    (hX.normalizedRelativeHurewiczRangeChain_comp_subtype x) c
  rw [ConcreteCategory.comp_apply] at hr
  have hrz : (r : HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X)) = z := by
    rw [← hc]
    exact hr
  obtain ⟨y, hy⟩ := r.property
  exact ⟨y, hy.trans hrz⟩

/-- **Surjectivity in the first relative Hurewicz degree for a point pair.** -/
theorem relativeHurewicz_surjective
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Surjective
      (relativeHurewicz n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))) := by
  intro z
  obtain ⟨y, hy⟩ := hX.relativeHurewiczAdd_surjective x z
  exact ⟨y.toMul, hy⟩

end IsNConnected

end Submission
