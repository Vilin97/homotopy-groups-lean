/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Submission.Hurewicz.SimplexHEP
import Submission.Model.Sphere

/-!
# Realization of the standard simplicial boundary

This file constructs the canonical continuous map from geometric realization of the standard
simplicial boundary `SSet.boundary n` to the ordinary boundary of the topological standard
simplex.  A boundary simplex is a nonsurjective monotone vertex map; its affine realization has a
vanishing target coordinate and therefore lands in `Submission.bdry n`.  These restricted affine
maps are natural in the simplex degree and hence define a simplicial map into the singular complex
of `bdry n`.  The realization/singular adjunction supplies the desired continuous map.

Composing with the maintained simplex-boundary/disk-boundary homeomorphism gives a continuous map
from realization of `∂Δ[n+1]` to the exact metric `n`-sphere used by the homotopy-group library.
No injectivity, surjectivity, or homeomorphism claim about this realization map is made here.

## Main definitions

* `Submission.boundaryTopologicalSimplexMap`: the restricted affine map represented by one
  boundary simplex;
* `Submission.boundaryToSingularBdry`: the resulting map to the singular simplicial set;
* `Submission.boundaryRealizationToBdry`: its adjoint continuous realization map;
* `Submission.boundaryRealizationToSphere`: the comparison with the exact metric sphere.
-/

noncomputable section

namespace Submission

open CategoryTheory Simplicial Opposite

/-- The affine simplex represented by a simplex in `∂Δ[n]`, with codomain restricted to the
ordinary boundary of the topological standard simplex. -/
noncomputable def boundaryTopologicalSimplexMap {n : ℕ} {Δ : SimplexCategoryᵒᵖ}
    (s : (SSet.boundary n : SSet).obj Δ) :
    C(stdSimplex ℝ (Fin (Δ.unop.len + 1)), bdry n) where
  toFun x := ⟨stdSimplex.map (SSet.stdSimplex.objEquiv s.1).toOrderHom x, by
    have hs : ¬Function.Surjective (SSet.stdSimplex.asOrderHom s.1) := s.2
    have hrange : Set.range (SSet.stdSimplex.asOrderHom s.1) ≠ Set.univ := by
      intro hrange
      apply hs
      intro j
      have hjmem : j ∈ Set.range (SSet.stdSimplex.asOrderHom s.1) := by
        rw [hrange]
        exact Set.mem_univ j
      exact hjmem
    rcases (Set.ne_univ_iff_exists_notMem _).mp hrange with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (FunOnFinite.linearMap ℝ ℝ
      (SSet.stdSimplex.objEquiv s.1).toOrderHom x) j = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_filter] at hi
    exact False.elim (hj ⟨i, hi.2⟩)⟩
  continuous_toFun := Continuous.subtype_mk (stdSimplex.continuous_map _) _

/-- Restricting a boundary simplex and then realizing it affinely agrees with precomposition by
the corresponding affine map of topological simplices. -/
theorem boundaryTopologicalSimplexMap_naturality {n : ℕ}
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (s : (SSet.boundary n : SSet).obj Δ) :
    boundaryTopologicalSimplexMap ((SSet.boundary n : SSet).map f s) =
      (boundaryTopologicalSimplexMap s).comp
        ⟨stdSimplex.map f.unop.toOrderHom, stdSimplex.continuous_map _⟩ := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change stdSimplex.map _ x = stdSimplex.map _ (stdSimplex.map _ x)
  rw [stdSimplex.map_comp_apply]
  rfl

/-- The degreewise map sending a boundary simplex to its restricted affine singular simplex. -/
noncomputable def boundaryToSingularBdryApp (n : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (SSet.boundary n : SSet).obj Δ ⟶
      (TopCat.toSSet.obj (TopCat.of (bdry n))).obj Δ :=
  ↾fun s ↦ (TopCat.toSSetObjEquiv _ _).symm (boundaryTopologicalSimplexMap s)

/-- Naturality of the degreewise restricted-affine-simplex map. -/
theorem boundaryToSingularBdryApp_naturality (n : ℕ)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (SSet.boundary n : SSet).map f ≫ boundaryToSingularBdryApp n Δ' =
      boundaryToSingularBdryApp n Δ ≫
        (TopCat.toSSet.obj (TopCat.of (bdry n))).map f := by
  ext s
  apply (TopCat.toSSetObjEquiv _ _).injective
  change boundaryTopologicalSimplexMap ((SSet.boundary n : SSet).map f s) =
    (boundaryTopologicalSimplexMap s).comp
      ⟨stdSimplex.map f.unop.toOrderHom, stdSimplex.continuous_map _⟩
  exact boundaryTopologicalSimplexMap_naturality f s

/-- Boundary simplices define singular simplices in the ordinary topological boundary. -/
noncomputable def boundaryToSingularBdry (n : ℕ) :
    (SSet.boundary n : SSet) ⟶ TopCat.toSSet.obj (TopCat.of (bdry n)) where
  app := boundaryToSingularBdryApp n
  naturality _ _ f := boundaryToSingularBdryApp_naturality n f

/-- The canonical map from realization of the standard simplicial boundary to the ordinary
boundary of the topological standard simplex. -/
noncomputable def boundaryRealizationToBdry (n : ℕ) :
    SSet.toTop.obj (SSet.boundary n : SSet) ⟶ TopCat.of (bdry n) :=
  (sSetTopAdj.homEquiv _ _).symm (boundaryToSingularBdry n)

/-- The canonical continuous map from realization of the standard simplicial `n`-sphere to the
exact metric `n`-sphere. -/
noncomputable def boundaryRealizationToSphere (n : ℕ) :
    SSet.toTop.obj (SSet.boundary (n + 1) : SSet) ⟶
      TopCat.of (SphereSpace n) :=
  boundaryRealizationToBdry (n + 1) ≫
    TopCat.ofHom (bdryHomeoDiskBoundary (n + 1) :
      C(bdry (n + 1), TopCat.diskBoundary.{0} (n + 1))) ≫
    TopCat.ofHom (⟨fun x ↦ x.down, continuous_uliftDown⟩ :
      C(TopCat.diskBoundary.{0} (n + 1), SphereSpace n))

end Submission
