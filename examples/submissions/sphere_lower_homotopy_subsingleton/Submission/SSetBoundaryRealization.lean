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
The map to the ordinary simplex boundary is surjective: every boundary point lies on a face, and
the corresponding realized simplicial face supplies an explicit preimage.  No injectivity or
homeomorphism claim about this realization map is made here.

## Main definitions

* `Submission.boundaryTopologicalSimplexMap`: the restricted affine map represented by one
  boundary simplex;
* `Submission.boundaryToSingularBdry`: the resulting map to the singular simplicial set;
* `Submission.boundaryRealizationToBdry`: its adjoint continuous realization map;
* `Submission.boundaryRealizationToBdry_surjective`: surjectivity onto the ordinary simplex
  boundary;
* `Submission.boundaryRealizationToSphere`: the comparison with the exact metric sphere.
* `Submission.boundaryRealizationToSphere_surjective`: surjectivity of that comparison.
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

/-- The continuous realization of the `i`-th simplicial face, with codomain restricted to the
ordinary boundary of the topological standard simplex. -/
noncomputable def topologicalBoundaryFace {n : ℕ} (i : Fin (n + 2)) :
    SSet.toTop.obj (Δ[n] : SSet) ⟶ TopCat.of (bdry (n + 1)) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨faceMap i (SimplexCategory.toTopHomeo (SimplexCategory.mk n) x),
        faceMap_mem_bdry i _⟩,
      Continuous.subtype_mk
        ((continuous_faceMap i).comp
          (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous) _⟩

set_option backward.isDefEq.respectTransparency false in
/-- Under the singular-simplex equivalence, the adjunction unit's canonical top simplex is the
inverse of the standard-simplex realization homeomorphism. -/
lemma toSSetObjEquiv_yonedaEquiv_unit_stdSimplex {n : ℕ} :
    (TopCat.toSSetObjEquiv
      (SSet.toTop.obj (Δ[n] : SSet)) (op (SimplexCategory.mk n)))
        (SSet.yonedaEquiv (sSetTopAdj.unit.app (Δ[n] : SSet))) =
      ⟨(SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm,
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.continuous⟩ := by
  apply ContinuousMap.ext
  intro x
  change (SSet.yonedaEquiv (sSetTopAdj.unit.app (Δ[n] : SSet))).down.hom (ULift.up x) = _
  change (((sSetTopAdj.unit.app (Δ[n] : SSet)).app _
    (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet)))).down).hom (ULift.up x) = _
  rw [sSetTopAdj_unit_app_app_down]
  have hy : SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet))) = 𝟙 (Δ[n] : SSet) :=
    Equiv.symm_apply_apply _ _
  have hcomp : SSet.toTopSimplex.inv.app (SimplexCategory.mk n) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet)))) =
      SSet.toTopSimplex.inv.app (SimplexCategory.mk n) := by
    rw [hy, (SSet.toTop).map_id]
    exact Category.comp_id _
  calc
    _ = (SSet.toTopSimplex.inv.app (SimplexCategory.mk n)).hom (ULift.up x) := by
      convert ConcreteCategory.congr_hom hcomp (ULift.up x) using 1 <;> rfl
    _ = _ := rfl

/-- Restricting `boundaryRealizationToBdry` to a realized simplicial face gives the corresponding
affine face map into the ordinary simplex boundary. -/
lemma boundaryRealizationToBdry_comp_boundaryι {n : ℕ} (i : Fin (n + 2)) :
    SSet.toTop.map (SSet.boundary.ι.{0} i) ≫ boundaryRealizationToBdry (n + 1) =
      topologicalBoundaryFace i := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [show (sSetTopAdj.homEquiv _ _) (boundaryRealizationToBdry (n + 1)) =
      boundaryToSingularBdry (n + 1) by
    exact Equiv.apply_symm_apply _ _]
  rw [Adjunction.homEquiv_unit]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  apply (TopCat.toSSetObjEquiv _ _).injective
  change boundaryTopologicalSimplexMap.{0}
      (SSet.yonedaEquiv (SSet.boundary.ι.{0} i)) =
    (topologicalBoundaryFace i).hom.comp
      ((TopCat.toSSetObjEquiv
        (SSet.toTop.obj (Δ[n] : SSet)) (op (SimplexCategory.mk n)))
          (SSet.yonedaEquiv (sSetTopAdj.unit.app (Δ[n] : SSet))))
  rw [toSSetObjEquiv_yonedaEquiv_unit_stdSimplex]
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change stdSimplex.map
      (SSet.stdSimplex.objEquiv
        (SSet.yonedaEquiv (SSet.boundary.ι.{0} i)).1).toOrderHom x =
    faceMap i ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm x))
  rw [Homeomorph.apply_symm_apply]
  have hs : SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv (SSet.boundary.ι.{0} i)).1 = SimplexCategory.δ i := by
    change SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv
        (SSet.boundary.ι.{0} i ≫ (SSet.boundary (n + 1)).ι)) = SimplexCategory.δ i
    rw [SSet.boundary.ι_ι]
    change SSet.stdSimplex.objEquiv.{0}
      (SSet.yonedaEquiv (SSet.stdSimplex.{0}.map (SimplexCategory.δ i))) =
        SimplexCategory.δ i
    rw [SSet.yonedaEquiv_map, Equiv.apply_symm_apply]
  rw [hs]
  classical
  refine Subtype.ext (funext fun k => ?_)
  have hδ : ⇑(SimplexCategory.δ (n := n) i).toOrderHom = i.succAbove := rfl
  have hmap : (stdSimplex.map (SimplexCategory.δ (n := n) i).toOrderHom x).1 =
      FunOnFinite.linearMap ℝ ℝ (SimplexCategory.δ (n := n) i).toOrderHom x.1 := rfl
  rw [hmap, FunOnFinite.linearMap_apply_apply]
  refine Fin.succAboveCases i ?_ (fun m => ?_) k
  · rw [faceMap_coe_same]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_filter, hδ] at hm
    exact absurd hm.2 (Fin.succAbove_ne i m)
  · rw [faceMap_coe_succAbove, Finset.sum_filter, Finset.sum_eq_single m]
    · rw [hδ, if_pos rfl]
    · intro q _ hq
      rw [hδ, if_neg]
      exact fun h => hq (Fin.succAbove_right_injective (p := i) h)
    · intro h
      exact absurd (Finset.mem_univ m) h

/-- The canonical map from realization of `∂Δ[n+1]` onto the ordinary boundary of the
topological `(n+1)`-simplex is surjective. -/
theorem boundaryRealizationToBdry_surjective (n : ℕ) :
    Function.Surjective (boundaryRealizationToBdry (n + 1)) := by
  intro b
  let i : Fin (n + 2) := bdryIdx b
  let y : stdSimplex ℝ (Fin (n + 1)) := dropMap i (bdryIdx_spec b)
  let z : SSet.toTop.obj (Δ[n] : SSet) :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y
  refine ⟨SSet.toTop.map (SSet.boundary.ι.{0} i) z, ?_⟩
  calc
    boundaryRealizationToBdry (n + 1)
        (SSet.toTop.map (SSet.boundary.ι.{0} i) z) =
      topologicalBoundaryFace i z := by
        exact ConcreteCategory.congr_hom
          (boundaryRealizationToBdry_comp_boundaryι i) z
    _ = b := by
      apply Subtype.ext
      change faceMap i
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) z) = b.1
      dsimp [z]
      rw [Homeomorph.apply_symm_apply]
      exact faceMap_dropMap i (bdryIdx_spec b)

/-- The canonical comparison from realization of the standard simplicial `n`-sphere onto the
exact metric `n`-sphere is surjective. -/
theorem boundaryRealizationToSphere_surjective (n : ℕ) :
    Function.Surjective (boundaryRealizationToSphere n) := by
  intro s
  let u : TopCat.diskBoundary.{0} (n + 1) := ULift.up s
  let b : bdry (n + 1) := (bdryHomeoDiskBoundary (n + 1)).symm u
  obtain ⟨x, hx⟩ := boundaryRealizationToBdry_surjective n b
  refine ⟨x, ?_⟩
  change ((bdryHomeoDiskBoundary (n + 1))
    (boundaryRealizationToBdry (n + 1) x)).down = s
  rw [hx]
  dsimp [b, u]
  rw [Homeomorph.apply_symm_apply]

end Submission
