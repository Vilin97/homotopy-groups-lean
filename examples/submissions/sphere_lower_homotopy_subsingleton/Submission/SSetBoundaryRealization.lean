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
Conversely, the realized face inclusions agree on intersections and therefore glue to a continuous
map from the ordinary boundary back to the realization.  The face formulas and the simplicial
boundary extensionality theorem prove that these maps are mutually inverse.  Thus realization of
the standard simplicial `n`-sphere is homeomorphic to the exact metric `n`-sphere.

## Main definitions

* `Submission.boundaryTopologicalSimplexMap`: the restricted affine map represented by one
  boundary simplex;
* `Submission.boundaryToSingularBdry`: the resulting map to the singular simplicial set;
* `Submission.boundaryRealizationToBdry`: its adjoint continuous realization map;
* `Submission.boundaryRealizationToBdry_surjective`: surjectivity onto the ordinary simplex
  boundary;
* `Submission.boundaryRealizationToSphere`: the comparison with the exact metric sphere.
* `Submission.boundaryRealizationToSphere_surjective`: surjectivity of that comparison.
* `Submission.boundaryRealizationHomeomorphBdry`: the homeomorphism with the ordinary simplex
  boundary;
* `Submission.boundaryRealizationHomeomorphSphere`: the homeomorphism with the exact metric sphere.
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

/-- The affine map induced by a simplex-category face is the corresponding coordinate face map. -/
lemma stdSimplexMap_delta_eq_faceMap {j : ℕ} (i : Fin (j + 2))
    (x : stdSimplex ℝ (Fin (j + 1))) :
    stdSimplex.map (⇑(SimplexCategory.δ (n := j) i)) x = faceMap i x := by
  classical
  refine Subtype.ext (funext fun k => ?_)
  have hδ : ⇑(SimplexCategory.δ (n := j) i) = i.succAbove := rfl
  have hmap : (stdSimplex.map (⇑(SimplexCategory.δ (n := j) i)) x).1 =
      FunOnFinite.linearMap ℝ ℝ (⇑(SimplexCategory.δ (n := j) i)) x.1 := rfl
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

lemma boundaryVal_succAbove_eq {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    ((p.succAbove k : Fin (n + 1)) : ℕ) =
      if (k : ℕ) < (p : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  rcases lt_or_ge k.castSucc p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, if_pos]
    · rfl
    · simpa [Fin.lt_def] using h
  · rw [Fin.succAbove_of_le_castSucc _ _ h, if_neg]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc] at h
      omega

/-- The coordinate face maps satisfy the first cosimplicial identity. -/
lemma boundaryFaceMap_faceMap {j : ℕ} {i₀ j₀ : Fin (j + 2)} (h : i₀ ≤ j₀)
    (w : stdSimplex ℝ (Fin (j + 1))) :
    faceMap j₀.succ (faceMap i₀ w) = faceMap i₀.castSucc (faceMap j₀ w) := by
  rw [← stdSimplexMap_delta_eq_faceMap, ← stdSimplexMap_delta_eq_faceMap,
    ← stdSimplexMap_delta_eq_faceMap, ← stdSimplexMap_delta_eq_faceMap,
    stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext m
  refine Fin.val_injective ?_
  simp only [Function.comp_apply, SimplexCategory.coe_δ, boundaryVal_succAbove_eq,
    Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- Two distinct coordinate-face presentations of one boundary point factor through their common
codimension-two face. -/
lemma boundaryFaces_exists_commonFactor {j : ℕ} {i k : Fin (j + 3)} (hik : i < k)
    {y z : stdSimplex ℝ (Fin (j + 2))} (h : faceMap i y = faceMap k z) :
    ∃ w : stdSimplex ℝ (Fin (j + 1)),
      y = faceMap (k.pred (Fin.ne_zero_of_lt hik)) w ∧
        z = faceMap (i.castPred (Fin.ne_last_of_lt hik)) w := by
  set j₀ := k.pred (Fin.ne_zero_of_lt hik) with hj₀
  set i₀ := i.castPred (Fin.ne_last_of_lt hik) with hi₀
  have hsucc : j₀.succ = k := Fin.succ_pred _ _
  have hcast : i₀.castSucc = i := Fin.castSucc_castPred _ _
  have hle : i₀ ≤ j₀ := by
    have h1 : (i₀ : ℕ) = (i : ℕ) := rfl
    have h2 : (j₀ : ℕ) = (k : ℕ) - 1 := rfl
    have h3 : (i : ℕ) < (k : ℕ) := hik
    rw [Fin.le_def, h1, h2]
    omega
  have hky : y.1 j₀ = 0 := by
    have hik' : i.succAbove j₀ = k := Fin.succAbove_pred_of_lt i k hik
    have e1 : (faceMap i y).1 (i.succAbove j₀) = y.1 j₀ :=
      faceMap_coe_succAbove i y j₀
    rw [hik', h, faceMap_coe_same] at e1
    exact e1.symm
  refine ⟨dropMap j₀ hky, (faceMap_dropMap j₀ hky).symm, ?_⟩
  refine (faceMap_injective k ?_).symm
  calc
    faceMap k (faceMap i₀ (dropMap j₀ hky)) =
        faceMap j₀.succ (faceMap i₀ (dropMap j₀ hky)) := by rw [hsucc]
    _ = faceMap i₀.castSucc (faceMap j₀ (dropMap j₀ hky)) :=
      boundaryFaceMap_faceMap hle _
    _ = faceMap i y := by rw [hcast, faceMap_dropMap]
    _ = faceMap k z := h

lemma boundaryFaces_disjoint_zeroDim {i k : Fin 2} (hik : i ≠ k)
    (y z : stdSimplex ℝ (Fin 1)) : faceMap i y ≠ faceMap k z := by
  intro h
  have h1 : (faceMap i y).1 i = 0 := faceMap_coe_same i y
  have h2 : (faceMap i y).1 k = 0 := by rw [h]; exact faceMap_coe_same k z
  have hs : (faceMap i y).1 0 + (faceMap i y).1 1 = 1 := by
    have hsum := (faceMap i y).2.2
    rwa [Fin.sum_univ_two] at hsum
  clear h
  fin_cases i <;> fin_cases k <;> simp_all

lemma boundaryPoint_existsFace {j : ℕ} (b : bdry (j + 1)) :
    ∃ (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))),
      (⟨faceMap i y, faceMap_mem_bdry i y⟩ : bdry (j + 1)) = b :=
  ⟨bdryIdx b, dropMap _ (bdryIdx_spec b),
    Subtype.ext (faceMap_dropMap _ (bdryIdx_spec b))⟩

/-- A topological face maps back into the realization by the corresponding realized simplicial
face inclusion. -/
noncomputable def boundaryFaceToRealization {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), SSet.toTop.obj (SSet.boundary (n + 1) : SSet)) :=
  ⟨fun y ↦ SSet.toTop.map (SSet.boundary.ι.{0} i)
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y),
    (SSet.toTop.map (SSet.boundary.ι.{0} i)).hom.continuous.comp
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.continuous⟩

lemma boundaryFaceToRealization_eq_of_lt {n : ℕ} {i k : Fin (n + 2)} (hik : i < k)
    {y z : stdSimplex ℝ (Fin (n + 1))} (h : faceMap i y = faceMap k z) :
    boundaryFaceToRealization i y = boundaryFaceToRealization k z := by
  obtain _ | n := n
  · exact False.elim (boundaryFaces_disjoint_zeroDim (ne_of_lt hik) y z h)
  · obtain ⟨w, rfl, rfl⟩ := boundaryFaces_exists_commonFactor hik h
    set j₀ := k.pred (Fin.ne_zero_of_lt hik) with hj₀
    set i₀ := i.castPred (Fin.ne_last_of_lt hik) with hi₀
    have hsucc : j₀.succ = k := Fin.succ_pred _ _
    have hcast : i₀.castSucc = i := Fin.castSucc_castPred _ _
    have hle : i₀ ≤ j₀ := by
      have h1 : (i₀ : ℕ) = (i : ℕ) := rfl
      have h2 : (j₀ : ℕ) = (k : ℕ) - 1 := rfl
      have h3 : (i : ℕ) < (k : ℕ) := hik
      rw [Fin.le_def, h1, h2]
      omega
    have hmaps :
        SSet.stdSimplex.δ j₀ ≫ SSet.boundary.ι.{0} i =
          SSet.stdSimplex.δ i₀ ≫ SSet.boundary.ι.{0} k := by
      rw [← cancel_mono (SSet.boundary (n + 2)).ι]
      simp only [Category.assoc, SSet.boundary.ι_ι]
      rw [← hcast, ← hsucc]
      exact (SSet.stdSimplex.δ_comp_δ hle).symm
    have hmaps' :
        SSet.stdSimplex.{0}.map (SimplexCategory.δ j₀) ≫
            SSet.boundary.ι.{0} i =
          SSet.stdSimplex.{0}.map (SimplexCategory.δ i₀) ≫
            SSet.boundary.ι.{0} k := hmaps
    change SSet.toTop.map (SSet.boundary.ι.{0} i)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
          (faceMap j₀ w)) =
      SSet.toTop.map (SSet.boundary.ι.{0} k)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm
          (faceMap i₀ w))
    rw [← stdSimplexMap_delta_eq_faceMap, ← stdSimplexMap_delta_eq_faceMap,
      SimplexCategory.toTopHomeo_symm_naturality_apply,
      SimplexCategory.toTopHomeo_symm_naturality_apply]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← (SSet.toTop).map_comp, ← (SSet.toTop).map_comp, hmaps']

/-- The maps from the topological faces back into the realization agree on every intersection. -/
lemma boundaryFaceToRealization_compatible {n : ℕ} (i k : Fin (n + 2))
    (y z : stdSimplex ℝ (Fin (n + 1))) (h : faceMap i y = faceMap k z) :
    boundaryFaceToRealization i y = boundaryFaceToRealization k z := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact boundaryFaceToRealization_eq_of_lt hik h
  · exact congrArg (boundaryFaceToRealization i) (faceMap_injective i h)
  · exact (boundaryFaceToRealization_eq_of_lt hki h.symm).symm

/-- The continuous inverse candidate obtained by gluing the realized face inclusions over the
ordinary simplex boundary. -/
noncomputable def boundaryRealizationFromBdry (n : ℕ) :
    TopCat.of (bdry (n + 1)) ⟶
      SSet.toTop.obj (SSet.boundary (n + 1) : SSet) :=
  TopCat.ofHom (glueFaces (fun i ↦ boundaryFaceToRealization i)
    boundaryFaceToRealization_compatible)

@[simp]
theorem boundaryRealizationFromBdry_faceMap {n : ℕ} (i : Fin (n + 2))
    (y : stdSimplex ℝ (Fin (n + 1))) :
    boundaryRealizationFromBdry n ⟨faceMap i y, faceMap_mem_bdry i y⟩ =
      SSet.toTop.map (SSet.boundary.ι.{0} i)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := by
  exact glueFaces_faceMap (fun i ↦ boundaryFaceToRealization i)
    boundaryFaceToRealization_compatible i y

/-- Gluing the realized faces and then applying the affine boundary map is the identity. -/
theorem boundaryRealizationFromBdry_comp_toBdry (n : ℕ) :
    boundaryRealizationFromBdry n ≫ boundaryRealizationToBdry (n + 1) =
      𝟙 (TopCat.of (bdry (n + 1))) := by
  apply ConcreteCategory.hom_ext
  intro b
  obtain ⟨i, y, rfl⟩ := boundaryPoint_existsFace b
  rw [ConcreteCategory.comp_apply, boundaryRealizationFromBdry_faceMap]
  calc
    boundaryRealizationToBdry (n + 1)
        (SSet.toTop.map (SSet.boundary.ι.{0} i)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) =
      topologicalBoundaryFace i
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y) := by
          exact ConcreteCategory.congr_hom
            (boundaryRealizationToBdry_comp_boundaryι i) _
    _ = ⟨faceMap i y, faceMap_mem_bdry i y⟩ := by
      apply Subtype.ext
      change faceMap i
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm y)) = faceMap i y
      rw [Homeomorph.apply_symm_apply]
    _ = (𝟙 (TopCat.of (bdry (n + 1)))) ⟨faceMap i y, faceMap_mem_bdry i y⟩ := rfl

theorem topologicalBoundaryFace_comp_boundaryRealizationFromBdry {n : ℕ}
    (i : Fin (n + 2)) :
    topologicalBoundaryFace i ≫ boundaryRealizationFromBdry n =
      SSet.toTop.map (SSet.boundary.ι.{0} i) := by
  apply ConcreteCategory.hom_ext
  intro x
  change boundaryRealizationFromBdry n
      ⟨faceMap i (SimplexCategory.toTopHomeo (SimplexCategory.mk n) x),
        faceMap_mem_bdry i _⟩ = SSet.toTop.map (SSet.boundary.ι.{0} i) x
  rw [boundaryRealizationFromBdry_faceMap]
  rw [Homeomorph.symm_apply_apply]

/-- Maps out of the realized standard boundary are determined by their restrictions to the
realized codimension-one faces. -/
lemma boundaryRealization_hom_ext {n : ℕ} {X : TopCat.{0}}
    {f g : SSet.toTop.obj (SSet.boundary (n + 1) : SSet) ⟶ X}
    (h : ∀ i : Fin (n + 2),
      SSet.toTop.map (SSet.boundary.ι.{0} i) ≫ f =
        SSet.toTop.map (SSet.boundary.ι.{0} i) ≫ g) :
    f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply SSet.boundary.hom_ext
  intro i
  rw [← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left]
  exact congrArg (sSetTopAdj.homEquiv (Δ[n] : SSet) X) (h i)

/-- Applying the affine boundary map and then gluing the realized faces is the identity. -/
theorem boundaryRealizationToBdry_comp_fromBdry (n : ℕ) :
    boundaryRealizationToBdry (n + 1) ≫ boundaryRealizationFromBdry n =
      𝟙 (SSet.toTop.obj (SSet.boundary (n + 1) : SSet)) := by
  apply boundaryRealization_hom_ext
  intro i
  rw [← Category.assoc, boundaryRealizationToBdry_comp_boundaryι,
    topologicalBoundaryFace_comp_boundaryRealizationFromBdry, Category.comp_id]

/-- Geometric realization of the standard simplicial boundary is homeomorphic to the ordinary
boundary of the topological standard simplex. -/
noncomputable def boundaryRealizationHomeomorphBdry (n : ℕ) :
    SSet.toTop.obj (SSet.boundary (n + 1) : SSet) ≃ₜ bdry (n + 1) where
  toFun := boundaryRealizationToBdry (n + 1)
  invFun := boundaryRealizationFromBdry n
  left_inv x := by
    have h := ConcreteCategory.congr_hom
      (boundaryRealizationToBdry_comp_fromBdry n) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  right_inv x := by
    have h := ConcreteCategory.congr_hom
      (boundaryRealizationFromBdry_comp_toBdry n) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  continuous_toFun := (boundaryRealizationToBdry (n + 1)).hom.continuous
  continuous_invFun := (boundaryRealizationFromBdry n).hom.continuous

/-- Geometric realization of the standard simplicial `n`-sphere is homeomorphic to the exact
metric `n`-sphere. -/
noncomputable def boundaryRealizationHomeomorphSphere (n : ℕ) :
    SSet.toTop.obj (SSet.boundary (n + 1) : SSet) ≃ₜ SphereSpace n :=
  (boundaryRealizationHomeomorphBdry n).trans
    ((bdryHomeoDiskBoundary (n + 1)).trans Homeomorph.ulift)

@[simp]
theorem boundaryRealizationHomeomorphSphere_apply (n : ℕ)
    (x : SSet.toTop.obj (SSet.boundary (n + 1) : SSet)) :
    boundaryRealizationHomeomorphSphere n x = boundaryRealizationToSphere n x := by
  rfl

end Submission
