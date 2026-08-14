/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.FiniteOrderedComplexCarrierRealization

/-!
# Affine realization of finite ordered simplicial complexes

This file completes the comparison between an arbitrary finite ordered simplicial complex and the
union of its affine faces.  The inverse is constructed facetwise and glued over the finite closed
cover by nonempty facets.  On an overlap, the two local inverses factor through the canonical
simplex of the facet intersection, so the cosimplicial realization identities identify them.

The resulting homeomorphism is canonical in the forward direction and has exact formulas on every
listed facet.

## Main results

* `facetRealizationPoint_eq`: realized facet points with the same ambient barycentric coordinates
  agree;
* `orderedRealizationFromFacetFamilyCarrier`: the continuous inverse obtained by finite gluing;
* `orderedRealizationHomeomorphFacetFamilyCarrier`: the realization/carrier homeomorphism for any
  finite ordered complex.
-/

noncomputable section

open CategoryTheory Simplicial Opposite

namespace Submission.FiniteOrderedComplex

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Mapping barycentric coordinates along an injective map of finite vertex types is injective. -/
theorem stdSimplex_map_injective_of_injective
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := ℝ) f) := by
  classical
  intro x y h
  apply stdSimplex.ext
  funext i
  have hi := congrArg (fun z : stdSimplex ℝ Y ↦ z (f i)) h
  change (FunOnFinite.linearMap ℝ ℝ f x) (f i) =
    (FunOnFinite.linearMap ℝ ℝ f y) (f i) at hi
  rw [FunOnFinite.linearMap_apply_apply, FunOnFinite.linearMap_apply_apply] at hi
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i] at hi
  · exact hi
  · intro j hj hji
    rw [Finset.mem_filter] at hj
    exact False.elim (hji (hf hj.2))
  · intro hi'
    exact False.elim (hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
  · intro j hj hji
    rw [Finset.mem_filter] at hj
    exact False.elim (hji (hf hj.2))
  · intro hi'
    exact False.elim (hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))

/-- A barycentric coordinate outside the range of a vertex map vanishes after mapping. -/
theorem stdSimplex_map_eq_zero_of_not_mem_range
    {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y) (x : stdSimplex ℝ X) (y : Y)
    (hy : y ∉ Set.range f) :
    stdSimplex.map f x y = 0 := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ f x) y = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  exact False.elim (hy ⟨i, hi.2⟩)

/-- The canonical ordered simplex associated to any finite face of the complex. -/
def faceCanonicalSimplex {d : ℕ} (facets : Finset (Finset V))
    (face : Finset V) (hface : IsFace facets face)
    (hcard : face.card = d + 1) : (orderedSSet facets) _⦋d⦌ :=
  canonicalSimplex face hcard hface

/-- The Yoneda simplex map selecting any finite face of the ordered complex. -/
def faceSSetι {d : ℕ} (facets : Finset (Finset V))
    (face : Finset V) (hface : IsFace facets face)
    (hcard : face.card = d + 1) :
    (Δ[d] : SSet) ⟶ orderedSSet facets :=
  SSet.yonedaEquiv.symm (faceCanonicalSimplex facets face hface hcard)

/-- The monotone index map exhibiting one finite face as a face of a containing facet. -/
def faceToFacetIndexHom {c d : ℕ}
    (face facet : Finset V) (hsubset : face ⊆ facet)
    (hfacecard : face.card = c + 1) (hfacetcard : facet.card = d + 1) :
    (⦋c⦌ : SimplexCategory) ⟶ ⦋d⦌ :=
  simplexIndexHom facet hfacetcard (ambientCanonicalSimplex face hfacecard)
    (fun i ↦ hsubset (face.orderEmbOfFin_mem hfacecard i))

omit [Fintype V] in
/-- The face-to-facet index map commutes with the increasing vertex enumerations. -/
theorem faceToFacetIndexHom_orderEmb {c d : ℕ}
    (face facet : Finset V) (hsubset : face ⊆ facet)
    (hfacecard : face.card = c + 1) (hfacetcard : facet.card = d + 1)
    (i : Fin (c + 1)) :
    facet.orderEmbOfFin hfacetcard
        ((faceToFacetIndexHom face facet hsubset hfacecard hfacetcard).toOrderHom i) =
      face.orderEmbOfFin hfacecard i := by
  change facet.orderEmbOfFin hfacetcard
      ((facet.orderIsoOfFin hfacetcard).symm
        ⟨face.orderEmbOfFin hfacecard i,
          hsubset (face.orderEmbOfFin_mem hfacecard i)⟩) = _
  exact congrArg Subtype.val ((facet.orderIsoOfFin hfacetcard).apply_symm_apply _)

omit [Fintype V] in
/-- The canonical simplex of a face factors through the canonical simplex of every containing
listed facet. -/
theorem faceSSetι_factor_through_facet {c d : ℕ}
    (facets : Finset (Finset V))
    (face facet : Finset V) (hfacet : facet ∈ facets) (hsubset : face ⊆ facet)
    (hfacecard : face.card = c + 1) (hfacetcard : facet.card = d + 1) :
    SSet.stdSimplex.map
        (faceToFacetIndexHom face facet hsubset hfacecard hfacetcard) ≫
      facetSSetι facets facet hfacet hfacetcard =
        faceSSetι facets face ⟨facet, hfacet, hsubset⟩ hfacecard := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  apply Subtype.ext
  exact nerve_map_simplexIndexHom_ambientCanonicalSimplex
    facet hfacetcard (ambientCanonicalSimplex face hfacecard)
      (fun i ↦ hsubset (face.orderEmbOfFin_mem hfacecard i))

/-- Every ambient simplex point supported on a finite face has ordered barycentric coordinates on
that face. -/
theorem exists_stdSimplex_map_orderEmb_eq
    {d : ℕ} (face : Finset V) (hcard : face.card = d + 1)
    (x : stdSimplex ℝ V) (hx : ∀ v, v ∉ face → x v = 0) :
    ∃ y : stdSimplex ℝ (Fin (d + 1)),
      stdSimplex.map (face.orderEmbOfFin hcard) y = x := by
  let xf : simplexFaceCarrier face := ⟨x, hx⟩
  let z : stdSimplex ℝ face := simplexFaceRestriction face xf
  let e : Fin (d + 1) ≃ face := (face.orderIsoOfFin hcard).toEquiv
  let y : stdSimplex ℝ (Fin (d + 1)) := stdSimplex.map e.symm z
  refine ⟨y, ?_⟩
  rw [show y = stdSimplex.map e.symm z by rfl]
  rw [stdSimplex.map_comp_apply]
  have he : (face.orderEmbOfFin hcard) ∘ e.symm =
      (fun v : face ↦ v.1) := by
    funext v
    exact congrArg Subtype.val (e.apply_symm_apply v)
  rw [he]
  change (simplexFaceEmbedding face z).1 = x
  exact congrArg Subtype.val (simplexFaceEmbedding_restriction face xf)

/-- Points in two realized listed facets agree whenever their ambient barycentric coordinates
agree.  The proof factors both points through the canonical simplex of the facet intersection. -/
theorem facetRealizationPoint_eq
    {d e : ℕ} (facets : Finset (Finset V))
    (A B : Finset V) (hA : A ∈ facets) (hB : B ∈ facets)
    (hAcard : A.card = d + 1) (hBcard : B.card = e + 1)
    (y : stdSimplex ℝ (Fin (d + 1)))
    (z : stdSimplex ℝ (Fin (e + 1)))
    (h : stdSimplex.map (A.orderEmbOfFin hAcard) y =
      stdSimplex.map (B.orderEmbOfFin hBcard) z) :
    SSet.toTop.map (facetSSetι facets A hA hAcard)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk d)).symm y) =
      SSet.toTop.map (facetSSetι facets B hB hBcard)
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk e)).symm z) := by
  let x : stdSimplex ℝ V := stdSimplex.map (A.orderEmbOfFin hAcard) y
  have hxA : ∀ v, v ∉ A → x v = 0 := by
    intro v hv
    apply stdSimplex_map_eq_zero_of_not_mem_range
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hv
  have hxB : ∀ v, v ∉ B → x v = 0 := by
    intro v hv
    rw [show x = stdSimplex.map (B.orderEmbOfFin hBcard) z by exact h]
    apply stdSimplex_map_eq_zero_of_not_mem_range
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hv
  let C := A ∩ B
  have hxC : ∀ v, v ∉ C → x v = 0 := by
    intro v hv
    rw [Finset.mem_inter, not_and_or] at hv
    exact hv.elim (hxA v) (hxB v)
  have hC_nonempty : C.Nonempty := by
    by_contra hC
    rw [Finset.not_nonempty_iff_eq_empty] at hC
    have hzero : ∀ v, x v = 0 := by
      intro v
      exact hxC v (by simp [hC])
    have hsum : (∑ v, x v) = 0 := Finset.sum_eq_zero fun v _ ↦ hzero v
    have hone : (∑ v, x v) = 1 := x.2.2
    linarith
  let c := C.card - 1
  have hCcard : C.card = c + 1 := by
    dsimp [c]
    exact (Nat.sub_add_cancel (Finset.one_le_card.mpr hC_nonempty)).symm
  obtain ⟨w, hw⟩ := exists_stdSimplex_map_orderEmb_eq C hCcard x hxC
  have hCA : C ⊆ A := Finset.inter_subset_left
  have hCB : C ⊆ B := Finset.inter_subset_right
  let fA := faceToFacetIndexHom C A hCA hCcard hAcard
  let fB := faceToFacetIndexHom C B hCB hCcard hBcard
  have hy : y = stdSimplex.map fA.toOrderHom w := by
    apply stdSimplex_map_injective_of_injective
      (A.orderEmbOfFin hAcard) (A.orderEmbOfFin hAcard).injective
    rw [stdSimplex.map_comp_apply]
    change x = _
    rw [show (A.orderEmbOfFin hAcard) ∘ fA.toOrderHom =
        C.orderEmbOfFin hCcard by
      funext i
      exact faceToFacetIndexHom_orderEmb C A hCA hCcard hAcard i]
    exact hw.symm
  have hz : z = stdSimplex.map fB.toOrderHom w := by
    apply stdSimplex_map_injective_of_injective
      (B.orderEmbOfFin hBcard) (B.orderEmbOfFin hBcard).injective
    rw [stdSimplex.map_comp_apply]
    rw [← h]
    change x = _
    rw [show (B.orderEmbOfFin hBcard) ∘ fB.toOrderHom =
        C.orderEmbOfFin hCcard by
      funext i
      exact faceToFacetIndexHom_orderEmb C B hCB hCcard hBcard i]
    exact hw.symm
  rw [hy, hz]
  have hnatA :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk d)).symm
          (stdSimplex.map fA.toOrderHom w) =
        SSet.toTop.map (SSet.stdSimplex.map fA)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk c)).symm w) := by
    exact SimplexCategory.toTopHomeo_symm_naturality_apply.{0} fA w
  have hnatB :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk e)).symm
          (stdSimplex.map fB.toOrderHom w) =
        SSet.toTop.map (SSet.stdSimplex.map fB)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk c)).symm w) := by
    exact SimplexCategory.toTopHomeo_symm_naturality_apply.{0} fB w
  rw [hnatA, hnatB]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← (SSet.toTop).map_comp, ← (SSet.toTop).map_comp]
  rw [show SSet.stdSimplex.map fA ≫ facetSSetι facets A hA hAcard =
      faceSSetι facets C ⟨A, hA, hCA⟩ hCcard by
    exact faceSSetι_factor_through_facet facets C A hA hCA hCcard hAcard]
  rw [show SSet.stdSimplex.map fB ≫ facetSSetι facets B hB hBcard =
      faceSSetι facets C ⟨A, hA, hCA⟩ hCcard by
    exact faceSSetι_factor_through_facet facets C B hB hCB hCcard hBcard]

/-- Nonempty listed facets, used as the finite closed-cover index. -/
abbrev NonemptyFacetIndex (facets : Finset (Finset V)) :=
  {facet : Finset V // facet ∈ facets ∧ facet.Nonempty}

omit [LinearOrder V] in
/-- A finite face supporting a point of a nonempty standard simplex is nonempty. -/
theorem supported_facet_nonempty (facet : Finset V) (x : stdSimplex ℝ V)
    (hx : ∀ v, v ∉ facet → x v = 0) : facet.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst facet
  have hzero : ∀ v, x v = 0 := fun v ↦ hx v (by simp)
  have hsum : (∑ v, x v) = 0 := Finset.sum_eq_zero fun v _ ↦ hzero v
  have hone : (∑ v, x v) = 1 := x.2.2
  linarith

omit [LinearOrder V] in
/-- Every affine carrier point is supported on some nonempty listed facet. -/
theorem exists_nonemptyFacetIndex_support (facets : Finset (Finset V))
    (b : facetFamilyCarrier facets) :
    ∃ i : NonemptyFacetIndex facets, ∀ v, v ∉ i.1 → b.1 v = 0 := by
  obtain ⟨facet, hfacet, hx⟩ :=
    (mem_facetFamilyCarrier_iff facets b.1).mp b.2
  exact ⟨⟨facet, hfacet, supported_facet_nonempty facet b.1 hx⟩, hx⟩

/-- Choose a nonempty listed facet supporting a carrier point. -/
noncomputable def carrierFacetIndex (facets : Finset (Finset V))
    (b : facetFamilyCarrier facets) : NonemptyFacetIndex facets :=
  (exists_nonemptyFacetIndex_support facets b).choose

omit [LinearOrder V] in
/-- The chosen carrier facet supports the original ambient barycentric point. -/
theorem carrierFacetIndex_support (facets : Finset (Finset V))
    (b : facetFamilyCarrier facets) :
    ∀ v, v ∉ (carrierFacetIndex facets b).1 → b.1 v = 0 :=
  (exists_nonemptyFacetIndex_support facets b).choose_spec

section FacetFamilyGluing

variable (facets : Finset (Finset V))
  {Z : Type} [TopologicalSpace Z]
  (g : (i : NonemptyFacetIndex facets) → C(simplexFaceCarrier i.1, Z))
  (hg : ∀ (i k : NonemptyFacetIndex facets)
    (y : simplexFaceCarrier i.1) (z : simplexFaceCarrier k.1),
      y.1 = z.1 → g i y = g k z)

/-- The function obtained by choosing a supporting facet and applying its local map. -/
noncomputable def glueFacetFamilyFun (b : facetFamilyCarrier facets) : Z :=
  g (carrierFacetIndex facets b)
    ⟨b.1, carrierFacetIndex_support facets b⟩

include hg in
omit [LinearOrder V] in
/-- On any supporting facet, the glued function equals that facet's local map. -/
theorem glueFacetFamily_aux (b : facetFamilyCarrier facets)
    (i : NonemptyFacetIndex facets) (hi : ∀ v, v ∉ i.1 → b.1 v = 0) :
    glueFacetFamilyFun facets g b = g i ⟨b.1, hi⟩ :=
  hg _ _ _ _ rfl

include hg in
omit [LinearOrder V] in
/-- Compatible maps on the finite closed facet cover glue continuously. -/
theorem continuous_glueFacetFamilyFun :
    Continuous (glueFacetFamilyFun facets g) := by
  set S : NonemptyFacetIndex facets → Set (facetFamilyCarrier facets) :=
    fun i => {b | ∀ v, v ∉ i.1 → b.1 v = 0} with hS
  refine (locallyFinite_of_finite S).continuous ?_ (fun i => ?_) (fun i => ?_)
  · refine Set.eq_univ_of_forall fun b => ?_
    exact Set.mem_iUnion.2
      ⟨carrierFacetIndex facets b, carrierFacetIndex_support facets b⟩
  · change IsClosed ((fun x : facetFamilyCarrier facets => x.1) ⁻¹'
      simplexFaceCarrier i.1)
    exact (isClosed_simplexFaceCarrier i.1).preimage continuous_subtype_val
  · rw [continuousOn_iff_continuous_restrict]
    have heq : (S i).restrict (glueFacetFamilyFun facets g) =
        fun b : S i => g i ⟨b.1.1, b.2⟩ := by
      funext b
      exact glueFacetFamily_aux facets g hg b.1 i b.2
    rw [heq]
    exact (g i).continuous.comp
      (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _)

include hg in
/-- Glue a compatible family of continuous maps over all nonempty listed facets. -/
noncomputable def glueFacetFamily : C(facetFamilyCarrier facets, Z) :=
  ⟨glueFacetFamilyFun facets g, continuous_glueFacetFamilyFun facets g hg⟩

include hg in
omit [LinearOrder V] in
/-- The glued continuous map restricts to the supplied map on each affine face. -/
@[simp]
theorem glueFacetFamily_face
    (i : NonemptyFacetIndex facets) (y : simplexFaceCarrier i.1) :
    glueFacetFamily facets g hg ⟨y.1, by
      rw [mem_facetFamilyCarrier_iff]
      exact ⟨i.1, i.2.1, y.2⟩⟩ = g i y := by
  let b : facetFamilyCarrier facets := ⟨y.1, by
    rw [mem_facetFamilyCarrier_iff]
    exact ⟨i.1, i.2.1, y.2⟩⟩
  change glueFacetFamilyFun facets g b = g i y
  simpa only [b] using glueFacetFamily_aux facets g hg b i y.2

end FacetFamilyGluing

/-- The dimension of a nonempty listed facet. -/
def nonemptyFacetDim {facets : Finset (Finset V)}
    (i : NonemptyFacetIndex facets) : ℕ := i.1.card - 1

omit [Fintype V] [LinearOrder V] in
/-- A nonempty facet has one more vertex than its dimension. -/
theorem nonemptyFacet_card {facets : Finset (Finset V)}
    (i : NonemptyFacetIndex facets) :
    i.1.card = nonemptyFacetDim i + 1 :=
  (Nat.sub_add_cancel (Finset.one_le_card.mpr i.2.2)).symm

/-- Ordered barycentric coordinates on a nonempty affine face. -/
def nonemptyFacetCoordinates {facets : Finset (Finset V)}
    (i : NonemptyFacetIndex facets) :
    simplexFaceCarrier i.1 →
      stdSimplex ℝ (Fin (nonemptyFacetDim i + 1)) := fun x =>
  stdSimplex.map ((i.1.orderIsoOfFin (nonemptyFacet_card i)).toEquiv.symm)
    (simplexFaceRestriction i.1 x)

/-- Re-embedding the ordered coordinates of a face point recovers its ambient simplex point. -/
theorem nonemptyFacetCoordinates_map_eq
    {facets : Finset (Finset V)} (i : NonemptyFacetIndex facets)
    (x : simplexFaceCarrier i.1) :
    stdSimplex.map (i.1.orderEmbOfFin (nonemptyFacet_card i))
        (nonemptyFacetCoordinates i x) = x.1 := by
  let e : Fin (nonemptyFacetDim i + 1) ≃ i.1 :=
    (i.1.orderIsoOfFin (nonemptyFacet_card i)).toEquiv
  change stdSimplex.map (i.1.orderEmbOfFin (nonemptyFacet_card i))
      (stdSimplex.map e.symm (simplexFaceRestriction i.1 x)) = x.1
  rw [stdSimplex.map_comp_apply]
  have he : (i.1.orderEmbOfFin (nonemptyFacet_card i)) ∘ e.symm =
      (fun v : i.1 ↦ v.1) := by
    funext v
    exact congrArg Subtype.val (e.apply_symm_apply v)
  rw [he]
  change (simplexFaceEmbedding i.1 (simplexFaceRestriction i.1 x)).1 = x.1
  exact congrArg Subtype.val (simplexFaceEmbedding_restriction i.1 x)

/-- A point of a listed affine face maps back through its realized canonical simplex. -/
def facetFaceToRealization (facets : Finset (Finset V))
    (i : NonemptyFacetIndex facets) :
    C(simplexFaceCarrier i.1, SSet.toTop.obj (orderedSSet facets)) where
  toFun x :=
    SSet.toTop.map
      (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i))
      ((SimplexCategory.toTopHomeo
        (SimplexCategory.mk (nonemptyFacetDim i))).symm
          (nonemptyFacetCoordinates i x))
  continuous_toFun :=
    (SSet.toTop.map
      (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i))).hom.continuous.comp
        ((SimplexCategory.toTopHomeo
          (SimplexCategory.mk (nonemptyFacetDim i))).symm.continuous.comp
            ((stdSimplex.continuous_map _).comp
              (continuous_simplexFaceRestriction i.1)))

/-- The facewise inverse realization maps agree wherever two affine faces meet. -/
theorem facetFaceToRealization_compatible (facets : Finset (Finset V))
    (i k : NonemptyFacetIndex facets)
    (y : simplexFaceCarrier i.1) (z : simplexFaceCarrier k.1)
    (h : y.1 = z.1) :
    facetFaceToRealization facets i y =
      facetFaceToRealization facets k z := by
  apply facetRealizationPoint_eq facets i.1 k.1 i.2.1 k.2.1
    (nonemptyFacet_card i) (nonemptyFacet_card k)
  calc
    stdSimplex.map (i.1.orderEmbOfFin (nonemptyFacet_card i))
        (nonemptyFacetCoordinates i y) = y.1 :=
      nonemptyFacetCoordinates_map_eq i y
    _ = z.1 := h
    _ = stdSimplex.map (k.1.orderEmbOfFin (nonemptyFacet_card k))
        (nonemptyFacetCoordinates k z) :=
      (nonemptyFacetCoordinates_map_eq k z).symm

/-- The inverse candidate obtained by gluing all realized facet inclusions. -/
def orderedRealizationFromFacetFamilyCarrier
    (facets : Finset (Finset V)) :
    TopCat.of (facetFamilyCarrier facets) ⟶
      SSet.toTop.obj (orderedSSet facets) :=
  TopCat.ofHom (glueFacetFamily facets (facetFaceToRealization facets)
    (facetFaceToRealization_compatible facets))

/-- Gluing affine faces into the realization and applying the canonical carrier map is the
identity. -/
theorem orderedRealizationFromFacetFamilyCarrier_comp_toCarrier
    (facets : Finset (Finset V)) :
    orderedRealizationFromFacetFamilyCarrier facets ≫
        orderedRealizationToFacetFamilyCarrier facets =
      𝟙 (TopCat.of (facetFamilyCarrier facets)) := by
  apply ConcreteCategory.hom_ext
  intro b
  let i := carrierFacetIndex facets b
  let y : simplexFaceCarrier i.1 :=
    ⟨b.1, carrierFacetIndex_support facets b⟩
  rw [ConcreteCategory.comp_apply]
  change orderedRealizationToFacetFamilyCarrier facets
      (glueFacetFamily facets (facetFaceToRealization facets)
        (facetFaceToRealization_compatible facets) b) = b
  rw [show glueFacetFamily facets (facetFaceToRealization facets)
      (facetFaceToRealization_compatible facets) b =
        facetFaceToRealization facets i y by
    exact glueFacetFamily_aux facets (facetFaceToRealization facets)
      (facetFaceToRealization_compatible facets) b i
        (carrierFacetIndex_support facets b)]
  calc
    _ = (facetTopologicalCarrierMap facets i.1 i.2.1
          (nonemptyFacet_card i)).hom
        ((SimplexCategory.toTopHomeo
          (SimplexCategory.mk (nonemptyFacetDim i))).symm
            (nonemptyFacetCoordinates i y)) := by
      exact ConcreteCategory.congr_hom
        (orderedRealizationToFacetFamilyCarrier_comp_facetSSetι
          facets i.1 i.2.1 (nonemptyFacet_card i)) _
    _ = facetAffineCarrierMap facets i.1 i.2.1
        (nonemptyFacet_card i) (nonemptyFacetCoordinates i y) := by
      change facetAffineCarrierMap facets i.1 i.2.1
        (nonemptyFacet_card i)
          ((SimplexCategory.toTopHomeo
            (SimplexCategory.mk (nonemptyFacetDim i)))
              ((SimplexCategory.toTopHomeo
                (SimplexCategory.mk (nonemptyFacetDim i))).symm
                  (nonemptyFacetCoordinates i y))) = _
      rw [Homeomorph.apply_symm_apply]
    _ = b := by
      apply Subtype.ext
      exact nonemptyFacetCoordinates_map_eq i y

omit [Fintype V] in
/-- Maps out of an ordered finite complex are determined on the realized listed facets. -/
theorem orderedSSet_hom_ext_facets (facets : Finset (Finset V))
    {X : SSet} {f g : orderedSSet facets ⟶ X}
    (h : ∀ i : NonemptyFacetIndex facets,
      facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i) ≫ f =
        facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i) ≫ g) :
    f = g := by
  ext D s
  obtain ⟨facet, hfacet, hs⟩ := s.2
  have hfacet_nonempty : facet.Nonempty :=
    ⟨s.1.obj ⟨0, Nat.zero_lt_succ D.unop.len⟩,
      hs ⟨0, Nat.zero_lt_succ D.unop.len⟩⟩
  let i : NonemptyFacetIndex facets :=
    ⟨facet, hfacet, hfacet_nonempty⟩
  let a := simplexIndexHom i.1 (nonemptyFacet_card i) s.1 hs
  have hs' : (orderedSSet facets).map a.op
      (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i)) = s := by
    apply Subtype.ext
    exact nerve_map_simplexIndexHom_ambientCanonicalSimplex
      i.1 (nonemptyFacet_card i) s.1 hs
  have hcanon :
      f.app (op (SimplexCategory.mk (nonemptyFacetDim i)))
          (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i)) =
        g.app (op (SimplexCategory.mk (nonemptyFacetDim i)))
          (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i)) := by
    have hh := congrArg SSet.yonedaEquiv (h i)
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at hh
    have hiYoneda : SSet.yonedaEquiv
        (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i)) =
          facetCanonicalSimplex facets i.1 i.2.1
            (nonemptyFacet_card i) :=
      Equiv.apply_symm_apply _ _
    rw [hiYoneda] at hh
    exact hh
  rw [← hs']
  calc
    f.app D ((orderedSSet facets).map a.op
        (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i))) =
      X.map a.op (f.app _
        (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i))) := by
          exact ConcreteCategory.congr_hom (f.naturality a.op) _
    _ = X.map a.op (g.app _
        (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i))) :=
      congrArg (X.map a.op) hcanon
    _ = g.app D ((orderedSSet facets).map a.op
        (facetCanonicalSimplex facets i.1 i.2.1 (nonemptyFacet_card i))) := by
          exact (ConcreteCategory.congr_hom (g.naturality a.op) _).symm

omit [Fintype V] in
/-- Maps out of the realization are determined by their restrictions to the listed facets. -/
theorem orderedRealization_hom_ext_facets (facets : Finset (Finset V))
    {X : TopCat} {f g : SSet.toTop.obj (orderedSSet facets) ⟶ X}
    (h : ∀ i : NonemptyFacetIndex facets,
      SSet.toTop.map
          (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i)) ≫ f =
        SSet.toTop.map
          (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i)) ≫ g) :
    f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply orderedSSet_hom_ext_facets facets
  intro i
  rw [← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left]
  exact congrArg (sSetTopAdj.homEquiv _ X) (h i)

/-- A canonical ordered simplex point, regarded as a point of its ambient affine face. -/
def nonemptyFacetCanonicalFacePoint
    {facets : Finset (Finset V)} (i : NonemptyFacetIndex facets)
    (y : stdSimplex ℝ (Fin (nonemptyFacetDim i + 1))) :
    simplexFaceCarrier i.1 :=
  ⟨stdSimplex.map (i.1.orderEmbOfFin (nonemptyFacet_card i)) y, by
    intro v hv
    apply stdSimplex_map_eq_zero_of_not_mem_range
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hv⟩

/-- Reading the ordered coordinates of a canonically embedded facet point recovers them. -/
@[simp]
theorem nonemptyFacetCoordinates_canonicalFacePoint
    {facets : Finset (Finset V)} (i : NonemptyFacetIndex facets)
    (y : stdSimplex ℝ (Fin (nonemptyFacetDim i + 1))) :
    nonemptyFacetCoordinates i (nonemptyFacetCanonicalFacePoint i y) = y := by
  apply stdSimplex_map_injective_of_injective
    (i.1.orderEmbOfFin (nonemptyFacet_card i))
      (i.1.orderEmbOfFin (nonemptyFacet_card i)).injective
  rw [nonemptyFacetCoordinates_map_eq]
  rfl

/-- Include one affine face in the full facet-family carrier. -/
def faceCarrierToFacetFamilyCarrier
    (facets : Finset (Finset V)) (i : NonemptyFacetIndex facets)
    (x : simplexFaceCarrier i.1) : facetFamilyCarrier facets :=
  ⟨x.1, by
    rw [mem_facetFamilyCarrier_iff]
    exact ⟨i.1, i.2.1, x.2⟩⟩

/-- A realized facet followed by the glued inverse is its canonical realized inclusion. -/
theorem facetTopologicalCarrierMap_comp_fromCarrier
    (facets : Finset (Finset V)) (i : NonemptyFacetIndex facets) :
    facetTopologicalCarrierMap facets i.1 i.2.1
        (nonemptyFacet_card i) ≫
      orderedRealizationFromFacetFamilyCarrier facets =
        SSet.toTop.map
          (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i)) := by
  apply ConcreteCategory.hom_ext
  intro x
  let y : stdSimplex ℝ (Fin (nonemptyFacetDim i + 1)) :=
    (SimplexCategory.toTopHomeo
      (SimplexCategory.mk (nonemptyFacetDim i))) x
  let p : simplexFaceCarrier i.1 :=
    nonemptyFacetCanonicalFacePoint i y
  change glueFacetFamily facets (facetFaceToRealization facets)
      (facetFaceToRealization_compatible facets)
        (facetAffineCarrierMap facets i.1 i.2.1
          (nonemptyFacet_card i) y) =
    SSet.toTop.map
      (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i)) x
  rw [show facetAffineCarrierMap facets i.1 i.2.1
      (nonemptyFacet_card i) y =
        faceCarrierToFacetFamilyCarrier facets i p by
    apply Subtype.ext
    rfl]
  rw [show glueFacetFamily facets (facetFaceToRealization facets)
      (facetFaceToRealization_compatible facets)
        (faceCarrierToFacetFamilyCarrier facets i p) =
      facetFaceToRealization facets i p by
    exact glueFacetFamily_face facets (facetFaceToRealization facets)
      (facetFaceToRealization_compatible facets) i p]
  change SSet.toTop.map
      (facetSSetι facets i.1 i.2.1 (nonemptyFacet_card i))
        ((SimplexCategory.toTopHomeo
          (SimplexCategory.mk (nonemptyFacetDim i))).symm
            (nonemptyFacetCoordinates i p)) = _
  rw [show nonemptyFacetCoordinates i p = y by
    exact nonemptyFacetCoordinates_canonicalFacePoint i y]
  rw [show y = (SimplexCategory.toTopHomeo
      (SimplexCategory.mk (nonemptyFacetDim i))) x by rfl]
  rw [Homeomorph.symm_apply_apply]

/-- Applying the affine carrier map and then gluing all realized facets is the identity. -/
theorem orderedRealizationToFacetFamilyCarrier_comp_fromCarrier
    (facets : Finset (Finset V)) :
    orderedRealizationToFacetFamilyCarrier facets ≫
        orderedRealizationFromFacetFamilyCarrier facets =
      𝟙 (SSet.toTop.obj (orderedSSet facets)) := by
  apply orderedRealization_hom_ext_facets facets
  intro i
  rw [← Category.assoc,
    orderedRealizationToFacetFamilyCarrier_comp_facetSSetι,
    facetTopologicalCarrierMap_comp_fromCarrier, Category.comp_id]

/-- The realization of any finite ordered simplicial complex is homeomorphic to the union of its
affine simplex faces. -/
def orderedRealizationHomeomorphFacetFamilyCarrier
    (facets : Finset (Finset V)) :
    SSet.toTop.obj (orderedSSet facets) ≃ₜ facetFamilyCarrier facets where
  toFun := orderedRealizationToFacetFamilyCarrier facets
  invFun := orderedRealizationFromFacetFamilyCarrier facets
  left_inv x := by
    have h := ConcreteCategory.congr_hom
      (orderedRealizationToFacetFamilyCarrier_comp_fromCarrier facets) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  right_inv x := by
    have h := ConcreteCategory.congr_hom
      (orderedRealizationFromFacetFamilyCarrier_comp_toCarrier facets) x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  continuous_toFun := (orderedRealizationToFacetFamilyCarrier facets).hom.continuous
  continuous_invFun := (orderedRealizationFromFacetFamilyCarrier facets).hom.continuous

end Submission.FiniteOrderedComplex
