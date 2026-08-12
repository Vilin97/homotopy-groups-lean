/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Submission.Homology.MayerVietorisLES
import Submission.Homology.RelMap

/-!
# Excision for relative singular homology

For subsets `A B ⊆ X` whose interiors cover `X`, inclusion induces an isomorphism

`H_*(A, A ∩ B) ⟶ H_*(X, B)`.

The proof separates the two standard ingredients already present in the development.

* The Mayer--Vietoris short exact sequence exhibits the square of small singular chain
  complexes as a pushout, so it induces an isomorphism on cokernels.
* The small-simplices homotopy equivalence identifies the relative small-chain cokernel with
  the ordinary relative singular chain complex on homology.

Their composite is proved equal to the canonical map of relative chain complexes.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor AlgebraicTopology.singularChainComplexFunctor

noncomputable section

namespace Submission

variable {X : TopCat.{0}} (A B : Set X)

/-- The square of singular chain complexes attached to the small-simplices cover is a pushout. -/
theorem mvChain_isPushout :
    IsPushout
      (SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap (mvQb A B) (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ))
      (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) := by
  let qa := SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ)
  let qb := SSet.chainComplexMap (mvQb A B) (AddCommGrpCat.of ℤ)
  let pa := SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ)
  let pb := SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)
  let h := (mvSC_shortExact A B).gIsCokernel
  have hcond : qa ≫ pa = qb ≫ pb := by
    dsimp [qa, qb, pa, pb]
    rw [← (SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) |>.map_comp,
      ← (SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ) |>.map_comp,
      mvQa_comp_mvPa]
  have hzero (s : PushoutCocone qa qb) :
      biprod.lift qa qb ≫ biprod.desc s.inl (-s.inr) = 0 := by
    simp only [biprod.lift_desc, Preadditive.comp_neg, s.condition, add_neg_cancel]
  let desc (s : PushoutCocone qa qb) : mvSmallComplex A B ⟶ s.pt :=
    h.desc (CokernelCofork.ofπ (biprod.desc s.inl (-s.inr)) (hzero s))
  have hfac (s : PushoutCocone qa qb) :
      biprod.desc pa (-pb) ≫ desc s = biprod.desc s.inl (-s.inr) := by
    exact h.fac (CokernelCofork.ofπ (biprod.desc s.inl (-s.inr)) (hzero s))
      WalkingParallelPair.one
  have fac_left (s : PushoutCocone qa qb) : pa ≫ desc s = s.inl := by
    calc
      pa ≫ desc s = biprod.inl ≫ biprod.desc pa (-pb) ≫ desc s := by simp
      _ = biprod.inl ≫ biprod.desc s.inl (-s.inr) := by rw [hfac]
      _ = s.inl := by simp
  have fac_right (s : PushoutCocone qa qb) : pb ≫ desc s = s.inr := by
    have hneg : (-pb) ≫ desc s = -s.inr := by
      calc
        (-pb) ≫ desc s = biprod.inr ≫ biprod.desc pa (-pb) ≫ desc s := by simp
        _ = biprod.inr ≫ biprod.desc s.inl (-s.inr) := by rw [hfac]
        _ = -s.inr := by simp
    simpa only [Preadditive.neg_comp, neg_inj] using hneg
  exact IsPushout.of_isColimit
    (PushoutCocone.IsColimit.mk hcond desc fac_left fac_right (fun s m hm₁ hm₂ => by
      apply Cofork.IsColimit.hom_ext h
      have heq : biprod.desc pa (-pb) ≫ m = biprod.desc pa (-pb) ≫ desc s := by
        apply biprod.hom_ext' <;>
          simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Preadditive.neg_comp,
            hm₁, hm₂, fac_left, fac_right]
      exact heq))

/-- The relative chain complex of the small-simplices pair `(C^{A,B}_*(X), C_*(B))`. -/
abbrev mvSmallRelComplex : ChainComplex AddCommGrpCat.{0} ℕ :=
  cokernel (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))

instance mono_mvInclLeft : Mono (mvInclLeft A B) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext (congrArg (fun z : A => (z : X)) h)

instance mono_mvInclRight : Mono (mvInclRight A B) := by
  rw [TopCat.mono_iff_injective]
  intro x y h
  exact Subtype.ext (congrArg (fun z : B => (z : X)) h)

/-- The pushout square induces the chain map from `(A, A ∩ B)` to the relative small-chain
complex. -/
noncomputable def mvExcisionToSmallChainMap :
    relComplex (mvInclLeft A B) ⟶ mvSmallRelComplex A B :=
  let sq := mvChain_isPushout A B
  cokernel.map
    (SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ))
    (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
    (SSet.chainComplexMap (mvQb A B) (AddCommGrpCat.of ℤ))
    (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ)) sq.w

/-- The pushout comparison of relative chain complexes is an isomorphism. -/
theorem isIso_mvExcisionToSmallChainMap :
    IsIso (mvExcisionToSmallChainMap A B) := by
  exact isIso_cokernel_map_of_isPushout (mvChain_isPushout A B)

instance mono_mvPb : Mono (mvPb A B) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [CategoryTheory.mono_iff_injective]
  exact injective_mvPb_app A B n

/-- The short exact sequence defining relative chains for the small-simplices pair. -/
noncomputable def mvSmallRelShortComplex :
    ShortComplex (ChainComplex AddCommGrpCat.{0} ℕ) :=
  let pb := SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)
  ShortComplex.mk pb (cokernel.π pb) (cokernel.condition pb)

theorem mvSmallRelShortComplex_shortExact :
    (mvSmallRelShortComplex A B).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    change Mono (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
    infer_instance
  epi_g := coequalizer.π_epi

/-- Inclusion of small chains in all singular chains induces a map of relative complexes. -/
noncomputable def mvSmallRelMap :
    mvSmallRelComplex A B ⟶ relComplex (subIncl B) :=
  cokernel.map
    (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
    (CsingMap (subIncl B)) (𝟙 _) (mvSmallIncl A B)
    ((mvPb_smallIncl A B).trans (Category.id_comp _).symm)

/-- The morphism of relative short exact sequences induced by inclusion of small chains. -/
noncomputable def mvSmallRelShortComplexMap :
    mvSmallRelShortComplex A B ⟶ relShortComplex (subIncl B) where
  τ₁ := 𝟙 _
  τ₂ := mvSmallIncl A B
  τ₃ := mvSmallRelMap A B
  comm₁₂ := by
    change (𝟙 _ : Csing (TopCat.of B) ⟶ Csing (TopCat.of B)) ≫ CsingMap (subIncl B) =
      SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ) ≫ mvSmallIncl A B
    rw [Category.id_comp, mvPb_smallIncl]
  comm₂₃ := by
    change mvSmallIncl A B ≫ relProj (subIncl B) =
      cokernel.π (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) ≫
        mvSmallRelMap A B
    symm
    change cokernel.π (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) ≫
        cokernel.desc (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
          (mvSmallIncl A B ≫ cokernel.π (CsingMap (subIncl B))) _ =
      mvSmallIncl A B ≫ cokernel.π (CsingMap (subIncl B))
    rw [cokernel.π_desc]

/-- If the interiors cover, inclusion of small chains induces an isomorphism on relative
homology. -/
theorem isIso_homologyMap_mvSmallRelMap
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mvSmallRelMap A B) n) := by
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (mvSmallRelShortComplexMap A B)
    (mvSmallRelShortComplex_shortExact A B)
    (relShortComplex_shortExact (subIncl B))
  · change Epi (HomologicalComplex.homologyMap (𝟙 (Csing (TopCat.of B))) n)
    rw [HomologicalComplex.homologyMap_id]
    infer_instance
  · change IsIso (HomologicalComplex.homologyMap (mvSmallIncl A B) n)
    exact (mvSmallHomologyIso A B h n).isIso_hom
  · intro j _
    change IsIso (HomologicalComplex.homologyMap (𝟙 (Csing (TopCat.of B))) j)
    rw [HomologicalComplex.homologyMap_id]
    infer_instance
  · intro j _
    change Mono (HomologicalComplex.homologyMap (mvSmallIncl A B) j)
    exact (mvSmallHomologyIso A B h j).isIso_hom.mono_of_iso

/-- The pushout and small-simplices comparisons compose to the canonical relative chain map. -/
theorem mvExcisionChainMap_comp :
    mvExcisionToSmallChainMap A B ≫ mvSmallRelMap A B =
      relComplexMap (mvInclLeft A B) (subIncl B)
        (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl) := by
  apply (coequalizer.π_epi : Epi (relProj (mvInclLeft A B))).left_cancellation
  change cokernel.π (CsingMap (mvInclLeft A B)) ≫
      (mvExcisionToSmallChainMap A B ≫ mvSmallRelMap A B) =
    cokernel.π (CsingMap (mvInclLeft A B)) ≫
      relComplexMap (mvInclLeft A B) (subIncl B) _
  rw [← Category.assoc]
  change (cokernel.π (SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ)) ≫
      cokernel.desc (SSet.chainComplexMap (mvQa A B) (AddCommGrpCat.of ℤ))
        (SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ) ≫
          cokernel.π (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))) _) ≫
      mvSmallRelMap A B =
    cokernel.π (CsingMap (mvInclLeft A B)) ≫
      relComplexMap (mvInclLeft A B) (subIncl B) _
  rw [cokernel.π_desc, Category.assoc]
  change SSet.chainComplexMap (mvPa A B) (AddCommGrpCat.of ℤ) ≫
      (cokernel.π (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ)) ≫
        cokernel.desc (SSet.chainComplexMap (mvPb A B) (AddCommGrpCat.of ℤ))
          (mvSmallIncl A B ≫ cokernel.π (CsingMap (subIncl B))) _) =
    cokernel.π (CsingMap (mvInclLeft A B)) ≫
      relComplexMap (mvInclLeft A B) (subIncl B) _
  rw [cokernel.π_desc, ← Category.assoc, mvPa_smallIncl]
  change CsingMap (subIncl A) ≫ relProj (subIncl B) =
    relProj (mvInclLeft A B) ≫ relComplexMap (mvInclLeft A B) (subIncl B) _
  exact (relProj_comp_relComplexMap (mvInclLeft A B) (subIncl B) _).symm

/-- The canonical relative-homology excision map for a two-set cover. -/
def mvExcisionHrelMap (n : ℕ) : Hrel n (mvInclLeft A B) ⟶ Hrel n (subIncl B) :=
  HrelMap n (mvInclLeft A B) (subIncl B)
    (show mvInclLeft A B ≫ subIncl A = mvInclRight A B ≫ subIncl B by rfl)

/-- **Excision for relative singular homology.** If the interiors of `A` and `B` cover `X`, the
canonical map `H_n(A, A ∩ B) ⟶ H_n(X, B)` is an isomorphism in every degree. -/
theorem isIso_mvExcisionHrelMap (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (mvExcisionHrelMap A B n) := by
  letI := isIso_mvExcisionToSmallChainMap A B
  letI := isIso_homologyMap_mvSmallRelMap A B h n
  have hi : IsIso (HomologicalComplex.homologyMap
      (mvExcisionToSmallChainMap A B ≫ mvSmallRelMap A B) n) := by
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  rw [mvExcisionChainMap_comp] at hi
  exact hi

end Submission
