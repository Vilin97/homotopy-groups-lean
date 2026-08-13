/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Cohomology.DualShortExact
import Submission.Cohomology.DualBridge
import Submission.Homology.MayerVietoris
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# The cohomological long exact sequence of a pair

For an injective continuous map `i : A ⟶ X`, the singular-chain inclusion is split in each degree:
a singular simplex in `X` is sent back to its unique preimage when it lies in the image of `i`,
and to zero otherwise.  Consequently the relative-chain short exact sequence remains short exact
after applying `Hom(-, G)`.  Its homology is the cohomological long exact sequence of the pair.

This file keeps relative cohomology in the categorical dual-complex model.  The natural bridge to
the concrete `Hsing` groups then shows that restriction `Hⁿ(X;R) ⟶ Hⁿ(A;R)` is bijective whenever
the relative groups in degrees `n` and `n+1` vanish.

## Main definitions and results

* `Submission.relDegreeSplitting` -- the degreewise splitting of relative singular chains;
* `Submission.relCohSC` and `Submission.relCohSC_shortExact` -- the dual short exact sequence;
* `Submission.HrelCoh` -- relative cohomology in the dual-complex model;
* `Submission.isIso_relCohRestriction` -- the relative-vanishing criterion;
* `Submission.bijective_Hsing_map_of_isZero_HrelCoh` -- its concrete singular-cohomology form.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

attribute [local implicit_reducible] Limits.Cofan.mk Limits.sigmaConst
  AlgebraicTopology.alternatingFaceMapComplex AlgebraicTopology.AlternatingFaceMapComplex.obj
  SSet.chainComplexFunctor

noncomputable section

namespace Submission

variable {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]

/-- The degreewise retraction of an injective singular-chain map. -/
def relRetr (n : ℕ) : (Csing X).X n ⟶ (Csing A).X n :=
  mvRetr (TopCat.toSSet.map i) n

@[reassoc]
theorem CsingMap_comp_relRetr (n : ℕ) :
    (CsingMap i).f n ≫ relRetr i n = 𝟙 ((Csing A).X n) := by
  change (SSet.chainComplexMap (TopCat.toSSet.map i) (AddCommGrpCat.of ℤ)).f n ≫
    mvRetr (TopCat.toSSet.map i) n =
      𝟙 ((CsingSSet (TopCat.toSSet.obj A)).X n)
  have hi : Function.Injective i := (TopCat.mono_iff_injective i).1 inferInstance
  have hs := injective_toSSet_map_app i hi n
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ι_mvRetr (TopCat.toSSet.map i) hs,
    Category.comp_id]

/-- The relative singular-chain short exact sequence is split in every degree. -/
def relDegreeSplitting (n : ℕ) : ShortComplex.Splitting
    ((relShortComplex i).map
      (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n)) := by
  let h := ((HomologicalComplex.shortExact_iff_degreewise_shortExact
    (relShortComplex i)).1 (relShortComplex_shortExact i) n)
  exact ShortComplex.Splitting.ofExactOfRetraction _ h.exact (relRetr i n)
    (CsingMap_comp_relRetr i n) h.epi_g

variable (G : AddCommGrpCat.{0})

/-- The reversed dual of the relative singular-chain short complex. -/
abbrev relCohSC :
    ShortComplex (HomologicalComplex AddCommGrpCat.{0} (ComplexShape.down ℕ).symm) :=
  homDualShortComplex (relShortComplex i) G

/-- The cochain-level sequence of a pair is short exact. -/
theorem relCohSC_shortExact : (relCohSC i G).ShortExact :=
  homDualShortComplex_shortExact (relShortComplex i) G (relDegreeSplitting i)

/-- Relative cohomology, modeled as the homology of the dual relative-chain complex. -/
abbrev HrelCoh (n : ℕ) : AddCommGrpCat.{0} :=
  (homDual (relComplex i) G).homology n

/-- Restriction on dual-complex cohomology. -/
abbrev relCohRestriction (n : ℕ) :
    (homDual (Csing X) G).homology n ⟶ (homDual (Csing A) G).homology n :=
  HomologicalComplex.homologyMap (homDualMap (CsingMap i) G) n

/-- Exactness at absolute cohomology:
`Hⁿ(X,A;G) ⟶ Hⁿ(X;G) ⟶ Hⁿ(A;G)`. -/
theorem relCoh_exact_relative_absolute_restriction (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relCohSC i G).f n)
      (relCohRestriction i G n)
      (by
        change HomologicalComplex.homologyMap (relCohSC i G).f n ≫
          HomologicalComplex.homologyMap (relCohSC i G).g n = 0
        rw [← HomologicalComplex.homologyMap_comp, (relCohSC i G).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (relCohSC_shortExact i G).homology_exact₂ n

/-- Exactness at the subspace cohomology:
`Hⁿ(X;G) ⟶ Hⁿ(A;G) ⟶ Hⁿ⁺¹(X,A;G)`. -/
theorem relCoh_exact_restriction_connecting (n : ℕ) :
    (ShortComplex.mk
      (relCohRestriction i G n)
      ((relCohSC_shortExact i G).δ n (n + 1) (by rfl))
      ((relCohSC_shortExact i G).comp_δ n (n + 1) (by rfl))).Exact :=
  (relCohSC_shortExact i G).homology_exact₃ n (n + 1) (by rfl)

/-- Relative cohomology in degree `n+1` vanishes when degree `n` cohomology of the
subspace and degree `n+1` cohomology of the ambient space both vanish. -/
theorem isZero_HrelCoh_of_isZero_subspace_of_isZero_space (n : ℕ)
    (hA : IsZero ((homDual (Csing A) G).homology n))
    (hX : IsZero ((homDual (Csing X) G).homology (n + 1))) :
    IsZero (HrelCoh i G (n + 1)) :=
  ((relCohSC_shortExact i G).homology_exact₁ n (n + 1) (by rfl)).isZero_X₂
    (hA.eq_of_src _ _) (hX.eq_of_tgt _ _)

/-- If relative cohomology vanishes in degrees `n` and `n+1`, restriction on degree `n`
cohomology is an isomorphism. -/
theorem isIso_relCohRestriction (n : ℕ)
    (hn : IsZero (HrelCoh i G n)) (hn₁ : IsZero (HrelCoh i G (n + 1))) :
    IsIso (relCohRestriction i G n) := by
  haveI : Mono (relCohRestriction i G n) :=
    (relCoh_exact_relative_absolute_restriction i G n).mono_g (hn.eq_of_src _ _)
  haveI : Epi (relCohRestriction i G n) :=
    (relCoh_exact_restriction_connecting i G n).epi_f (hn₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable (R : Type) [CommRing R]

/-- Relative vanishing in adjacent degrees makes the concrete singular-cohomology restriction
map bijective. -/
theorem bijective_Hsing_map_of_isZero_HrelCoh (n : ℕ)
    (hn : IsZero (HrelCoh i (AddCommGrpCat.of R) n))
    (hn₁ : IsZero (HrelCoh i (AddCommGrpCat.of R) (n + 1))) :
    Function.Bijective (Hsing.map (R := R) i n) := by
  letI : IsIso (relCohRestriction i (AddCommGrpCat.of R) n) :=
    isIso_relCohRestriction i (AddCommGrpCat.of R) n hn hn₁
  have hbij : Function.Bijective (relCohRestriction i (AddCommGrpCat.of R) n) :=
    ⟨(AddCommGrpCat.mono_iff_injective _).1 inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance⟩
  constructor
  · intro x y hxy
    apply (HsingEquivDualHomology R X n).injective
    apply hbij.1
    rw [← HsingEquivDualHomology_naturality,
      ← HsingEquivDualHomology_naturality, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hbij.2 (HsingEquivDualHomology R A n y)
    refine ⟨(HsingEquivDualHomology R X n).symm z, ?_⟩
    apply (HsingEquivDualHomology R A n).injective
    rw [HsingEquivDualHomology_naturality, AddEquiv.apply_symm_apply, hz]

end Submission
