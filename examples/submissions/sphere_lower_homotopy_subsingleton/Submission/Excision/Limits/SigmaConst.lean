/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# ...

-/

universe v u

@[expose] public section

open CategoryTheory Limits

-- Reducibility attributes that upstream Mathlib gained after the revision pinned here;
-- the vendored library relies on them.
attribute [local implicit_reducible] Limits.Cofan.mk Limits.Fan.mk Limits.sigmaConst
  Limits.sigmaConstCokernelCofork Limits.Cofork.ofπ Limits.Fork.ofι

namespace CategoryTheory

variable {C : Type*} [Category* C]

section

variable [HasCoproducts.{max u v} C]

/-- The isomorphism `(sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T`
when `T : Type u`. -/
@[no_expose]
noncomputable def sigmaConstObjObjULiftIso (X : C) (T : Type u) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    (sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T :=
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  Sigma.reindex Equiv.ulift.{v, u} (fun (_ : T) ↦ X)

@[reassoc (attr := simp)]
lemma ι_sigmaConstObjObjULiftIso_hom (X : C) {T : Type u} (t : ULift.{v} T) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    Sigma.ι _ t ≫ (sigmaConstObjObjULiftIso.{v} X T).hom =
      Sigma.ι (fun _ ↦ X) t.down := by
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  exact Sigma.ι_reindex_hom Equiv.ulift.{v, u} (fun (_ : T) ↦ X) t

@[reassoc (attr := simp)]
lemma ι_sigmaConstObjObjULiftIso_inv (X : C) {T : Type u} (t : T) :
    haveI : HasCoproducts.{u} C := hasCoproducts_shrink
    Sigma.ι _ t ≫ (sigmaConstObjObjULiftIso.{v} X T).inv =
      Sigma.ι (fun _ ↦ X) (ULift.up.{v} t) := by
  rw [← ι_sigmaConstObjObjULiftIso_hom_assoc.{v}, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism `(sigmaConst.obj X).obj (ULift.{v} T) ≅ (sigmaConst.obj X).obj T`
for `X : C` and `T : Type u`, as an isomorphism of functors `C ⥤ Type u ⥤ C`. -/
@[simps!]
noncomputable def sigmaConstULiftIso :
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  sigmaConst.{max u v} ⋙
    (Functor.whiskeringLeft _ _ C).obj uliftFunctor.{v, u} ≅
  sigmaConst.{u} :=
  haveI : HasCoproducts.{u} C := hasCoproducts_shrink
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun T ↦ sigmaConstObjObjULiftIso.{v} X T) (by
      intro T₁ T₂ g
      refine Sigma.hom_ext (f := fun (_ : ULift.{v} T₁) ↦ X) _ _ (fun t ↦ ?_)
      rw [show ((sigmaConst.{max u v} ⋙
          (Functor.whiskeringLeft _ _ C).obj uliftFunctor.{v, u}).obj X).map g =
            (sigmaConst.obj X).map (uliftFunctor.{v, u}.map g) from rfl,
        sigmaConst_obj_map, sigmaConst_obj_map]
      erw [Sigma.ι_comp_map'_assoc, ι_sigmaConstObjObjULiftIso_hom,
        ι_sigmaConstObjObjULiftIso_hom_assoc, Sigma.ι_comp_map', Category.id_comp]))
    (by
      intro X Y g
      ext T
      refine Sigma.hom_ext (f := fun (_ : ULift.{v} T) ↦ X) _ _ (fun t ↦ ?_)
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Functor.comp_map,
        Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app, sigmaConst_map_app]
      erw [Sigma.ι_map_assoc, ι_sigmaConstObjObjULiftIso_hom,
        ι_sigmaConstObjObjULiftIso_hom_assoc, Sigma.ι_map])

end

open Classical in
instance [HasCoproducts.{u} C] {T₁ T₂ : Type u} (f : T₁ ⟶ T₂) [Mono f] [Preadditive C] (X : C) :
    IsSplitMono ((sigmaConst.obj X).map f) := by
  have (t₂ : T₂) (ht₂ : t₂ ∈ Set.range f) : ∃ t₁, f t₁ = t₂ := ht₂
  choose t₁ ht₁ using this
  have ht (t : T₁) : t₁ (f t) (by simp) = t := injective_of_mono f (ht₁ _ _)
  exact ⟨⟨{
    retraction :=
      Sigma.desc (fun t₂ ↦
        if ht₂ : t₂ ∈ Set.range f then Sigma.ι (fun _ ↦ X) (t₁ t₂ ht₂) else 0)
    id := by
      dsimp
      refine Sigma.hom_ext _ _ (fun t ↦ ?_)
      refine Eq.trans ?_ (Category.comp_id _).symm
      rw [sigmaConst_obj_map, Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc,
        dif_pos (Set.mem_range_self t), ht]
  }⟩⟩

namespace Limits

variable [Preadditive C] (R : C)

section

variable {α β : Type*} (f : α → β) (hf : Function.Injective f)
  [HasCoproduct (fun (_ : α) ↦ R)] [HasCoproduct (fun (_ : β) ↦ R)]
  [HasCoproduct (fun (_ : ((Set.range f)ᶜ : Set _)) ↦ R)]

/-- The short complex corresponding to the colimit cofork
`sigmaConstCokernelCofork R f` for `f : α → β`. -/
noncomputable abbrev sigmaConstCokernelShortComplex : ShortComplex C :=
    .mk _ _ (sigmaConstCokernelCofork R f).condition

/-- When `f : α → β` is injective, the short complex
`sigmaConstCokernelShortComplex R f` admits a splitting. -/
noncomputable def splittingSigmaConstCokernelShortComplex :
    (sigmaConstCokernelShortComplex R f).Splitting := by
  classical
  have (b : β) (hb : b ∈ Set.range f) : ∃ a, f a = b := hb
  choose ρ hρ using this
  have hρ' (a : α) : ρ (f a) (by simp) = a := hf (hρ _ _)
  exact
  { r := Sigma.desc (fun b ↦
      if hb : b ∈ Set.range f then Sigma.ι (fun _ ↦ R) (ρ b hb) else 0)
    s := Sigma.desc (fun ⟨c, _⟩ ↦ Sigma.ι (fun _ ↦ R) c)
    f_r := by
      dsimp
      refine Sigma.hom_ext _ _ (fun a ↦ ?_)
      refine Eq.trans ?_ (Category.comp_id _).symm
      rw [Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_desc,
        dif_pos (Set.mem_range_self a), hρ']
    s_g := by
      dsimp
      refine Sigma.hom_ext _ _ (fun c ↦ ?_)
      obtain ⟨c, hc⟩ := c
      refine Eq.trans ?_ (Category.comp_id _).symm
      dsimp [sigmaConstCokernelCofork]
      rw [Sigma.ι_desc_assoc, Sigma.ι_desc, dif_pos hc]
    id := by
      dsimp
      refine Sigma.hom_ext _ _ (fun b ↦ ?_)
      refine Eq.trans ?_ (Category.comp_id _).symm
      dsimp [sigmaConstCokernelCofork]
      rw [Preadditive.comp_add, Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        rw [dif_pos (Set.mem_range_self a), hρ',
          dif_neg (by simp),
          Sigma.ι_comp_map', Category.id_comp, zero_comp, add_zero]
      · rw [dif_neg hb, dif_pos (by simpa using hb), zero_comp, zero_add, Sigma.ι_desc] }

/-- If `c` is a colimit cokernel cofork for a map `∐ fun (_ : α) ↦ R ⟶ ∐ fun (_ : β) ↦ R`
induced by an injective map `f : α → β`, this is a splitting of the short complex
given by the vanishing `c.condition`. -/
noncomputable def splittingSigmaConstCokernelShortComplex'
    {c : CokernelCofork (Sigma.map' (f := fun (_ : α) ↦ R) (g := fun (_ : β) ↦ R) f (fun _ ↦ 𝟙 R))}
    (hc : IsColimit c) :
    (ShortComplex.mk _ _ c.condition).Splitting :=
  (splittingSigmaConstCokernelShortComplex R f hf).ofIso
    ((ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (IsColimit.coconePointUniqueUpToIso (isColimitSigmaConstCokernelCofork R f) hc)
      (by cat_disch) (by
      simp [dsimp% (IsColimit.comp_coconePointUniqueUpToIso_hom
        (isColimitSigmaConstCokernelCofork R f) hc) .one])))

/-- Let `f : α → β` be an injective map and `R : C` an object in a category
with suitable coproducts. Then, the map `∐ fun (a : α) ↦ R) ⟶ ∐ fun (b : β) ↦ R`
is the kernel of the projection to its cokernel. -/
@[no_expose]
noncomputable def isLimitKernelForkOfIsColimitCokernelCoforkSigmaConst
    [HasZeroObject C]
    {c : CokernelCofork (Sigma.map' (f := fun (_ : α) ↦ R) (g := fun (_ : β) ↦ R) f (fun _ ↦ 𝟙 R))}
    (hc : IsColimit c) :
    IsLimit (KernelFork.ofι _ c.condition) := by
  let iso := IsColimit.coconePointUniqueUpToIso (isColimitSigmaConstCokernelCofork R f) hc
  have hiso : (sigmaConstCokernelCofork R f).π ≫ iso.hom = c.π :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitSigmaConstCokernelCofork R f) hc (.one)
  let e : parallelPair (sigmaConstCokernelCofork R f).π 0 ≅
      parallelPair c.π 0 :=
    parallelPair.ext (Iso.refl _) iso (by simpa) (by simp)
  refine IsLimit.ofIsoLimit
    ((IsLimit.postcomposeHomEquiv e _).2
    ((splittingSigmaConstCokernelShortComplex R f hf).fIsKernel))
    (Fork.ext (Iso.refl _) ?_)
  dsimp [Cone.postcompose, Fork.ι, parallelPair.ext, e]
  cat_disch

end

end Limits

end CategoryTheory
