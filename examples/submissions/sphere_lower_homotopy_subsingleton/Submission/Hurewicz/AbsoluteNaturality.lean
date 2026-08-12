/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.AbsoluteIsomorphism

/-!
# Naturality of the absolute Hurewicz homomorphism

The maintained absolute Hurewicz homomorphism is defined through the relative Hurewicz map of
the singleton pair.  Including that singleton in an arbitrary based subspace gives the expected
compatibility between the absolute-to-relative maps in homotopy and homology.  This is the
comparison square needed for pairs with contractible distinguished subspace.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {X : Type} [TopologicalSpace X]

/-- A based continuous map, regarded as a map between the singleton pairs at its source and
target basepoints. -/
def singletonBasedPairMap {Y : Type} [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y) :
    BasedPairMap ({x} : Set X) ({y} : Set Y)
      (⟨x, rfl⟩ : ({x} : Set X)) (⟨y, rfl⟩ : ({y} : Set Y)) where
  toContinuousMap := f
  mapsTo' := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz ⊢
    simpa [hz] using hf
  map_basepoint' := hf

/-- Inclusion of the singleton at the basepoint into an arbitrary based subspace, with the
identity map on the ambient space. -/
def singletonToBasedPair (A : Set X) (a : A) :
    BasedPairMap ({(a : X)} : Set X) A
      (⟨a, rfl⟩ : ({(a : X)} : Set X)) a where
  toContinuousMap := ContinuousMap.id X
  mapsTo' := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact a.property
  map_basepoint' := rfl

/-- Relative Hurewicz applied after `j_*` agrees with absolute Hurewicz followed by the
absolute-to-relative map in homology. -/
theorem relativeHurewicz_jStar (n : ℕ) (A : Set X) (a : A)
    (z : π_ (n + 2) X (a : X)) :
    relativeHurewicz n A a
        (RelHomotopyGroup.jStar (n + 2) X A a z) =
      relJ (n + 2) (subIncl (Y := TopCat.of X) A)
        (absoluteHurewiczAdd n (a : X) (Additive.ofMul z)) := by
  let a₀ : ({(a : X)} : Set X) := ⟨a, rfl⟩
  let f := singletonToBasedPair A a
  have hHur := relativeHurewicz_naturality n f
    (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)
  have hJ := ConcreteCategory.congr_hom
    (relJ_naturality (n + 2)
      (subIncl (Y := TopCat.of X) ({(a : X)} : Set X))
      (subIncl (Y := TopCat.of X) A)
      f.subIncl_naturality)
    (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hJ
  change f.hrelMap (n + 2)
      (relativeHurewicz n ({(a : X)} : Set X) a₀
        (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)) = _ at hHur
  rw [RelHomotopyGroup.map_jStar] at hHur
  have hmap : HomotopyGroup.map f.toContinuousMap f.map_basepoint' z = z := by
    change HomotopyGroup.map (ContinuousMap.id X) _ z = z
    exact HomotopyGroup.map_id_apply z
  rw [hmap] at hHur
  rw [relJ_absoluteHurewiczAdd] at hJ
  have hamb : f.ambientHom = 𝟙 (TopCat.of X) := rfl
  have hHgrp : HgrpMap (n + 2) f.ambientHom = 𝟙 _ := by
    rw [hamb, HgrpMap_id]
  have hHgrpApply := ConcreteCategory.congr_hom hHgrp
    (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))
  rw [ConcreteCategory.id_apply] at hHgrpApply
  change f.hrelMap (n + 2)
      (relativeHurewicz n ({(a : X)} : Set X) a₀
        (RelHomotopyGroup.jStar (n + 2) X ({(a : X)} : Set X) a₀ z)) =
    relJ (n + 2) (subIncl (Y := TopCat.of X) A)
      (HgrpMap (n + 2) f.ambientHom
        (absoluteHurewiczAdd n (a : X) (Additive.ofMul z))) at hJ
  exact hHur.symm.trans (hJ.trans (congrArg
    (fun q => relJ (n + 2) (subIncl (Y := TopCat.of X) A) q) hHgrpApply))

/-- The absolute Hurewicz homomorphism is natural under based continuous maps. -/
theorem absoluteHurewiczAdd_naturality (n : ℕ)
    {Y : Type} [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y) (z : Additive (π_ (n + 2) X x)) :
    HgrpMap (n + 2) (TopCat.ofHom f) (absoluteHurewiczAdd n x z) =
      absoluteHurewiczAdd n y
        (Additive.ofMul (HomotopyGroup.map f hf z.toMul)) := by
  let a : ({x} : Set X) := ⟨x, rfl⟩
  let b : ({y} : Set Y) := ⟨y, rfl⟩
  let F := singletonBasedPairMap f hf
  let i := subIncl (Y := TopCat.of X) ({x} : Set X)
  let j := subIncl (Y := TopCat.of Y) ({y} : Set Y)
  have hHur := relativeHurewicz_naturality n F
    (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)
  change F.hrelMap (n + 2)
      (relativeHurewicz n ({x} : Set X) a
        (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) = _ at hHur
  rw [RelHomotopyGroup.map_jStar] at hHur
  change F.hrelMap (n + 2)
      (relativeHurewicz n ({x} : Set X) a
        (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) =
    relativeHurewicz n ({y} : Set Y) b
      (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
        (HomotopyGroup.map f hf z.toMul)) at hHur
  have hJ := ConcreteCategory.congr_hom
    (relJ_naturality (n + 2) i j F.subIncl_naturality)
    (absoluteHurewiczAdd n x z)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hJ
  have hsource := relJ_absoluteHurewiczAdd n x z
  have htarget := relJ_absoluteHurewiczAdd n y
    (Additive.ofMul (HomotopyGroup.map f hf z.toMul))
  change relJ (n + 2) i (absoluteHurewiczAdd n x z) =
    relativeHurewicz n ({x} : Set X) a
      (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul) at hsource
  change relJ (n + 2) j
      (absoluteHurewiczAdd n y
        (Additive.ofMul (HomotopyGroup.map f hf z.toMul))) =
    relativeHurewicz n ({y} : Set Y) b
      (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
        (HomotopyGroup.map f hf z.toMul)) at htarget
  have hjBij : Function.Bijective (relJ (n + 2) j) := by
    letI : IsIso (relJ (n + 2) j) := isIso_relJ_singleton n y
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  apply hjBij.injective
  calc
    relJ (n + 2) j
        (HgrpMap (n + 2) (TopCat.ofHom f) (absoluteHurewiczAdd n x z)) =
        F.hrelMap (n + 2) (relJ (n + 2) i (absoluteHurewiczAdd n x z)) := hJ.symm
    _ = F.hrelMap (n + 2)
        (relativeHurewicz n ({x} : Set X) a
          (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a z.toMul)) := by
      rw [hsource]
    _ = relativeHurewicz n ({y} : Set Y) b
        (RelHomotopyGroup.jStar (n + 2) Y ({y} : Set Y) b
          (HomotopyGroup.map f hf z.toMul)) := hHur
    _ = relJ (n + 2) j
        (absoluteHurewiczAdd n y
          (Additive.ofMul (HomotopyGroup.map f hf z.toMul))) := htarget.symm

/-- If the distinguished subspace is contractible, the relative Hurewicz map in the first
nonvanishing degree is an isomorphism whenever the corresponding absolute Hurewicz map is.

This is a cancellation argument around the preceding square: both absolute-to-relative maps
`j_*` and `j` are isomorphisms for a contractible subspace. -/
theorem IsNConnected.relativeHurewiczAdd_bijective_of_contractibleSubspace
    {n : ℕ} (hX : IsNConnected (n + 1) X) (A : Set X) (a : A)
    [ContractibleSpace A] :
    Function.Bijective (relativeHurewiczAdd n A a) := by
  let i := subIncl (Y := TopCat.of X) A
  have hJ : Function.Bijective (RelHomotopyGroup.jStarHom n X A a) :=
    bijective_jStar_of_subsingleton n a
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) a)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) a)
  let eJ : Additive (π_ (n + 2) X (a : X)) ≃+
      Additive (π_rel (n + 2) X A a) :=
    MulEquiv.toAdditive
      (MulEquiv.ofBijective (RelHomotopyGroup.jStarHom n X A a) hJ)
  have hJAdd : Function.Bijective
      (RelHomotopyGroup.jStarHom n X A a).toAdditive := by
    exact eJ.bijective
  have htop : IsZero (Hgrp (n + 2) (TopCat.of A)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of A) (n + 1)
  have hprev : IsZero (Hgrp (n + 1) (TopCat.of A)) :=
    isZero_Hgrp_of_contractible (X := TopCat.of A) n
  letI : IsIso (relJ (n + 2) i) :=
    isIso_relJ i (n + 1) (htop.eq_zero_of_src _) (hprev.mono _)
  have hRelJ : Function.Bijective (relJ (n + 2) i) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hcomm :
      (fun z => relativeHurewiczAdd n A a
        ((RelHomotopyGroup.jStarHom n X A a).toAdditive z)) =
      fun z => relJ (n + 2) i (absoluteHurewiczAdd n (a : X) z) := by
    funext z
    exact relativeHurewicz_jStar n A a z.toMul
  have hcomp : Function.Bijective
      (relativeHurewiczAdd n A a ∘
        (RelHomotopyGroup.jStarHom n X A a).toAdditive) := by
    change Function.Bijective (fun z => relativeHurewiczAdd n A a
      ((RelHomotopyGroup.jStarHom n X A a).toAdditive z))
    rw [hcomm]
    exact hRelJ.comp (hX.absoluteHurewiczAdd_bijective (a : X))
  exact (Function.Bijective.of_comp_iff _ hJAdd).mp hcomp

end Submission
