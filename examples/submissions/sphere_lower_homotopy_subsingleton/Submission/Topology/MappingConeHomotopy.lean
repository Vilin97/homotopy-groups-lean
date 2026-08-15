/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Topology.MappingCone
import Submission.WhiteheadTheorem.Exponential
import Submission.WhiteheadTheorem.Shapes.Maps

/-!
# Homotopies of maps of topological mapping cones

A homotopy between two maps under a fixed subspace induces a homotopy between the corresponding
maps of mapping cones.  The construction glues the curried target homotopy to the constant
homotopy on the cone summand.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat
open scoped unitInterval Topology

namespace Submission

universe u

/-- The path-valued map on a mapping cone induced by a target homotopy which is pointwise fixed
on the attaching subspace. -/
noncomputable def topologicalMappingConeMapHomotopyPath
    {A X Y : TopCat.{u}}
    (f : A ⟶ X) (g : A ⟶ Y)
    (x₀ x₁ : X ⟶ Y)
    (H : ContinuousMap.Homotopy x₀.hom x₁.hom)
    (hH : ∀ (t : I) (a : A), H (t, f a) = g a) :
    topologicalMappingCone f ⟶ TopCat.of C(I, topologicalMappingCone g) :=
  pushout.desc
    (TopCat.ofHom
      (((ContinuousMap.Homotopy.refl
        (topologicalMappingConeIncl g).hom).comp H).toContinuousMap.argSwap.curry))
    (TopCat.ofHom
      ((ContinuousMap.Homotopy.refl
        (topologicalMappingConeConeIncl g).hom).toContinuousMap.argSwap.curry)) (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro a
      apply ContinuousMap.ext
      intro t
      change topologicalMappingConeIncl g (H (t, f a)) =
        topologicalMappingConeConeIncl g (topologicalConeBaseIncl A a)
      rw [hH]
      exact ConcreteCategory.congr_hom (topologicalMappingCone_condition g) a)

@[reassoc]
theorem topologicalMappingConeIncl_mapHomotopyPath
    {A X Y : TopCat.{u}}
    (f : A ⟶ X) (g : A ⟶ Y)
    (x₀ x₁ : X ⟶ Y)
    (H : ContinuousMap.Homotopy x₀.hom x₁.hom)
    (hH : ∀ (t : I) (a : A), H (t, f a) = g a) :
    topologicalMappingConeIncl f ≫
        topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH =
      TopCat.ofHom
        (((ContinuousMap.Homotopy.refl
          (topologicalMappingConeIncl g).hom).comp H).toContinuousMap.argSwap.curry) := by
  exact pushout.inl_desc _ _ _

@[reassoc]
theorem topologicalMappingConeConeIncl_mapHomotopyPath
    {A X Y : TopCat.{u}}
    (f : A ⟶ X) (g : A ⟶ Y)
    (x₀ x₁ : X ⟶ Y)
    (H : ContinuousMap.Homotopy x₀.hom x₁.hom)
    (hH : ∀ (t : I) (a : A), H (t, f a) = g a) :
    topologicalMappingConeConeIncl f ≫
        topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH =
      TopCat.ofHom
        ((ContinuousMap.Homotopy.refl
          (topologicalMappingConeConeIncl g).hom).toContinuousMap.argSwap.curry) := by
  exact pushout.inr_desc _ _ _

/-- A homotopy of target maps which is pointwise constant on the common attaching subspace
induces a homotopy of the associated maps of topological mapping cones. -/
noncomputable def topologicalMappingConeMapHomotopy
    {A X Y : TopCat.{u}}
    (f : A ⟶ X) (g : A ⟶ Y)
    (x₀ x₁ : X ⟶ Y)
    (h₀ : f ≫ x₀ = g) (h₁ : f ≫ x₁ = g)
    (H : ContinuousMap.Homotopy x₀.hom x₁.hom)
    (hH : ∀ (t : I) (a : A), H (t, f a) = g a) :
    ContinuousMap.Homotopy
      (topologicalMappingConeMap f g (𝟙 A) x₀ (by simpa using h₀)).hom
      (topologicalMappingConeMap f g (𝟙 A) x₁ (by simpa using h₁)).hom where
  toFun p := topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH p.2 p.1
  continuous_toFun :=
    (topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH).hom.uncurry.continuous.comp
      (continuous_snd.prodMk continuous_fst)
  map_zero_left z := by
    let P := topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH
    have hP : P ≫ PathSpace.eval₀ (topologicalMappingCone g) =
        topologicalMappingConeMap f g (𝟙 A) x₀ (by simpa using h₀) := by
      apply topologicalMappingCone_hom_ext f
      · rw [← Category.assoc,
          topologicalMappingConeIncl_mapHomotopyPath,
          topologicalMappingConeIncl_map]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        change topologicalMappingConeIncl g (H (0, x)) =
          topologicalMappingConeIncl g (x₀ x)
        rw [H.apply_zero]
      · rw [← Category.assoc,
          topologicalMappingConeConeIncl_mapHomotopyPath,
          topologicalMappingConeConeIncl_map, topologicalConeMap_id,
          Category.id_comp]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro c
        rfl
    exact ConcreteCategory.congr_hom hP z
  map_one_left z := by
    let P := topologicalMappingConeMapHomotopyPath f g x₀ x₁ H hH
    have hP : P ≫ PathSpace.evalAt (topologicalMappingCone g) 1 =
        topologicalMappingConeMap f g (𝟙 A) x₁ (by simpa using h₁) := by
      apply topologicalMappingCone_hom_ext f
      · rw [← Category.assoc,
          topologicalMappingConeIncl_mapHomotopyPath,
          topologicalMappingConeIncl_map]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        change topologicalMappingConeIncl g (H (1, x)) =
          topologicalMappingConeIncl g (x₁ x)
        rw [H.apply_one]
      · rw [← Category.assoc,
          topologicalMappingConeConeIncl_mapHomotopyPath,
          topologicalMappingConeConeIncl_map, topologicalConeMap_id,
          Category.id_comp]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro c
        rfl
    exact ConcreteCategory.congr_hom hP z

/-- A homotopy equivalence under a common subspace induces a homotopy equivalence of mapping
cones, provided both inverse-composite homotopies fix that subspace pointwise. -/
noncomputable def topologicalMappingConeHomotopyEquiv
    {A X Y : TopCat.{u}}
    (f : A ⟶ X) (g : A ⟶ Y)
    (x : X ⟶ Y) (y : Y ⟶ X)
    (hfx : f ≫ x = g) (hgy : g ≫ y = f)
    (HX : ContinuousMap.Homotopy (ContinuousMap.id X) (x ≫ y).hom)
    (HY : ContinuousMap.Homotopy (ContinuousMap.id Y) (y ≫ x).hom)
    (hX : ∀ (t : I) (a : A), HX (t, f a) = f a)
    (hY : ∀ (t : I) (a : A), HY (t, g a) = g a) :
    ContinuousMap.HomotopyEquiv (topologicalMappingCone f) (topologicalMappingCone g) where
  toFun := (topologicalMappingConeMap f g (𝟙 A) x (by simpa using hfx)).hom
  invFun := (topologicalMappingConeMap g f (𝟙 A) y (by simpa using hgy)).hom
  left_inv := by
    let H := topologicalMappingConeMapHomotopy f f (𝟙 X) (x ≫ y)
      (by simp) (by rw [← Category.assoc, hfx, hgy]) HX hX
    have hzero :
        (topologicalMappingConeMap f f (𝟙 A) (𝟙 X) (by simp)).hom =
          (ContinuousMap.id (topologicalMappingCone f)) := by
      exact congrArg ConcreteCategory.hom (topologicalMappingConeMap_id f)
    have hone :
        (topologicalMappingConeMap f f (𝟙 A) (x ≫ y)
            (by rw [← Category.assoc, hfx, hgy, Category.id_comp])).hom =
          (topologicalMappingConeMap g f (𝟙 A) y (by simpa using hgy)).hom.comp
            (topologicalMappingConeMap f g (𝟙 A) x (by simpa using hfx)).hom := by
      have hcomp := topologicalMappingConeMap_comp f g f
        (𝟙 A) (𝟙 A) x y (by simpa using hfx) (by simpa using hgy)
      calc
        _ = (topologicalMappingConeMap f g (𝟙 A) x (by simpa using hfx) ≫
              topologicalMappingConeMap g f (𝟙 A) y (by simpa using hgy)).hom :=
          congrArg ConcreteCategory.hom (by simpa using hcomp)
        _ = _ := rfl
    exact ⟨(H.cast hzero hone).symm⟩
  right_inv := by
    let H := topologicalMappingConeMapHomotopy g g (𝟙 Y) (y ≫ x)
      (by simp) (by rw [← Category.assoc, hgy, hfx]) HY hY
    have hzero :
        (topologicalMappingConeMap g g (𝟙 A) (𝟙 Y) (by simp)).hom =
          (ContinuousMap.id (topologicalMappingCone g)) := by
      exact congrArg ConcreteCategory.hom (topologicalMappingConeMap_id g)
    have hone :
        (topologicalMappingConeMap g g (𝟙 A) (y ≫ x)
            (by rw [← Category.assoc, hgy, hfx, Category.id_comp])).hom =
          (topologicalMappingConeMap f g (𝟙 A) x (by simpa using hfx)).hom.comp
            (topologicalMappingConeMap g f (𝟙 A) y (by simpa using hgy)).hom := by
      have hcomp := topologicalMappingConeMap_comp g f g
        (𝟙 A) (𝟙 A) y x (by simpa using hgy) (by simpa using hfx)
      calc
        _ = (topologicalMappingConeMap g f (𝟙 A) y (by simpa using hgy) ≫
              topologicalMappingConeMap f g (𝟙 A) x (by simpa using hfx)).hom :=
          congrArg ConcreteCategory.hom (by simpa using hcomp)
        _ = _ := rfl
    exact ⟨(H.cast hzero hone).symm⟩

end Submission
