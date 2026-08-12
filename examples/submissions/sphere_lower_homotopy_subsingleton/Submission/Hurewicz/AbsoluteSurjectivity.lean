/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.RelativeSurjectivity

/-!
# The absolute Hurewicz homomorphism in the first nonvanishing degree

For a singleton point pair, both maps from the absolute group to the corresponding relative group
are isomorphisms in degree at least two.  Transporting the maintained relative Hurewicz
homomorphism through those maps gives the absolute Hurewicz homomorphism.  Relative
first-nonvanishing surjectivity then immediately implies absolute surjectivity.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X]

/-- For a singleton point pair, the map from absolute to relative homology is an isomorphism in
every degree at least two. -/
theorem isIso_relJ_singleton (n : ℕ) (x : X) :
    IsIso (relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X))) := by
  let htop : IsZero (Hgrp (n + 2) (TopCat.of ({x} : Set X))) := by
    simpa [Nat.add_assoc] using
      (isZero_Hgrp_of_contractible (X := TopCat.of ({x} : Set X)) (n + 1))
  let hprev : IsZero (Hgrp (n + 1) (TopCat.of ({x} : Set X))) :=
    isZero_Hgrp_of_contractible (X := TopCat.of ({x} : Set X)) n
  exact isIso_relJ (subIncl (Y := TopCat.of X) ({x} : Set X)) (n + 1)
    (htop.eq_zero_of_src _) (hprev.mono _)

/-- Absolute homology and singleton-pair relative homology agree in every degree at least two. -/
noncomputable def homologyIsoRelSingleton (n : ℕ) (x : X) :
    Hgrp (n + 2) (TopCat.of X) ≅
      HrelSet (Y := TopCat.of X) (n + 2) ({x} : Set X) := by
  letI : IsIso (relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X))) :=
    isIso_relJ_singleton n x
  exact asIso (relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X)))

@[simp]
theorem homologyIsoRelSingleton_hom_apply (n : ℕ) (x : X)
    (z : Hgrp (n + 2) (TopCat.of X)) :
    (homologyIsoRelSingleton n x).hom z =
      relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X)) z :=
  rfl

/-- Absolute homotopy and singleton-pair relative homotopy agree in every degree at least two. -/
noncomputable def homotopyGroupMulEquivRelSingleton (n : ℕ) (x : X) :
    π_ (n + 2) X x ≃* π_rel (n + 2) X ({x} : Set X) ⟨x, rfl⟩ :=
  MulEquiv.ofBijective
    (RelHomotopyGroup.jStarHom n X ({x} : Set X) ⟨x, rfl⟩)
    (bijective_jStar_of_subsingleton n (⟨x, rfl⟩ : ({x} : Set X))
      (subsingleton_homotopyGroup_of_subsingleton (N := Fin (n + 2))
        (⟨x, rfl⟩ : ({x} : Set X)))
      (subsingleton_homotopyGroup_of_subsingleton (N := Fin (n + 1))
        (⟨x, rfl⟩ : ({x} : Set X))))

@[simp]
theorem homotopyGroupMulEquivRelSingleton_apply (n : ℕ) (x : X)
    (z : π_ (n + 2) X x) :
    homotopyGroupMulEquivRelSingleton n x z =
      RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) ⟨x, rfl⟩ z :=
  by
    simp only [homotopyGroupMulEquivRelSingleton, MulEquiv.ofBijective_apply]
    rfl

/-- The higher absolute Hurewicz homomorphism, obtained from the relative Hurewicz homomorphism
of the singleton point pair. -/
noncomputable def absoluteHurewiczAdd (n : ℕ) (x : X) :
    Additive (π_ (n + 2) X x) →+ (Hgrp (n + 2) (TopCat.of X) : Type) := by
  let a : ({x} : Set X) := ⟨x, rfl⟩
  exact (homologyIsoRelSingleton n x).inv.hom.comp
    ((relativeHurewiczAdd n ({x} : Set X) a).comp
      (RelHomotopyGroup.jStarHom n X ({x} : Set X) a).toAdditive)

/-- Applying the relative projection after the absolute Hurewicz map recovers the relative
Hurewicz value of the image under `j_*`. -/
theorem relJ_absoluteHurewiczAdd (n : ℕ) (x : X)
    (z : Additive (π_ (n + 2) X x)) :
    relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X))
        (absoluteHurewiczAdd n x z) =
      relativeHurewiczAdd n ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))
        ((RelHomotopyGroup.jStarHom n X ({x} : Set X)
          (⟨x, rfl⟩ : ({x} : Set X))).toAdditive z) := by
  let i := subIncl (Y := TopCat.of X) ({x} : Set X)
  let a : ({x} : Set X) := ⟨x, rfl⟩
  change relJ (n + 2) i
      ((homologyIsoRelSingleton n x).inv
        (relativeHurewiczAdd n ({x} : Set X) a
          ((RelHomotopyGroup.jStarHom n X ({x} : Set X) a).toAdditive z))) =
    relativeHurewiczAdd n ({x} : Set X) a
      ((RelHomotopyGroup.jStarHom n X ({x} : Set X) a).toAdditive z)
  have h := ConcreteCategory.congr_hom (homologyIsoRelSingleton n x).inv_hom_id
    (relativeHurewiczAdd n ({x} : Set X) a
      ((RelHomotopyGroup.jStarHom n X ({x} : Set X) a).toAdditive z))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h

namespace IsNConnected

/-- **Surjectivity of the absolute Hurewicz homomorphism in the first potentially nonzero
degree.** -/
theorem absoluteHurewiczAdd_surjective
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Surjective (absoluteHurewiczAdd n x) := by
  intro z
  let i := subIncl (Y := TopCat.of X) ({x} : Set X)
  let a : ({x} : Set X) := ⟨x, rfl⟩
  letI : IsIso (relJ (n + 2) i) := isIso_relJ_singleton n x
  obtain ⟨y, hy⟩ := hX.relativeHurewiczAdd_surjective x (relJ (n + 2) i z)
  have hj : Function.Bijective (RelHomotopyGroup.jStarHom n X ({x} : Set X) a) :=
    bijective_jStar_of_subsingleton n a
      (subsingleton_homotopyGroup_of_subsingleton a)
      (subsingleton_homotopyGroup_of_subsingleton a)
  obtain ⟨q, hq⟩ := hj.2 y.toMul
  refine ⟨Additive.ofMul q, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (relJ (n + 2) i)).1 inferInstance
  rw [relJ_absoluteHurewiczAdd]
  change relativeHurewiczAdd n ({x} : Set X) a
      (Additive.ofMul (RelHomotopyGroup.jStarHom n X ({x} : Set X) a q)) =
    relJ (n + 2) i z
  rw [hq]
  exact hy

end IsNConnected

end Submission
