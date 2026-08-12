/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.AbsoluteSurjectivity
import Submission.Hurewicz.RelativeSimplicialDescent
import Submission.Hurewicz.SimplexCubeOrientation

/-!
# The absolute Hurewicz isomorphism in the first nonvanishing degree

The relative stick-class evaluator applied to the Hurewicz image of a cubical loop returns that
loop after two harmless global coordinate changes: the inverse cube--simplex orientation unit and
the injective stick sphere reparameterization.  This calculation makes the absolute Hurewicz map
injective.  Combined with first-nonvanishing surjectivity, it gives the Hurewicz isomorphism.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace Submission

variable {n : ℕ} {X : Type} [TopologicalSpace X]

namespace NormalizedSimplex

/-- The relative generalized-loop class of `ofGenLoop p` is the image of `p` under `j_*`. -/
theorem ofGenLoop_toRelGenLoop_class {x : X} (p : Ω^ (Fin (n + 2)) X x) :
    (⟦(ofGenLoop p).toRelGenLoop⟧ :
        π_rel (n + 2) X ({x} : Set X) (⟨x, rfl⟩ : ({x} : Set X))) =
      RelHomotopyGroup.jStar (n + 2) X ({x} : Set X)
        (⟨x, rfl⟩ : ({x} : Set X)) (⟦p⟧ : π_ (n + 2) X x) := by
  rw [RelHomotopyGroup.jStar_mk]
  apply congrArg Quotient.mk'
  change RelHomotopyGroup.jStarGen (A := ({x} : Set X))
      (a := (⟨x, rfl⟩ : ({x} : Set X))) (ofGenLoop p).toGenLoop =
    RelHomotopyGroup.jStarGen (A := ({x} : Set X))
      (a := (⟨x, rfl⟩ : ({x} : Set X))) p
  rw [ofGenLoop_toGenLoop]

end NormalizedSimplex

namespace IsNConnected

/-- On a representative generalized loop, the normalized inverse candidate after the absolute
Hurewicz map is the stick reparameterized class, multiplied by the inverse global orientation
unit. -/
theorem normalizedStickHomologyMap_absoluteHurewiczAdd_ofMul
    (hX : IsNConnected (n + 1) X) (x : X)
    (p : Ω^ (Fin (n + 2)) X x) :
    hX.normalizedStickHomologyMap x
        (absoluteHurewiczAdd n x
          (Additive.ofMul (⟦p⟧ : π_ (n + 2) X x))) =
      (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
        Additive.ofMul
          (stickReparamClass (n + 1) (⟦p⟧ : π_ (n + 2) X x)) := by
  let s : NormalizedSimplex n X x := NormalizedSimplex.ofGenLoop p
  let a : ({x} : Set X) := ⟨x, rfl⟩
  have hj :
      relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X))
          (absoluteHurewiczAdd n x
            (Additive.ofMul (⟦p⟧ : π_ (n + 2) X x))) =
        relativeHurewicz n ({x} : Set X) a
          (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) a) := by
    rw [relJ_absoluteHurewiczAdd]
    change relativeHurewicz n ({x} : Set X) a
        (RelHomotopyGroup.jStar (n + 2) X ({x} : Set X) a
          (⟦p⟧ : π_ (n + 2) X x)) = _
    rw [← NormalizedSimplex.ofGenLoop_toRelGenLoop_class]
  calc
    hX.normalizedStickHomologyMap x
        (absoluteHurewiczAdd n x
          (Additive.ofMul (⟦p⟧ : π_ (n + 2) X x))) =
      hX.normalizedStickRelativeHomologyMap x
        (relJ (n + 2) (subIncl (Y := TopCat.of X) ({x} : Set X))
          (absoluteHurewiczAdd n x
            (Additive.ofMul (⟦p⟧ : π_ (n + 2) X x)))) :=
      (hX.normalizedStickRelativeHomologyMap_relJ x _).symm
    _ = hX.normalizedStickRelativeHomologyMap x
        (relativeHurewicz n ({x} : Set X) a
          (⟦s.toRelGenLoop⟧ : π_rel (n + 2) X ({x} : Set X) a)) := by rw [hj]
    _ = hX.normalizedStickRelativeHomologyMap x
        ((↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) • s.relativeClass) := by
      rw [s.relativeHurewicz_toRelGenLoop]
    _ = (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
        hX.normalizedStickRelativeHomologyMap x s.relativeClass := by
      rw [map_zsmul]
    _ = (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
        Additive.ofMul (stickReparamClass (n + 1) s.homotopyClass) := by
      rw [hX.normalizedStickRelativeHomologyMap_relativeClass_eq_stickReparam]
    _ = (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
        Additive.ofMul
          (stickReparamClass (n + 1) (⟦p⟧ : π_ (n + 2) X x)) := by
      dsimp only [s]
      simpa only [Nat.add_assoc, Nat.reduceAdd] using congrArg
        (fun q => (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
          Additive.ofMul (stickReparamClass (n + 1) q))
        (NormalizedSimplex.ofGenLoop_homotopyClass p)

/-- The inverse calculation for an arbitrary additively tagged homotopy class. -/
theorem normalizedStickHomologyMap_absoluteHurewiczAdd
    (hX : IsNConnected (n + 1) X) (x : X)
    (z : Additive (π_ (n + 2) X x)) :
    hX.normalizedStickHomologyMap x (absoluteHurewiczAdd n x z) =
      (↑(cubeSimplexOrientationUnit n)⁻¹ : ℤ) •
        Additive.ofMul (stickReparamClass (n + 1) z.toMul) := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep z.toMul
  have hz : z = Additive.ofMul (⟦p⟧ : π_ (n + 2) X x) := by
    apply Additive.toMul.injective
    exact hp.symm
  rw [hz]
  exact hX.normalizedStickHomologyMap_absoluteHurewiczAdd_ofMul x p

/-- **Injectivity of the absolute Hurewicz homomorphism in the first potentially nonzero
degree.** -/
theorem absoluteHurewiczAdd_injective
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Injective (absoluteHurewiczAdd n x) := by
  intro a b hab
  have h := congrArg (fun q => hX.normalizedStickHomologyMap x q) hab
  rw [hX.normalizedStickHomologyMap_absoluteHurewiczAdd x,
    hX.normalizedStickHomologyMap_absoluteHurewiczAdd x] at h
  let u := cubeSimplexOrientationUnit n
  change (↑u⁻¹ : ℤ) •
      Additive.ofMul (stickReparamClass (n + 1) a.toMul) =
    (↑u⁻¹ : ℤ) •
      Additive.ofMul (stickReparamClass (n + 1) b.toMul) at h
  have hcancel := congrArg (fun q : Additive (π_ (n + 2) X x) =>
    (↑u : ℤ) • q) h
  have hu : (↑u : ℤ) * (↑u⁻¹ : ℤ) = 1 := by
    rw [← Units.val_mul]
    simp
  have hreparam :
      Additive.ofMul (stickReparamClass (n + 1) a.toMul) =
        Additive.ofMul (stickReparamClass (n + 1) b.toMul) := by
    simpa only [smul_smul, hu, one_smul] using hcancel
  apply Additive.toMul.injective
  apply stickReparamClass_injective (X := X) (x := x) (n + 1)
  exact Additive.ofMul.injective hreparam

/-- The absolute Hurewicz homomorphism in the first potentially nonzero degree is bijective. -/
theorem absoluteHurewiczAdd_bijective
    (hX : IsNConnected (n + 1) X) (x : X) :
    Function.Bijective (absoluteHurewiczAdd n x) :=
  ⟨hX.absoluteHurewiczAdd_injective x, hX.absoluteHurewiczAdd_surjective x⟩

/-- **The absolute Hurewicz isomorphism in the first potentially nonzero degree.** -/
noncomputable def absoluteHurewiczAddEquiv
    (hX : IsNConnected (n + 1) X) (x : X) :
    Additive (π_ (n + 2) X x) ≃+ (Hgrp (n + 2) (TopCat.of X) : Type) :=
  AddEquiv.ofBijective (absoluteHurewiczAdd n x) (hX.absoluteHurewiczAdd_bijective x)

@[simp]
theorem absoluteHurewiczAddEquiv_apply
    (hX : IsNConnected (n + 1) X) (x : X)
    (z : Additive (π_ (n + 2) X x)) :
    hX.absoluteHurewiczAddEquiv x z = absoluteHurewiczAdd n x z :=
  rfl

end IsNConnected

end Submission
