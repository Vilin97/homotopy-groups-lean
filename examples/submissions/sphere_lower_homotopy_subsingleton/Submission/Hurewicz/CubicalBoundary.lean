/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.RelativeBoundary
import Submission.Hurewicz.RelativeAdditivity
import Submission.Hurewicz.AbsoluteIsomorphism
import Submission.Homotopy.HomotopyLesTools
import Submission.Homology.LesTools
import Submission.WhiteheadTheorem.Shapes.CubeBoundaryMap

/-!
# The cubical boundary extension of a generalized loop

A relative generalized loop is constant on the boundary jar.  Consequently, its restriction
to the whole boundary of the cube is determined by its top face: it is the given ordinary
generalized loop on the top face and the constant map on the bottom face and all sides.

This file constructs that boundary extension independently of a filling and identifies it with
the boundary restriction of every relative generalized loop.  Combining the identification with
`relativeHurewicz_mk_boundary` isolates the remaining universal orientation comparison between
the cubical boundary class and the ordinary Hurewicz class of the top face.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace TopCat.cubeBoundary

universe u

variable {n : ℕ} {Z : TopCat.{u}}
variable (f01 : unitInterval.zeroOne → (TopCat.cube.{u} n ⟶ Z))
variable (fs : TopCat.of (I × TopCat.cubeBoundary.{u} n) ⟶ Z)

/-- Evaluation of `mapOfBotTopSides` at a point of its bottom member. -/
theorem mapOfBotTopSides_apply_of_mem_bot
    (h : ∀ t y, f01 t (TopCat.cubeBoundaryIncl _ y) =
      fs ⟨unitInterval.zeroOneIncl t, y⟩)
    (y : TopCat.cubeBoundary (n + 1))
    (hy : y ∈ botOrTop n 0) :
    mapOfBotTopSides f01 fs h y =
      f01 0 ⟨(Cube.splitAtLast y.down.val).snd⟩ := by
  have hy' : y ∈ botTopSidesCover n (0 : Fin 3) := hy
  have hlift := ContinuousMap.liftCoverClosed_coe'
    (botTopSidesCover n) (mapVecOfBotTopSides f01 fs)
    (mapVecOfBotTopSides_compatible f01 fs h)
    (botTopSidesCover_cover n) (botTopSidesCover_closed n) y hy'
  change (ContinuousMap.liftCoverClosed (botTopSidesCover n)
      (mapVecOfBotTopSides f01 fs) (mapVecOfBotTopSides_compatible f01 fs h)
      (botTopSidesCover_cover n) (botTopSidesCover_closed n)) y = _
  rw [hlift]
  rfl

/-- Evaluation of `mapOfBotTopSides` at a point of its sides member. -/
theorem mapOfBotTopSides_apply_of_mem_sides
    (h : ∀ t y, f01 t (TopCat.cubeBoundaryIncl _ y) =
      fs ⟨unitInterval.zeroOneIncl t, y⟩)
    (y : TopCat.cubeBoundary (n + 1))
    (hy : y ∈ sides n) :
    mapOfBotTopSides f01 fs h y =
      fs ⟨(Cube.splitAtLast y.down.val).fst,
        ⟨(Cube.splitAtLast y.down.val).snd,
          splitAtLast_snd_mem_boundary_of_mem_sides hy⟩⟩ := by
  have hy' : y ∈ botTopSidesCover n (2 : Fin 3) := hy
  have hlift := ContinuousMap.liftCoverClosed_coe'
    (botTopSidesCover n) (mapVecOfBotTopSides f01 fs)
    (mapVecOfBotTopSides_compatible f01 fs h)
    (botTopSidesCover_cover n) (botTopSidesCover_closed n) y hy'
  change (ContinuousMap.liftCoverClosed (botTopSidesCover n)
      (mapVecOfBotTopSides f01 fs) (mapVecOfBotTopSides_compatible f01 fs h)
      (botTopSidesCover_cover n) (botTopSidesCover_closed n)) y = _
  rw [hlift]
  rfl

end TopCat.cubeBoundary

namespace Submission

/-- Insert the unlifted cube boundary used by singular homology into the universe-lifted cube
boundary used by the closed-cover gluing construction. -/
def cubeBoundaryULiftHom (n : ℕ) :
    TopCat.of (∂I^n) ⟶ TopCat.cubeBoundary n :=
  TopCat.ofHom ⟨ULift.up, continuous_uliftUp⟩

namespace GenLoop

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y₀ : Y}

/-- The bottom and top face maps used in the cubical boundary extension: the bottom is constant
and the top is the given generalized loop. -/
def boundaryFaceMap (q : Ω^ (Fin n) X x) (t : unitInterval.zeroOne) :
    TopCat.cube n ⟶ TopCat.of X :=
  if t = 0 then
    TopCat.ofHom (ContinuousMap.const _ x)
  else
    TopCat.ofHom (q.val.comp ⟨ULift.down, continuous_uliftDown⟩)

/-- The side map used in the cubical boundary extension; it is constantly the basepoint. -/
def boundarySideMap (_q : Ω^ (Fin n) X x) :
    TopCat.of (I × TopCat.cubeBoundary n) ⟶ TopCat.of X :=
  TopCat.ofHom (ContinuousMap.const _ x)

theorem boundaryFaceSide_compatible (q : Ω^ (Fin n) X x) :
    ∀ t y,
      boundaryFaceMap q t (TopCat.cubeBoundaryIncl n y) =
        boundarySideMap q ⟨unitInterval.zeroOneIncl t, y⟩ := by
  intro t y
  obtain rfl | rfl := unitInterval.zeroOne.eq_zero_or_eq_one t
  · rw [boundaryFaceMap, if_pos rfl]
    rfl
  · have h10 : (1 : unitInterval.zeroOne) ≠ 0 := by
      intro h
      have hv : (1 : ℝ) = 0 := congrArg (fun t : unitInterval.zeroOne => t.1) h
      norm_num at hv
    rw [boundaryFaceMap, if_neg h10]
    change q.val y.down.val = x
    exact q.property y.down.val y.down.property

/-- The universe-lifted form of the cubical boundary extension used by the closed-cover gluing
construction. -/
noncomputable def cubicalBoundaryExtensionLifted (q : Ω^ (Fin n) X x) :
    TopCat.cubeBoundary (n + 1) ⟶ TopCat.of X :=
  TopCat.cubeBoundary.mapOfBotTopSides
    (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q)

/-- Extend a generalized `n`-loop to the boundary of the `(n+1)`-cube by putting it on the top
face and using the constant map on the boundary jar. -/
noncomputable def cubicalBoundaryExtension (q : Ω^ (Fin n) X x) :
    TopCat.of (∂I^(n + 1)) ⟶ TopCat.of X :=
  cubeBoundaryULiftHom (n + 1) ≫ cubicalBoundaryExtensionLifted q

/-- On the top face, the cubical boundary extension is the original generalized loop. -/
@[simp]
theorem cubicalBoundaryExtension_inclToTop (q : Ω^ (Fin n) X x) (y : I^Fin n) :
    cubicalBoundaryExtension q ⟨Cube.inclToTop y, Cube.inclToTop.mem_boundary y⟩ = q y := by
  have htop := ConcreteCategory.congr_hom
    (TopCat.cubeBoundary.cubeInclToBotOrTop_mapOfBotTopSides
      (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q) 1)
    (⟨y⟩ : TopCat.cube n)
  change (TopCat.cubeBoundary.mapOfBotTopSides
      (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q))
      (TopCat.cubeBoundary.cubeInclToBotOrTop 1 ⟨y⟩) =
    boundaryFaceMap q 1 ⟨y⟩ at htop
  have h10 : (1 : unitInterval.zeroOne) ≠ 0 := by
    intro h
    have hv : (1 : ℝ) = 0 := congrArg (fun t : unitInterval.zeroOne => t.1) h
    norm_num at hv
  rw [boundaryFaceMap, if_neg h10] at htop
  exact htop

/-- On the boundary jar, the cubical boundary extension is constantly the basepoint. -/
@[simp]
theorem cubicalBoundaryExtension_boundaryJar (q : Ω^ (Fin n) X x)
    (y : I^Fin (n + 1)) (hy : y ∈ ⊔I^(n + 1)) :
    cubicalBoundaryExtension q
        ⟨y, Cube.boundaryJar_subset_boundary (n + 1) hy⟩ = x := by
  let yu : TopCat.cubeBoundary (n + 1) :=
    ⟨⟨y, Cube.boundaryJar_subset_boundary (n + 1) hy⟩⟩
  change (TopCat.cubeBoundary.mapOfBotTopSides
      (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q)) yu = x
  rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with hbot | hsides
  · have hybot : yu ∈ TopCat.cubeBoundary.botOrTop n 0 := by
      change y (Fin.last n) = 0
      simpa only [Cube.splitAtLast_fst_eq] using hbot
    rw [TopCat.cubeBoundary.mapOfBotTopSides_apply_of_mem_bot
      (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q) yu hybot]
    rw [boundaryFaceMap, if_pos rfl]
    rfl
  · have hyside : yu ∈ TopCat.cubeBoundary.sides n := by
      obtain ⟨i, hi⟩ := hsides
      refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
      simpa only [Cube.splitAtLast_snd_apply_eq] using hi
    rw [TopCat.cubeBoundary.mapOfBotTopSides_apply_of_mem_sides
      (boundaryFaceMap q) (boundarySideMap q) (boundaryFaceSide_compatible q) yu hyside]
    rfl

/-- Cubical boundary extension commutes with postcomposition by a based map. -/
theorem cubicalBoundaryExtension_map (f : C(X, Y)) (hf : f x = y₀)
    (q : Ω^ (Fin n) X x) :
    cubicalBoundaryExtension (GenLoop.map f hf q) =
      cubicalBoundaryExtension q ≫ TopCat.ofHom f := by
  ext z
  change cubicalBoundaryExtension (GenLoop.map f hf q) z =
    f (cubicalBoundaryExtension q z)
  obtain ⟨u, hu⟩ := z
  rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary u hu with hlid | hjar
  · have huTop : u = Cube.inclToTop (Cube.splitAtLast u).snd := by
      apply Cube.splitAtLast.injective
      rw [Cube.splitAtLast_inclToTop_eq]
      apply Prod.ext
      · change u (Fin.last n) = 1 at hlid
        simpa only [Cube.splitAtLast_fst_eq] using hlid
      · rfl
    have hzTop : (⟨u, hu⟩ : ∂I^(n + 1)) =
        ⟨Cube.inclToTop (Cube.splitAtLast u).snd,
          Cube.inclToTop.mem_boundary (Cube.splitAtLast u).snd⟩ :=
      Subtype.ext huTop
    rw [hzTop, cubicalBoundaryExtension_inclToTop,
      cubicalBoundaryExtension_inclToTop]
    rfl
  · rw [cubicalBoundaryExtension_boundaryJar (GenLoop.map f hf q) u hjar,
      cubicalBoundaryExtension_boundaryJar q u hjar]
    exact hf.symm

/-- The homology class obtained by evaluating the oriented boundary of the `(n+2)`-cube on the
canonical boundary extension of an `(n+1)`-dimensional generalized loop. -/
noncomputable def cubicalBoundaryHurewicz (n : ℕ) (q : Ω^ (Fin (n + 1)) X x) :
    Hgrp (n + 1) (TopCat.of X) :=
  HgrpMap (n + 1) (cubicalBoundaryExtension q) (cubeBoundaryFundamentalClass n)

/-- The cubical boundary Hurewicz class is natural under based maps. -/
theorem cubicalBoundaryHurewicz_map (n : ℕ) (f : C(X, Y)) (hf : f x = y₀)
    (q : Ω^ (Fin (n + 1)) X x) :
    cubicalBoundaryHurewicz n (GenLoop.map f hf q) =
      HgrpMap (n + 1) (TopCat.ofHom f) (cubicalBoundaryHurewicz n q) := by
  rw [cubicalBoundaryHurewicz, cubicalBoundaryHurewicz,
    cubicalBoundaryExtension_map, HgrpMap_comp]
  rfl

end GenLoop

namespace RelGenLoop

variable {n : ℕ} {X : Type} [TopologicalSpace X] {A : Set X} {a : A}

/-- The boundary restriction of a relative generalized loop is the canonical cubical boundary
extension of its top face. -/
theorem pairMap_subspaceHom_eq_cubicalBoundaryExtension
    (p : RelGenLoop (n + 1) X A a) :
    (pairMap p).subspaceHom =
      GenLoop.cubicalBoundaryExtension (RelHomotopyGroup.bdGen p) := by
  ext z
  obtain ⟨y, hy⟩ := z
  rcases Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary y hy with hlid | hjar
  · have hyTop : y = Cube.inclToTop (Cube.splitAtLast y).snd := by
      apply Cube.splitAtLast.injective
      rw [Cube.splitAtLast_inclToTop_eq]
      apply Prod.ext
      · change y (Fin.last n) = 1 at hlid
        simpa only [Cube.splitAtLast_fst_eq] using hlid
      · rfl
    have hzTop : (⟨y, hy⟩ : ∂I^(n + 1)) =
        ⟨Cube.inclToTop (Cube.splitAtLast y).snd,
          Cube.inclToTop.mem_boundary (Cube.splitAtLast y).snd⟩ :=
      Subtype.ext hyTop
    rw [hzTop, GenLoop.cubicalBoundaryExtension_inclToTop]
    rfl
  · rw [GenLoop.cubicalBoundaryExtension_boundaryJar
      (RelHomotopyGroup.bdGen p) y hjar]
    exact p.property.2 y hjar

end RelGenLoop

/-- After applying the homology boundary map, relative Hurewicz is exactly the cubical boundary
Hurewicz class of the top face.  No connectivity assumption is needed. -/
theorem relativeHurewicz_mk_boundary_cubical (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} {a : A}
    (p : RelGenLoop (n + 2) X A a) :
    relδ (n + 1) (subIncl (Y := TopCat.of X) A)
        (relativeHurewicz n A a ⟦p⟧) =
      GenLoop.cubicalBoundaryHurewicz n (RelHomotopyGroup.bdGen p) := by
  rw [relativeHurewicz_mk_boundary]
  change HgrpMap (n + 1) (RelGenLoop.pairMap p).subspaceHom
      (cubeBoundaryFundamentalClass n) = _
  rw [RelGenLoop.pairMap_subspaceHom_eq_cubicalBoundaryExtension]
  rfl

/-- Cancellation around the homotopy and homology boundary maps.  If both boundary maps are
bijective and the cubical boundary evaluator agrees on representatives with any bijection
`g : π_(n+1)(A) → H_(n+1)(A)`, then relative Hurewicz is bijective.

This formulation separates the formal long-exact-sequence argument from the one universal
geometric input: the value of the chosen cubical boundary fundamental class. -/
theorem relativeHurewiczAdd_bijective_of_boundary_comparison (n : ℕ)
    {X : Type} [TopologicalSpace X] {A : Set X} (a : A)
    (g : Additive (π_ (n + 1) A a) →
      (Hgrp (n + 1) (TopCat.of A) : Type))
    (hbd : Function.Bijective
      (RelHomotopyGroup.bdHom n X A a).toAdditive)
    (hδ : Function.Bijective
      (relδ (n + 1) (subIncl (Y := TopCat.of X) A)))
    (hg : Function.Bijective g)
    (hcompare : ∀ q : Ω^ (Fin (n + 1)) A a,
      GenLoop.cubicalBoundaryHurewicz n q = g (Additive.ofMul (⟦q⟧ : π_ (n + 1) A a))) :
    Function.Bijective (relativeHurewiczAdd n A a) := by
  let bdAdd := (RelHomotopyGroup.bdHom n X A a).toAdditive
  let δ := relδ (n + 1) (subIncl (Y := TopCat.of X) A)
  let hrel := relativeHurewiczAdd n A a
  have hcomm : (δ ∘ hrel) = (g ∘ bdAdd) := by
    funext z
    obtain ⟨p, hp⟩ := Quotient.exists_rep z.toMul
    have hz : z = Additive.ofMul (⟦p⟧ : π_rel (n + 2) X A a) := by
      apply Additive.toMul.injective
      exact hp.symm
    subst z
    change relδ (n + 1) (subIncl (Y := TopCat.of X) A)
        (relativeHurewiczAdd n A a (Additive.ofMul ⟦p⟧)) =
      g (Additive.ofMul (RelHomotopyGroup.bdHom n X A a ⟦p⟧))
    rw [relativeHurewiczAdd_ofMul, relativeHurewicz_mk_boundary_cubical]
    change GenLoop.cubicalBoundaryHurewicz n (RelHomotopyGroup.bdGen p) =
      g (Additive.ofMul
        (RelHomotopyGroup.bd (n + 1) X A a (⟦p⟧ : π_rel (n + 2) X A a)))
    rw [RelHomotopyGroup.bd_mk]
    exact hcompare (RelHomotopyGroup.bdGen p)
  have hcomp : Function.Bijective (δ ∘ hrel) := by
    rw [hcomm]
    exact hg.comp hbd
  exact (Function.Bijective.of_comp_iff' hδ hrel).mp hcomp

namespace IsNConnected

/-- Contractible-ambient form of the first relative Hurewicz theorem, reduced to the universal
cubical boundary comparison.  The shift by one keeps the absolute Hurewicz map in degree at
least two; the fundamental-group case remains a separate low-dimensional comparison. -/
theorem relativeHurewiczAdd_bijective_of_contractibleAmbient
    {n : ℕ} {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    {A : Set X} (hA : IsNConnected (n + 1) A) (a : A)
    (hcompare : ∀ q : Ω^ (Fin (n + 2)) A a,
      GenLoop.cubicalBoundaryHurewicz (n + 1) q =
        absoluteHurewiczAdd n a (Additive.ofMul (⟦q⟧ : π_ (n + 2) A a))) :
    Function.Bijective (relativeHurewiczAdd (n + 1) A a) := by
  refine relativeHurewiczAdd_bijective_of_boundary_comparison (n + 1) a
    (absoluteHurewiczAdd n a) ?_ ?_ (hA.absoluteHurewiczAdd_bijective a) hcompare
  · change Function.Bijective (RelHomotopyGroup.bd (n + 2) X A a)
    exact bijective_bd_of_subsingleton (n + 1) a
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 3)) (a : X))
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) (a : X))
  · let i := subIncl (Y := TopCat.of X) A
    letI : IsIso (relδ (n + 2) i) :=
      isIso_relδ i (n + 2)
        (isZero_Hgrp_of_contractible (X := TopCat.of X) (n + 2))
        (isZero_Hgrp_of_contractible (X := TopCat.of X) (n + 1))
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end IsNConnected

end Submission
