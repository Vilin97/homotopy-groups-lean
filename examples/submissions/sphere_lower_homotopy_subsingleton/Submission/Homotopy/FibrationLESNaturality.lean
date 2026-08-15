/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.FibrationLESGroup
import Submission.Homotopy.RelMap

/-!
# Naturality of the long exact sequence of a fibration

A commuting based square between two fibrations gives a map of their fibre pairs.  The
relative-to-base comparison and hence the connecting maps commute with this square.  A final
four-out-of-five lemma transfers bijectivity from the two connecting maps and the fibre map to
the induced map between the base homotopy groups.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

universe u v w x

variable {E : Type u} {B : Type v} {E' : Type w} {B' : Type x}
  [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace E'] [TopologicalSpace B']
  {p : C(E, B)} {p' : C(E', B')} {b : B} {b' : B'}

/-- A commuting based square of total and base maps induces a based map of fibre pairs. -/
def fibrationBasedPairMap
    (e : (⇑p ⁻¹' {b} : Set E)) (e' : (⇑p' ⁻¹' {b'} : Set E'))
    (f : C(E, E')) (g : C(B, B'))
    (hf : f e = e') (hg : g b = b')
    (hsquare : p'.comp f = g.comp p) :
    BasedPairMap (⇑p ⁻¹' {b}) (⇑p' ⁻¹' {b'}) e e' where
  toContinuousMap := f
  mapsTo' := by
    intro z hz
    show p' (f z) = b'
    change p z = b at hz
    have hcomm := ContinuousMap.congr_fun hsquare z
    exact hcomm.trans ((congrArg g hz).trans hg)
  map_basepoint' := hf

/-- Naturality of the relative-to-base comparison for a commuting square of fibrations. -/
theorem pStar_naturality
    (e : (⇑p ⁻¹' {b} : Set E)) (e' : (⇑p' ⁻¹' {b'} : Set E'))
    (f : C(E, E')) (g : C(B, B'))
    (hf : f e = e') (hg : g b = b')
    (hsquare : p'.comp f = g.comp p) (n : ℕ)
    (z : π_rel n E (⇑p ⁻¹' {b}) e) :
    HomotopyGroup.map g hg (pStar e n z) =
      pStar e' n
        (RelHomotopyGroup.map
          (fibrationBasedPairMap e e' f g hf hg hsquare) z) := by
  induction z using Quotient.inductionOn with
  | _ q =>
      rw [pStar_mk, HomotopyGroup.map_mk,
        RelHomotopyGroup.map_mk, pStar_mk]
      apply congrArg (fun r => (⟦r⟧ : π_ n B' b'))
      apply GenLoop.ext
      intro y
      exact ContinuousMap.congr_fun hsquare (q.val y) |>.symm

/-- Naturality of the connecting map in the long exact sequence of a fibration. -/
theorem fibDelta_naturality
    (e : (⇑p ⁻¹' {b} : Set E)) (e' : (⇑p' ⁻¹' {b'} : Set E'))
    (hp : IsSerreFibration p) (hp' : IsSerreFibration p')
    (f : C(E, E')) (g : C(B, B'))
    (hf : f e = e') (hg : g b = b')
    (hsquare : p'.comp f = g.comp p) (n : ℕ)
    (z : π_ (n + 1) B b) :
    HomotopyGroup.map
        (fibrationBasedPairMap e e' f g hf hg hsquare).subspaceMap
        (fibrationBasedPairMap e e' f g hf hg hsquare).subspaceMap_basepoint
        (fibDelta e hp n z) =
      fibDelta e' hp' n (HomotopyGroup.map g hg z) := by
  let F := fibrationBasedPairMap e e' f g hf hg hsquare
  let q := (pStarEquiv e hp n).symm z
  have hq : RelHomotopyGroup.map F q =
      (pStarEquiv e' hp' n).symm (HomotopyGroup.map g hg z) := by
    apply (pStarEquiv e' hp' n).injective
    rw [pStarEquiv_apply, ← pStar_naturality e e' f g hf hg hsquare]
    change HomotopyGroup.map g hg ((pStarEquiv e hp n) q) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change HomotopyGroup.map F.subspaceMap F.subspaceMap_basepoint
      (RelHomotopyGroup.bd n E (⇑p ⁻¹' {b}) e q) =
    RelHomotopyGroup.bd n E' (⇑p' ⁻¹' {b'}) e'
      ((pStarEquiv e' hp' n).symm (HomotopyGroup.map g hg z))
  rw [← RelHomotopyGroup.bd_map F, hq]

/-- If both connecting maps and the induced fibre map are bijective, then so is the map on
the bases in the corresponding homotopy degree. -/
theorem homotopyGroup_map_bijective_of_fibDelta
    (e : (⇑p ⁻¹' {b} : Set E)) (e' : (⇑p' ⁻¹' {b'} : Set E'))
    (hp : IsSerreFibration p) (hp' : IsSerreFibration p')
    (f : C(E, E')) (g : C(B, B'))
    (hf : f e = e') (hg : g b = b')
    (hsquare : p'.comp f = g.comp p) (n : ℕ)
    (hsource : Function.Bijective (fibDelta e hp n))
    (htarget : Function.Bijective (fibDelta e' hp' n))
    (hfibre : Function.Bijective
      (HomotopyGroup.map
        (N := Fin n)
        (fibrationBasedPairMap e e' f g hf hg hsquare).subspaceMap
        (fibrationBasedPairMap e e' f g hf hg hsquare).subspaceMap_basepoint)) :
    Function.Bijective (HomotopyGroup.map g hg :
      π_ (n + 1) B b → π_ (n + 1) B' b') := by
  let F := fibrationBasedPairMap e e' f g hf hg hsquare
  have hnatural (z : π_ (n + 1) B b) :
      HomotopyGroup.map F.subspaceMap F.subspaceMap_basepoint
          (fibDelta e hp n z) =
        fibDelta e' hp' n (HomotopyGroup.map g hg z) :=
    fibDelta_naturality e e' hp hp' f g hf hg hsquare n z
  constructor
  · intro a c hac
    apply hsource.1
    apply hfibre.1
    rw [hnatural a, hnatural c, hac]
  · intro y
    obtain ⟨v, hv⟩ := hfibre.2 (fibDelta e' hp' n y)
    obtain ⟨z, hz⟩ := hsource.2 v
    refine ⟨z, htarget.1 ?_⟩
    rw [← hnatural, hz, hv]

end Submission
