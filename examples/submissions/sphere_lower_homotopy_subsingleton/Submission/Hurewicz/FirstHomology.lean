/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.VanishingSorries
import Submission.Homology.Point
import Submission.ForMathlib.HomotopyGroup.Contractible

/-!
# The first homology of a simply connected space vanishes

`H₁(X) = 0` whenever `X` is path connected and `π₁(X) = 0`.  This is the degree-one, unbased
shadow of the Hurewicz theorem, and it is a two-line consequence of the bounded compression
theorem of `Submission/Hurewicz/VanishingSorries.lean`: the inclusion of a basepoint
`pt → X` is a `1`-equivalence, hence an epimorphism on `H₁` — and `H₁(pt) = 0`.

Note that only `Submission.epi_HgrpMap_of_isNEquiv` (degrees `≤ M`) is strong enough here.
`Submission.isIso_HgrpMap_of_isNEquiv` needs `n < M`, and the basepoint inclusion is *not* a
`2`-equivalence: nothing is assumed about `π₂(X)`.

## Main results

* `Submission.isNEquiv_one_pointIncl` — the basepoint inclusion of a path-connected, simply
  connected space is a `1`-equivalence;
* `Submission.isZero_hgrp_one_of_subsingleton_piOne` — `H₁(X) = 0`.
-/

open CategoryTheory Limits

open scoped Topology

namespace Submission

/-! ### Glue -/

/-- The inclusion of a basepoint, as a morphism of `TopCat`. -/
def pointIncl {X : TopCat.{0}} (x : X) : TopCat.of PUnit.{1} ⟶ X :=
  TopCat.ofHom (ContinuousMap.const _ x)

@[simp]
theorem pointIncl_apply {X : TopCat.{0}} (x : X) (u : PUnit.{1}) : (pointIncl x).hom u = x := rfl

/-- Any map between nonempty subsingletons is bijective. -/
private theorem bijective_of_subsingleton {A B : Type*} [Subsingleton A] [Nonempty A]
    [Subsingleton B] (f : A → B) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.arbitrary A, Subsingleton.elim _ _⟩⟩

/-- An epimorphism out of a zero object forces its target to be a zero object. -/
theorem isZero_of_epi {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : C}
    (hX : IsZero X) (f : X ⟶ Y) [Epi f] : IsZero Y := by
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi f).mp ?_
  rw [Category.comp_id, comp_zero, hX.eq_zero_of_src f]

/-! ### The basepoint inclusion is a `1`-equivalence -/

/-- **The inclusion of a basepoint of a path-connected, simply connected space is a
`1`-equivalence**: it is bijective on `π₀` because `X` is path connected, and surjective on `π₁`
because `π₁(X)` is trivial. -/
theorem isNEquiv_one_pointIncl {X : TopCat.{0}} (x : X) [PathConnectedSpace X]
    (h1 : Subsingleton (π_ 1 ↥X x)) : IsNEquiv 1 (pointIncl x) := by
  refine ⟨⟨PUnit.unit⟩, ?_, ?_⟩
  · intro n hn u
    obtain rfl : n = 0 := by omega
    haveI : Subsingleton (π_ 0 ↥(TopCat.of PUnit.{1}) u) :=
      subsingleton_homotopyGroup_of_subsingleton (N := Fin 0) u
    haveI : Subsingleton (π_ 0 ↥X ((pointIncl x).hom u)) := subsingleton_homotopyGroup_zero x
    exact bijective_of_subsingleton _
  · intro u _
    haveI : Subsingleton (π_ 1 ↥X ((pointIncl x).hom u)) := h1
    exact ⟨default, Subsingleton.elim _ _⟩

/-! ### `H₁` of a simply connected space -/

/-- **A path-connected, simply connected space has vanishing first homology.** -/
theorem isZero_hgrp_one_of_subsingleton_piOne (X : TopCat.{0}) (x : X) [PathConnectedSpace X]
    (h1 : Subsingleton (π_ 1 ↥X x)) : IsZero (Hgrp 1 X) :=
  haveI : Epi (HgrpMap 1 (pointIncl x)) :=
    epi_HgrpMap_of_isNEquiv (isNEquiv_one_pointIncl x h1) 1 le_rfl
  isZero_of_epi (isZero_Hgrp_punit 1 one_ne_zero) (HgrpMap 1 (pointIncl x))

end Submission
