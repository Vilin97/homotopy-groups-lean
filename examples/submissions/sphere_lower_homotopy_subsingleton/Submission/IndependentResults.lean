/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ForMathlib.HomotopyGroup.Contractible
import Submission.ForMathlib.HomotopyGroup.Covering
import Submission.ForMathlib.HomotopyGroup.Product

/-!
# Nine independent homotopy-group results

This file exposes nine source-auditable results supplied by the reusable `Submission`
infrastructure. Together with `sphere_one_higher_homotopy_subsingleton` in the separate metric
circle submission, these form the maintained ten-result formalization set.

The list deliberately counts general mathematical statements, not individual numerical
specializations of one theorem.
-/

open scoped ContinuousMap Topology Topology.Homotopy

namespace Submission

universe u v w

/-- Result 1: Mathlib's cubical `pi_0` is the usual set of path components. -/
theorem pi0_equiv_zerothHomotopy
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 0 X x ≃ ZerothHomotopy X) :=
  ⟨HomotopyGroup.pi0EquivZerothHomotopy⟩

/-- Result 2: Mathlib's cubical `pi_1` is the usual fundamental group. -/
theorem pi1_mulEquiv_fundamentalGroup
    (X : Type u) [TopologicalSpace X] (x : X) :
    Nonempty (HomotopyGroup.Pi 1 X x ≃* FundamentalGroup X x) :=
  ⟨HomotopyGroup.pi1MulEquivFundamentalGroup⟩

/-- Result 3: a path gives change of basepoint in every positive dimension. -/
theorem homotopyGroup_change_basepoint
    (n : ℕ) (X : Type u) [TopologicalSpace X] (x y : X) (p : Path x y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) X y) :=
  nonempty_mulEquiv_of_joined ⟨p⟩

/-- Result 4: homotopy-equivalent spaces have isomorphic positive homotopy groups. -/
theorem homotopyGroup_homotopy_invariance
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (x : X) (e : X ≃ₕ Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) X x ≃*
        HomotopyGroup.Pi (n + 1) Y (e x)) :=
  nonempty_mulEquiv_of_homotopyEquiv' e x

/-- Result 5: positive homotopy groups preserve binary products. -/
theorem homotopyGroup_product
    (n : ℕ) (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (X × Y) (x, y) ≃*
        HomotopyGroup.Pi (n + 1) X x ×
          HomotopyGroup.Pi (n + 1) Y y) :=
  ⟨HomotopyGroup.prodMulEquiv x y⟩

/-- Result 6: induced maps on positive homotopy groups respect composition. -/
theorem homotopyGroup_map_comp
    (n : ℕ) {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (f : C(X, Y)) (hf : f x = y)
    (g : C(Y, Z)) (hg : g y = z) :
    (HomotopyGroup.mapHom (N := Fin (n + 1)) g hg).comp
        (HomotopyGroup.mapHom f hf) =
      HomotopyGroup.mapHom (g.comp f) (by simp [hf, hg]) :=
  HomotopyGroup.mapHom_comp g hg f hf

/-- Result 7: pointed-homotopic maps induce the same positive homotopy-group homomorphism. -/
theorem homotopyGroup_pointed_homotopy_invariance
    (n : ℕ) {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} (hf : f x = y)
    {S : Set X} (hx : x ∈ S) (H : f.HomotopicRel g S) :
    HomotopyGroup.mapHom (N := Fin (n + 1)) f hf =
      HomotopyGroup.mapHom g ((H.fst_eq_snd hx).symm.trans hf) :=
  HomotopyGroup.mapHom_eq_of_homotopicRel hf hx H

/-- Result 8: covering maps preserve homotopy groups in dimensions at least two. -/
theorem homotopyGroup_covering_invariance
    (k : ℕ) {E : Type u} {X : Type v}
    [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (hp : IsCoveringMap p) (e : E) :
    Nonempty
      (HomotopyGroup.Pi (k + 2) E e ≃*
        HomotopyGroup.Pi (k + 2) X (p e)) :=
  ⟨HomotopyGroup.coveringMulEquiv hp e⟩

/-- Result 9: every positive homotopy group of a contractible space is trivial. -/
theorem homotopyGroup_contractible_subsingleton
    (n : ℕ) (X : Type u) [TopologicalSpace X] [ContractibleSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) :=
  subsingleton_homotopyGroup_of_contractible x

end Submission
