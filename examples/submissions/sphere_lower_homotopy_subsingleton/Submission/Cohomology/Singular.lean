/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Basic
import Mathlib.AlgebraicTopology.SingularSet

/-!
# Singular cohomology of a topological space

The singular cochain complex of a space `X` is the cochain complex of its singular simplicial set
`TopCat.toSSet.obj X`, so singular cohomology is a special case of the simplicial cohomology of
`Submission/Cohomology/Basic.lean`:

`Hsing n X R := Hcoh n (TopCat.toSSet.obj X) R`.

Everything proved for `Hcoh` — the cup product, the Leibniz rule, associativity, unitality and
naturality — therefore applies verbatim.

## Relation to `Submission.Hgrp`

`Submission.Hgrp n X` (in `Submission/Homology/Basic.lean`) is Mathlib's singular *homology*
`H_n(X; ℤ)`, built as the homology of `alternatingFaceMapComplex` applied to the free
`AddCommGrpCat`-valued simplicial object on `TopCat.toSSet.obj X`.  By construction its degree-`n`
chain group is the free abelian group `ℤ[(Sing X)_n]` on the `n`-simplices, and the differential
is the alternating sum `∑ (-1)^i (δ i)_*`.

Our `Cochain (TopCat.toSSet.obj X) R n = (Sing X)_n → R` is exactly
`Hom_ℤ(ℤ[(Sing X)_n], R)` (via `Finsupp.linearCombination` / `Finsupp.lift`), and
`Submission.coboundary` is the transpose of that differential.  So the singular cochain complex
defined here is the `R`-linear dual of the singular chain complex underlying `Hgrp`, and
`Hsing n X R` is the cohomology of that dual complex.

The precise comparison — the universal coefficient theorem
`0 → Ext¹(H_{n-1}(X), R) → H^n(X; R) → Hom(H_n(X), R) → 0` — is **not** proved here; it is a
separate piece of work.  Nothing in this file depends on it.

## Main definitions

* `Submission.Hsing n X R` : singular cohomology.
* `Submission.Hsing.map f n` : contravariant functoriality.
* `Submission.cupHsing h` : the cup product.
* `Submission.Hsing.one` : the unit class in `H⁰`.
-/

namespace Submission

open CategoryTheory Simplicial

noncomputable section

/-- The singular `n`-cochains of a topological space with coefficients in `R`. -/
abbrev SingCochain (X : TopCat.{0}) (R : Type) [CommRing R] (n : ℕ) : Type :=
  Cochain (TopCat.toSSet.obj X) R n

/-- The `n`-th singular cohomology module of a topological space with coefficients in `R`. -/
def Hsing (n : ℕ) (X : TopCat.{0}) (R : Type) [CommRing R] : Type :=
  Hcoh n (TopCat.toSSet.obj X) R

instance (n : ℕ) (X : TopCat.{0}) (R : Type) [CommRing R] : AddCommGroup (Hsing n X R) :=
  inferInstanceAs (AddCommGroup (Hcoh n (TopCat.toSSet.obj X) R))

instance (n : ℕ) (X : TopCat.{0}) (R : Type) [CommRing R] : Module R (Hsing n X R) :=
  inferInstanceAs (Module R (Hcoh n (TopCat.toSSet.obj X) R))

variable {R : Type} [CommRing R]

/-- The map induced on singular cohomology by a continuous map (contravariant). -/
def Hsing.map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : Hsing n Y R →ₗ[R] Hsing n X R :=
  Hcoh.map R (TopCat.toSSet.map f) n

@[simp]
theorem Hsing.map_id (X : TopCat.{0}) (n : ℕ) :
    Hsing.map (R := R) (𝟙 X) n = LinearMap.id := by
  rw [Hsing.map, TopCat.toSSet.map_id, Hcoh.map_id]
  rfl

theorem Hsing.map_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Hsing.map (R := R) (f ≫ g) n = (Hsing.map f n).comp (Hsing.map g n) := by
  rw [Hsing.map, TopCat.toSSet.map_comp, Hcoh.map_comp]
  rfl

/-- An isomorphism of topological spaces induces a linear equivalence on singular cohomology,
contravariantly. -/
noncomputable def Hsing.linearEquivOfIso {X Y : TopCat.{0}} (f : X ⟶ Y) [IsIso f]
    (n : ℕ) : Hsing n Y R ≃ₗ[R] Hsing n X R where
  toLinearMap := Hsing.map f n
  invFun := Hsing.map (inv f) n
  left_inv x := by
    change Hsing.map (inv f) n (Hsing.map f n x) = x
    have hcomp := LinearMap.congr_fun (Hsing.map_comp (R := R) (inv f) f n) x
    rw [LinearMap.comp_apply] at hcomp
    rw [← hcomp, IsIso.inv_hom_id, Hsing.map_id]
    rfl
  right_inv x := by
    change Hsing.map f n (Hsing.map (inv f) n x) = x
    have hcomp := LinearMap.congr_fun (Hsing.map_comp (R := R) f (inv f) n) x
    rw [LinearMap.comp_apply] at hcomp
    rw [← hcomp, IsIso.hom_inv_id, Hsing.map_id]
    rfl

/-- Pullback along an isomorphism of topological spaces is bijective on singular cohomology. -/
theorem Hsing.map_bijective_of_isIso {X Y : TopCat.{0}} (f : X ⟶ Y) [IsIso f]
    (n : ℕ) : Function.Bijective (Hsing.map (R := R) f n) :=
  (Hsing.linearEquivOfIso f n).bijective

/-- The cup product on singular cohomology. -/
def cupHsing {X : TopCat.{0}} {p q n : ℕ} (h : p + q = n) :
    Hsing p X R →ₗ[R] Hsing q X R →ₗ[R] Hsing n X R :=
  cupH h

/-- The unit class in `H⁰(X; R)`. -/
def Hsing.one (X : TopCat.{0}) (R : Type) [CommRing R] : Hsing 0 X R :=
  Hcoh.one (TopCat.toSSet.obj X) R

theorem one_cupHsing {X : TopCat.{0}} {q : ℕ} (x : Hsing q X R) :
    cupHsing (Nat.zero_add q) (Hsing.one X R) x = x :=
  one_cupH x

theorem cupHsing_one {X : TopCat.{0}} {p : ℕ} (x : Hsing p X R) :
    cupHsing (Nat.add_zero p) x (Hsing.one X R) = x :=
  cupH_one x

theorem cupHsing_assoc {X : TopCat.{0}} {p q r m n k : ℕ} (hm : p + q = m) (hn : q + r = n)
    (hk : p + q + r = k) (x : Hsing p X R) (y : Hsing q X R) (z : Hsing r X R) :
    cupHsing (by omega : m + r = k) (cupHsing hm x y) z =
      cupHsing (by omega : p + n = k) x (cupHsing hn y z) :=
  cupH_assoc hm hn hk x y z

/-- **Naturality** of the cup product on singular cohomology. -/
theorem map_cupHsing {X Y : TopCat.{0}} (f : X ⟶ Y) {p q n : ℕ} (h : p + q = n)
    (x : Hsing p Y R) (y : Hsing q Y R) :
    Hsing.map f n (cupHsing h x y) =
      cupHsing h (Hsing.map f p x) (Hsing.map f q y) :=
  map_cupH (TopCat.toSSet.map f) h x y

end

end Submission
