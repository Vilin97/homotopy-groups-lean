/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.UCT.HomologyClass
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The dual complex `Hom(K, G)` and the evaluation map

For a complex `K` of abelian groups of shape `c` and an abelian group `G` we form the complex
`Submission.homDual K G` of shape `c.symm`, with `(homDual K G).X i = (K.X i ⟶ G)` and differential
given by precomposition with the differential of `K`.  For `K` a chain complex indexed by `ℕ` this
is the usual cochain complex `Hom(K, G)`.

Evaluating a cocycle on a cycle induces the *evaluation map*

`Submission.ev : Hⁱ(Hom(K, G)) ⟶ Hom(Hᵢ(K), G)`,

which is natural in `K`.  The universal coefficient theorem is the statement that `ev` is
surjective with kernel `Ext¹(H_{i-1}(K), G)`.

## Main definitions

* `Submission.homDual K G` — the complex `Hom(K, G)`.
* `Submission.homDualMap f G` — the map `Hom(L, G) ⟶ Hom(K, G)` induced by `f : K ⟶ L`.
* `Submission.evCocycle` — the map `Hᵢ(K) ⟶ G` induced by a cocycle.
* `Submission.ev` — the evaluation map `Hⁱ(Hom(K, G)) ⟶ Hom(Hᵢ(K), G)`.

## Main results

* `Submission.ev_homologyMk`, `Submission.evCocycle_homologyMk` — the computation rules.
* `Submission.ev_naturality` — naturality of `ev` in `K`.
-/

open CategoryTheory Limits Opposite

noncomputable section

namespace Submission

variable {ι : Type*} {c : ComplexShape ι} (K L : HomologicalComplex AddCommGrpCat.{0} c)
  (G : AddCommGrpCat.{0})

/-- The `G`-dual `Hom(K, G)` of a complex of abelian groups. -/
def homDual : HomologicalComplex AddCommGrpCat.{0} c.symm :=
  ((preadditiveYoneda.obj G).mapHomologicalComplex c.symm).obj K.op

theorem homDual_X (i : ι) : (homDual K G).X i = AddCommGrpCat.of (K.X i ⟶ G) := rfl

@[simp]
theorem homDual_d_apply (i j : ι) (φ : K.X i ⟶ G) :
    (homDual K G).d i j φ = K.d j i ≫ φ := rfl

variable {K L G}

/-- The map `Hom(L, G) ⟶ Hom(K, G)` induced by a chain map `f : K ⟶ L`. -/
def homDualMap (f : K ⟶ L) (G : AddCommGrpCat.{0}) : homDual L G ⟶ homDual K G where
  f i := (preadditiveYoneda.obj G).map (f.f i).op
  comm' i j _ := by
    ext φ
    show K.d j i ≫ f.f i ≫ φ = f.f j ≫ L.d j i ≫ φ
    rw [← Category.assoc, ← Category.assoc, f.comm]

@[simp]
theorem homDualMap_f_apply (f : K ⟶ L) (i : ι) (φ : L.X i ⟶ G) :
    (homDualMap f G).f i φ = f.f i ≫ φ := rfl

@[simp]
theorem homDualMap_id : homDualMap (𝟙 K) G = 𝟙 (homDual K G) := by
  ext i φ
  simp

@[simp]
theorem homDualMap_comp (f : K ⟶ L) {M : HomologicalComplex AddCommGrpCat.{0} c} (g : L ⟶ M) :
    homDualMap (f ≫ g) G = homDualMap g G ≫ homDualMap f G := by
  ext i φ
  simp

/-- Precomposition `Hom(B, G) ⟶ Hom(A, G)` along a map `u : A ⟶ B` of abelian groups. -/
def precompHom {A B : AddCommGrpCat.{0}} (u : A ⟶ B) (G : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (B ⟶ G) ⟶ AddCommGrpCat.of (A ⟶ G) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ => u ≫ φ
      map_zero' := comp_zero
      map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _ }

@[simp]
theorem precompHom_apply {A B : AddCommGrpCat.{0}} (u : A ⟶ B) (G : AddCommGrpCat.{0})
    (φ : B ⟶ G) : precompHom u G φ = u ≫ φ := rfl

section Ev

variable (K G) in
/-- The map `Hᵢ(K) ⟶ G` induced by a cocycle `φ : K.X i ⟶ G`. -/
def evCocycle (i : ι) (φ : K.X i ⟶ G) (hφ : K.d (c.prev i) i ≫ φ = 0) : K.homology i ⟶ G :=
  (K.sc i).descHomology ((K.sc i).iCycles ≫ φ) (by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    exact hφ)

variable {i : ι}

@[simp]
theorem evCocycle_homologyMk (φ : K.X i ⟶ G) (hφ : K.d (c.prev i) i ≫ φ = 0) (x : K.X i)
    (hx : K.d i (c.next i) x = 0) : evCocycle K G i φ hφ (homologyMk x hx) = φ x := by
  rw [homologyMk_eq_homologyπ]
  have h := ConcreteCategory.congr_hom
    (ShortComplex.π_descHomology (K.sc i) ((K.sc i).iCycles ≫ φ)
      (by rw [← Category.assoc, ShortComplex.toCycles_i]; exact hφ))
    ((K.sc i).abCyclesIso.inv ⟨x, hx⟩)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ShortComplex.abCyclesIso_inv_apply_iCycles] at h
  exact h

theorem evCocycle_add (φ ψ : K.X i ⟶ G) (hφ : K.d (c.prev i) i ≫ φ = 0)
    (hψ : K.d (c.prev i) i ≫ ψ = 0) :
    evCocycle K G i (φ + ψ) (by rw [Preadditive.comp_add, hφ, hψ, add_zero]) =
      evCocycle K G i φ hφ + evCocycle K G i ψ hψ := by
  refine homology_hom_ext fun x hx => ?_
  simp

theorem evCocycle_zero : evCocycle K G i 0 (comp_zero) = 0 := by
  refine homology_hom_ext fun x hx => ?_
  simp

variable (K G i) in
/-- The evaluation map on cocycles, as an additive homomorphism. -/
def evCyc : cyclesSub (homDual K G) i →+ (K.homology i ⟶ G) where
  toFun p := evCocycle K G i p.1 p.2
  map_zero' := evCocycle_zero
  map_add' p q := evCocycle_add p.1 q.1 p.2 q.2

theorem evCyc_apply (φ : K.X i ⟶ G) (hφ : K.d (c.prev i) i ≫ φ = 0) :
    evCyc K G i ⟨φ, hφ⟩ = evCocycle K G i φ hφ := rfl

theorem evCyc_apply' (p : cyclesSub (homDual K G) i) :
    evCyc K G i p = evCocycle K G i p.1 p.2 := rfl

theorem evCyc_boundary (ψ : K.X (c.next i) ⟶ G) (p : cyclesSub (homDual K G) i)
    (hp : p.1 = K.d i (c.next i) ≫ ψ) : evCyc K G i p = 0 := by
  refine homology_hom_ext fun x hx => ?_
  rw [evCyc_apply', evCocycle_homologyMk, hp, ConcreteCategory.comp_apply, hx, map_zero]
  simp

variable (K G i) in
/-- The evaluation map, on the explicit quotient description of `Hⁱ(Hom(K, G))`. -/
def evQuot : AddCommGrpCat.of (AddMonoidHom.ker (((homDual K G).sc i).g).hom ⧸
      AddMonoidHom.range (((homDual K G).sc i).abToCycles)) ⟶
    AddCommGrpCat.of (K.homology i ⟶ G) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.lift
    (AddMonoidHom.range (((homDual K G).sc i).abToCycles)) (evCyc K G i) (by
      rintro _ ⟨ψ, rfl⟩
      exact evCyc_boundary ψ _ rfl))

theorem evQuot_mk (p : cyclesSub (homDual K G) i) :
    evQuot K G i (QuotientAddGroup.mk'
      (AddMonoidHom.range (((homDual K G).sc i).abToCycles)) p) = evCyc K G i p := rfl

variable (K G i) in
/-- The **evaluation map** `Hⁱ(Hom(K, G)) ⟶ Hom(Hᵢ(K), G)`. -/
def ev : (homDual K G).homology i ⟶ AddCommGrpCat.of (K.homology i ⟶ G) :=
  ((homDual K G).sc i).abHomologyIso.hom ≫ evQuot K G i

@[simp]
theorem ev_homologyMk (φ : K.X i ⟶ G) (hφ : K.d (c.prev i) i ≫ φ = 0) :
    ev K G i (homologyMk (K := homDual K G) φ hφ) = evCocycle K G i φ hφ :=
  (congrArg (⇑(evQuot K G i)) (abHomologyIso_hom_homologyMk (K := homDual K G) φ hφ)).trans
    (evQuot_mk ⟨φ, hφ⟩)

/-- **Naturality of the evaluation map**: for a chain map `f : K ⟶ L` the square

```
Hⁱ(Hom(L, G)) --ev--> Hom(Hᵢ(L), G)
     |                      |
     |  (f*)*               |  (Hᵢ f)*
     v                      v
Hⁱ(Hom(K, G)) --ev--> Hom(Hᵢ(K), G)
```

commutes.  This is what makes the cohomological and the homological Wang maps adjoint. -/
theorem ev_naturality_apply (f : K ⟶ L) (Φ : (homDual L G).homology i) :
    ev K G i (HomologicalComplex.homologyMap (homDualMap f G) i Φ) =
      HomologicalComplex.homologyMap f i ≫ ev L G i Φ := by
  obtain ⟨φ, hφ, rfl⟩ := homologyMk_surjective Φ
  have hφ0 : L.d (c.prev i) i ≫ φ = 0 := hφ
  have hφ' : K.d (c.prev i) i ≫ (f.f i ≫ φ) = 0 := by
    rw [← Category.assoc, ← f.comm, Category.assoc, hφ0, comp_zero]
  rw [homologyMap_homologyMk (homDualMap f G) φ hφ hφ', ev_homologyMk, ev_homologyMk]
  refine homology_hom_ext fun x hx => ?_
  have hfx : L.d i (c.next i) (f.f i x) = 0 := by
    rw [← ConcreteCategory.comp_apply, f.comm, ConcreteCategory.comp_apply, hx, map_zero]
  rw [evCocycle_homologyMk, ConcreteCategory.comp_apply, homologyMap_homologyMk f x hx hfx,
    evCocycle_homologyMk]
  rfl

/-- Naturality of the evaluation map, as an equality of morphisms. -/
theorem ev_naturality (f : K ⟶ L) :
    HomologicalComplex.homologyMap (homDualMap f G) i ≫ ev K G i =
      ev L G i ≫ precompHom (HomologicalComplex.homologyMap f i) G := by
  ext Φ : 2
  exact ev_naturality_apply f Φ

end Ev

end Submission
