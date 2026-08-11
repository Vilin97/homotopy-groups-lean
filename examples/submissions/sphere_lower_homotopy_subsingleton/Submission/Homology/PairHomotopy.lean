/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Pair
import Submission.Homology.Homotopy
import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Homotopy invariance of relative singular homology

A map of pairs `(f_A, f) : (X, A) ⟶ (Y, B)` — that is, a commutative square with monomorphic
vertical maps — induces a map `HrelMap n : H_n(X, A) ⟶ H_n(Y, B)` on relative singular homology.
This file proves that homotopic maps of pairs induce the same map, and consequently that a
homotopy equivalence of pairs induces an isomorphism.

The proof has two halves.

* A purely homological half: a chain homotopy between two maps of chain complexes descends to
  the cokernels of a pair of monomorphisms, *provided* the homotopy operators carry the
  subcomplex into the subcomplex (`Submission.descHomotopy`). This is the only place where the
  degreewise description of cokernels in `ChainComplex` is needed.
* A simplicial half: the chain homotopy that Mathlib produces from a topological homotopy is
  natural, so a homotopy of pairs really does produce compatible chain homotopies
  (`Submission.CsingMap_comp_chainHomotopy_hom`).

## Main definitions and results

* `relComplexMap` / `HrelMap` — the maps induced by a map of pairs;
* `descHomotopy` — descent of a chain homotopy to the relative complexes;
* `isZero_Hrel_of_chainDeformation` — if the inclusion of the subcomplex admits a chain
  retraction which is a chain-homotopy inverse through operators preserving the subcomplex,
  then all relative homology vanishes;
* `HrelMap_congr` — homotopic maps of pairs induce the same map on relative homology;
* `hrelIsoOfHomotopyEquiv` — a homotopy equivalence of pairs is a relative homology isomorphism.
-/

open CategoryTheory Limits AlgebraicTopology MonoidalCategory

noncomputable section

namespace Submission

/-! ### Descending a chain homotopy to the cokernel -/

section Descent

variable {A X B Y : ChainComplex AddCommGrpCat.{0} ℕ}

/-- A map out of `X.X n` which kills the image of `A.X n` descends to the cokernel complex;
this uses that cokernels of maps of chain complexes are computed degreewise. -/
def cokDesc (i : A ⟶ X) (n : ℕ) {T : AddCommGrpCat.{0}} (u : X.X n ⟶ T) (hu : i.f n ≫ u = 0) :
    (cokernel i).X n ⟶ T :=
  Cofork.IsColimit.desc (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n) i) u
    (by simp only [Limits.zero_comp]; exact hu)

@[reassoc (attr := simp)]
theorem π_cokDesc (i : A ⟶ X) (n : ℕ) {T : AddCommGrpCat.{0}} (u : X.X n ⟶ T)
    (hu : i.f n ≫ u = 0) : (cokernel.π i).f n ≫ cokDesc i n u hu = u :=
  Cofork.IsColimit.π_desc (isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) n) i)

@[reassoc (attr := simp)]
theorem π_cokernel_map (i : A ⟶ X) (j : B ⟶ Y) (fA : A ⟶ B) (f : X ⟶ Y)
    (w : i ≫ f = fA ≫ j) :
    cokernel.π i ≫ cokernel.map i j fA f w = f ≫ cokernel.π j :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem π_cokernel_map_f (i : A ⟶ X) (j : B ⟶ Y) (fA : A ⟶ B) (f : X ⟶ Y)
    (w : i ≫ f = fA ≫ j) (n : ℕ) :
    (cokernel.π i).f n ≫ (cokernel.map i j fA f w).f n = f.f n ≫ (cokernel.π j).f n := by
  rw [← HomologicalComplex.comp_f, cokernel.map, cokernel.π_desc, HomologicalComplex.comp_f]

/-- A chain homotopy whose operators map the subcomplex `A` into the subcomplex `B` descends to
a chain homotopy between the induced maps of relative complexes. -/
def descHomotopy (i : A ⟶ X) (j : B ⟶ Y) {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j) (H : Homotopy f g)
    (hH : ∀ p q, i.f p ≫ H.hom p q ≫ (cokernel.π j).f q = 0) :
    Homotopy (cokernel.map i j fA f wf) (cokernel.map i j gA g wg) where
  hom p q := cokDesc i p (H.hom p q ≫ (cokernel.π j).f q) (by rw [← Category.assoc]; exact hH p q)
  zero p q hpq := by
    have hepi : Epi ((cokernel.π i).f p) := inferInstance
    apply hepi.left_cancellation
    simp [H.zero p q hpq]
  comm n := by
    have hepi : Epi ((cokernel.π i).f n) := inferInstance
    apply hepi.left_cancellation
    have hd : ∀ (p q : ℕ), (cokernel.π i).f p ≫ (cokernel i).d p q =
        X.d p q ≫ (cokernel.π i).f q := fun p q => (cokernel.π i).comm p q
    have hd' : ∀ (p q : ℕ), (cokernel.π j).f p ≫ (cokernel j).d p q =
        Y.d p q ≫ (cokernel.π j).f q := fun p q => (cokernel.π j).comm p q
    have e3 : (cokernel.π i).f n ≫ (dNext n) (fun p q => cokDesc i p
        (H.hom p q ≫ (cokernel.π j).f q) (by rw [← Category.assoc]; exact hH p q)) =
        (dNext n) H.hom ≫ (cokernel.π j).f n := by
      simp only [dNext, AddMonoidHom.mk'_apply]
      rw [← Category.assoc, hd, Category.assoc, π_cokDesc, ← Category.assoc]
    have e4 : (cokernel.π i).f n ≫ (prevD n) (fun p q => cokDesc i p
        (H.hom p q ≫ (cokernel.π j).f q) (by rw [← Category.assoc]; exact hH p q)) =
        (prevD n) H.hom ≫ (cokernel.π j).f n := by
      simp only [prevD, AddMonoidHom.mk'_apply]
      rw [← Category.assoc, π_cokDesc, Category.assoc, hd', ← Category.assoc]
    rw [Preadditive.comp_add, Preadditive.comp_add, e3, e4, π_cokernel_map_f, π_cokernel_map_f,
      ← Preadditive.add_comp, ← Preadditive.add_comp, ← H.comm n]

end Descent

/-! ### Maps of pairs -/

variable {A X B Y : TopCat.{0}}

/-- The map of relative singular chain complexes induced by a map of pairs, i.e. by a
commutative square whose vertical maps are monomorphisms. -/
def relComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j] {fA : A ⟶ B} {f : X ⟶ Y}
    (w : i ≫ f = fA ≫ j) : relComplex i ⟶ relComplex j :=
  cokernel.map _ _ (CsingMap fA) (CsingMap f)
    (by rw [CsingMap, CsingMap, CsingMap, CsingMap, ← CsingFunctor.map_comp,
      ← CsingFunctor.map_comp, w])

/-- The map on relative singular homology induced by a map of pairs. -/
def HrelMap (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j] {fA : A ⟶ B} {f : X ⟶ Y}
    (w : i ≫ f = fA ≫ j) : Hrel n i ⟶ Hrel n j :=
  HomologicalComplex.homologyMap (relComplexMap i j w) n

/-- The relative complex map is compatible with the projections from absolute chains. -/
@[reassoc (attr := simp)]
theorem relProj_comp_relComplexMap (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j] {fA : A ⟶ B}
    {f : X ⟶ Y} (w : i ≫ f = fA ≫ j) :
    relProj i ≫ relComplexMap i j w = CsingMap f ≫ relProj j :=
  cokernel.π_desc _ _ _

@[simp]
theorem relComplexMap_id (i : A ⟶ X) [Mono i] :
    relComplexMap i i (show i ≫ 𝟙 X = 𝟙 A ≫ i by simp) = 𝟙 _ := by
  have hepi : Epi (relProj i) := coequalizer.π_epi
  apply hepi.left_cancellation
  rw [relProj_comp_relComplexMap, CsingMap, CsingFunctor.map_id, Category.id_comp,
    Category.comp_id]

@[simp]
theorem HrelMap_id (n : ℕ) (i : A ⟶ X) [Mono i] :
    HrelMap n i i (show i ≫ 𝟙 X = 𝟙 A ≫ i by simp) = 𝟙 _ := by
  rw [HrelMap, relComplexMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem relComplexMap_comp {C Z : TopCat.{0}} (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    (k : C ⟶ Z) [Mono k] {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {gB : B ⟶ C} {g : Y ⟶ Z} (w' : j ≫ g = gB ≫ k) :
    relComplexMap i j w ≫ relComplexMap j k w' =
      relComplexMap i k (show i ≫ f ≫ g = (fA ≫ gB) ≫ k by
        rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) := by
  have hepi : Epi (relProj i) := coequalizer.π_epi
  apply hepi.left_cancellation
  rw [relProj_comp_relComplexMap_assoc, relProj_comp_relComplexMap,
    relProj_comp_relComplexMap]
  simp only [CsingMap]
  rw [CsingFunctor.map_comp, Category.assoc]

theorem HrelMap_comp {C Z : TopCat.{0}} (n : ℕ) (i : A ⟶ X) [Mono i] (j : B ⟶ Y) [Mono j]
    (k : C ⟶ Z) [Mono k] {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {gB : B ⟶ C} {g : Y ⟶ Z} (w' : j ≫ g = gB ≫ k) :
    HrelMap n i j w ≫ HrelMap n j k w' =
      HrelMap n i k (show i ≫ f ≫ g = (fA ≫ gB) ≫ k by
        rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) := by
  rw [HrelMap, HrelMap, HrelMap, ← relComplexMap_comp i j k w w',
    HomologicalComplex.homologyMap_comp]
  rfl

/-! ### Naturality of the chain homotopy attached to a homotopy -/

section Naturality

open Simplicial Opposite

variable {S T S' T' : SSet.{0}} {f g : S ⟶ T} {f' g' : S' ⟶ T'}

/-- Naturality of the combinatorial homotopy attached to a simplicial homotopy. -/
theorem toSimplicialObjectHomotopy_h_naturality (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    {u : S ⟶ S'} {v : T ⟶ T'} (hu : (u ▷ Δ[1]) ≫ H'.h = H.h ≫ v) (n : ℕ) (k : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h k
      = H.toSimplicialObjectHomotopy.h k ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy, TypeCat.Fun.toFun_apply,
    types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  rw [← SSet.yonedaEquiv_symm_comp, MonoidalCategory.comp_whiskerRight, Category.assoc, hu]
  rfl

/-- The degree-`p` component of the map of simplicial chain complexes. -/
theorem chainComplexMap_f (u : S ⟶ T) (R : AddCommGrpCat.{0}) (p : ℕ) :
    (SSet.chainComplexMap u R).f p = (sigmaConst.obj R).map (u.app (op ⦋p⦌)) := rfl

/-- The nonzero components of the chain homotopy attached to a simplicial homotopy. -/
theorem chainComplexMap_hom_succ (H : SSet.Homotopy f g) (R : AddCommGrpCat.{0}) (p : ℕ) :
    (H.chainComplexMap R).hom p (p + 1) =
      -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) •
        (((sigmaConst.obj R).map (H.toSimplicialObjectHomotopy.h k) :
          (S.chainComplex R).X p ⟶ (T.chainComplex R).X (p + 1))) := by
  rw [SSet.Homotopy.chainComplexMap, CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap]
  simp only [CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    CategoryTheory.SimplicialObject.Homotopy.whiskerRight_h]
  rfl

/-- Naturality of the chain homotopy attached to a simplicial homotopy. -/
theorem chainComplexMap_hom_naturality (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    {u : S ⟶ S'} {v : T ⟶ T'} (hu : (u ▷ Δ[1]) ≫ H'.h = H.h ≫ v) (R : AddCommGrpCat.{0})
    (p q : ℕ) :
    (SSet.chainComplexMap u R).f p ≫ (H'.chainComplexMap R).hom p q
      = (H.chainComplexMap R).hom p q ≫ (SSet.chainComplexMap v R).f q := by
  by_cases hpq : p + 1 = q
  · subst hpq
    have key : ∀ k : Fin (p + 1), (SSet.chainComplexMap u R).f p ≫
        (sigmaConst.obj R).map (H'.toSimplicialObjectHomotopy.h k) =
        (sigmaConst.obj R).map (H.toSimplicialObjectHomotopy.h k) ≫
          (SSet.chainComplexMap v R).f (p + 1) := by
      intro k
      show (sigmaConst.obj R).map (u.app (op ⦋p⦌)) ≫ _ =
        _ ≫ (sigmaConst.obj R).map (v.app (op ⦋p + 1⦌))
      rw [← Functor.map_comp, ← Functor.map_comp,
        toSimplicialObjectHomotopy_h_naturality H H' hu p k]
    simp only [SSet.Homotopy.chainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      CategoryTheory.SimplicialObject.Homotopy.whiskerRight_h]
    have gen : ∀ (a : (S.chainComplex R).X p ⟶ (S'.chainComplex R).X p)
        (b : (T.chainComplex R).X (p + 1) ⟶ (T'.chainComplex R).X (p + 1))
        (φ : Fin (p + 1) → ((S'.chainComplex R).X p ⟶ (T'.chainComplex R).X (p + 1)))
        (ψ : Fin (p + 1) → ((S.chainComplex R).X p ⟶ (T.chainComplex R).X (p + 1))),
        (∀ k, a ≫ φ k = ψ k ≫ b) →
          a ≫ (-∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • φ k) =
            (-∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • ψ k) ≫ b := by
      intro a b φ ψ h
      simp [Preadditive.comp_sum, Preadditive.sum_comp, h]
    exact gen _ _ _ _ key
  · rw [(H'.chainComplexMap R).zero p q (by simpa using hpq),
      (H.chainComplexMap R).zero p q (by simpa using hpq)]
    simp

end Naturality

/-! ### Homotopy invariance for pairs -/

section PairHomotopy

open Simplicial Opposite Functor.LaxMonoidal

variable {A X B Y : TopCat.{0}}

/-- The chain homotopy on singular chains induced by a homotopy of maps of spaces. -/
def csingHomotopy {f g : X ⟶ Y} (H : TopCat.Homotopy f g) : Homotopy (CsingMap f) (CsingMap g) :=
  H.toSSet.chainComplexMap (AddCommGrpCat.of ℤ)

/-- If two homotopies agree on a subspace, so do the induced simplicial homotopies. -/
theorem toSSet_h_compat {i : A ⟶ X} {j : B ⟶ Y} {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (HA : TopCat.Homotopy fA gA) (HX : TopCat.Homotopy f g)
    (hc : (i ▷ TopCat.I) ≫ HX.h = HA.h ≫ j) :
    (TopCat.toSSet.map i ▷ Δ[1]) ≫ HX.toSSet.h = HA.toSSet.h ≫ TopCat.toSSet.map j := by
  show (TopCat.toSSet.map i ▷ Δ[1]) ≫ (_ ◁ SSet.stdSimplex.toSSetObjI ≫
      μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map HX.h) =
    (_ ◁ SSet.stdSimplex.toSSetObjI ≫ μ TopCat.toSSet _ _ ≫ TopCat.toSSet.map HA.h) ≫
      TopCat.toSSet.map j
  rw [← Category.assoc, ← whisker_exchange]
  simp only [Category.assoc]
  congr 1
  rw [μ_natural_left_assoc, ← Functor.map_comp, ← Functor.map_comp, hc]

/-- A homotopy between two maps of pairs: homotopies of the ambient maps and of the restrictions
which agree on the subspace. -/
structure PairHomotopy (i : A ⟶ X) (j : B ⟶ Y) {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (_wf : i ≫ f = fA ≫ j) (_wg : i ≫ g = gA ≫ j) where
  /-- The homotopy of the maps of subspaces. -/
  sub : TopCat.Homotopy fA gA
  /-- The homotopy of the maps of ambient spaces. -/
  amb : TopCat.Homotopy f g
  /-- The two homotopies agree on the subspace. -/
  compat : (i ▷ TopCat.I) ≫ amb.h = sub.h ≫ j

/-- Homotopic maps of pairs induce the same map on relative singular homology. -/
theorem HrelMap_congr {i : A ⟶ X} [Mono i] {j : B ⟶ Y} [Mono j] {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j) (P : PairHomotopy i j wf wg) (n : ℕ) :
    HrelMap n i j wf = HrelMap n i j wg := by
  have hnat := chainComplexMap_hom_naturality P.sub.toSSet P.amb.toSSet
    (toSSet_h_compat P.sub P.amb P.compat) (AddCommGrpCat.of ℤ)
  have hH : ∀ p q, (CsingMap i).f p ≫ (csingHomotopy P.amb).hom p q ≫
      (cokernel.π (CsingMap j)).f q = 0 := by
    intro p q
    have h1 : (CsingMap i).f p ≫ (csingHomotopy P.amb).hom p q =
        (csingHomotopy P.sub).hom p q ≫ (CsingMap j).f q := hnat p q
    rw [← Category.assoc, h1, Category.assoc, ← HomologicalComplex.comp_f,
      cokernel.condition, HomologicalComplex.zero_f, comp_zero]
  have w1 : CsingMap i ≫ CsingMap f = CsingMap fA ≫ CsingMap j := by
    rw [CsingMap, CsingMap, CsingMap, CsingMap, ← CsingFunctor.map_comp,
      ← CsingFunctor.map_comp, wf]
  have w2 : CsingMap i ≫ CsingMap g = CsingMap gA ≫ CsingMap j := by
    rw [CsingMap, CsingMap, CsingMap, CsingMap, ← CsingFunctor.map_comp,
      ← CsingFunctor.map_comp, wg]
  exact (descHomotopy (CsingMap i) (CsingMap j) w1 w2 (csingHomotopy P.amb) hH).homologyMap_eq n

/-- Building a `PairHomotopy` from the pointwise compatibility condition. -/
def PairHomotopy.ofPointwise {i : A ⟶ X} {j : B ⟶ Y} {fA gA : A ⟶ B} {f g : X ⟶ Y}
    (wf : i ≫ f = fA ≫ j) (wg : i ≫ g = gA ≫ j)
    (sub : TopCat.Homotopy fA gA) (amb : TopCat.Homotopy f g)
    (hc : ∀ (t : unitInterval) (a : A), amb (t, i a) = j (sub (t, a))) :
    PairHomotopy i j wf wg where
  sub := sub
  amb := amb
  compat := by ext p; exact hc _ _

/-- A homotopy equivalence of pairs induces an isomorphism on relative singular homology. -/
def hrelIsoOfPairHomotopyEquiv {i : A ⟶ X} [Mono i] {j : B ⟶ Y} [Mono j]
    {fA : A ⟶ B} {f : X ⟶ Y} (w : i ≫ f = fA ≫ j)
    {gB : B ⟶ A} {g : Y ⟶ X} (w' : j ≫ g = gB ≫ i)
    {w₁ : i ≫ f ≫ g = (fA ≫ gB) ≫ i} {w₁' : i ≫ 𝟙 X = 𝟙 A ≫ i}
    {w₂ : j ≫ g ≫ f = (gB ≫ fA) ≫ j} {w₂' : j ≫ 𝟙 Y = 𝟙 B ≫ j}
    (P₁ : PairHomotopy i i w₁ w₁') (P₂ : PairHomotopy j j w₂ w₂') (n : ℕ) :
    Hrel n i ≅ Hrel n j where
  hom := HrelMap n i j w
  inv := HrelMap n j i w'
  hom_inv_id := by
    rw [HrelMap_comp]
    exact (HrelMap_congr _ _ P₁ n).trans (HrelMap_id n i)
  inv_hom_id := by
    rw [HrelMap_comp]
    exact (HrelMap_congr _ _ P₂ n).trans (HrelMap_id n j)

end PairHomotopy

/-! ### Vanishing of relative homology from a chain deformation -/

/-- If the inclusion of singular chains of a subspace admits a retraction `r` such that
`r` followed by the inclusion is chain homotopic to the identity through operators preserving
the subcomplex, then all relative singular homology vanishes. -/
theorem isZero_Hrel_of_chainDeformation {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]
    (r : Csing X ⟶ Csing A) (hr : CsingMap i ≫ r = 𝟙 (Csing A))
    (H : Homotopy (r ≫ CsingMap i) (𝟙 (Csing X)))
    (hH : ∀ p q, (CsingMap i).f p ≫ H.hom p q ≫ (relProj i).f q = 0) (n : ℕ) :
    IsZero (Hrel n i) := by
  have hw1 : CsingMap i ≫ (r ≫ CsingMap i) = 𝟙 (Csing A) ≫ CsingMap i := by
    rw [← Category.assoc, hr, Category.id_comp]
  have hw2 : CsingMap i ≫ 𝟙 (Csing X) = 𝟙 (Csing A) ≫ CsingMap i := by
    rw [Category.comp_id, Category.id_comp]
  have hepi : Epi (cokernel.π (CsingMap i)) := coequalizer.π_epi
  have hz : cokernel.map (CsingMap i) (CsingMap i) (𝟙 (Csing A)) (r ≫ CsingMap i) hw1 = 0 := by
    apply hepi.left_cancellation
    rw [π_cokernel_map, Category.assoc]
    rw [show CsingMap i ≫ cokernel.π (CsingMap i) = 0 from cokernel.condition _]
    rw [comp_zero, comp_zero]
  have ho : cokernel.map (CsingMap i) (CsingMap i) (𝟙 (Csing A)) (𝟙 (Csing X)) hw2 = 𝟙 _ := by
    apply hepi.left_cancellation
    rw [π_cokernel_map, Category.id_comp, Category.comp_id]
  have key := (descHomotopy (CsingMap i) (CsingMap i) hw1 hw2 H hH).homologyMap_eq n
  rw [hz, ho, HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at key
  exact (IsZero.iff_id_eq_zero _).2 key.symm

end Submission
