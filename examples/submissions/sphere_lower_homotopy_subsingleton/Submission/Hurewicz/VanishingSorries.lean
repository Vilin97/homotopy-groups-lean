/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.Compression
import Submission.WhiteheadTheorem

/-!
# The vanishing theorem

This file completes the chain

`π_*(X, A) = 0  ⟹  H_*(X, A) = 0  ⟹  a weak homotopy equivalence is a homology isomorphism`

from the algebra of `Submission/Hurewicz/Vanishing.lean` and `Submission/Hurewicz/Deformation.lean`
and the geometry of `Submission/Hurewicz/Tower.lean` and `Submission/Hurewicz/Compression.lean`,
in both an unbounded and a bounded form.

The construction is by recursion on the dimension of a simplex, using the homotopy extension
property of `(𝔻 j, ∂𝔻 j)` together with the compression lemma
`TopCat.disk.homotopicRel_boundary_of_unique_pi`, with the reparametrisation schedule
`t_j = 1 - 2 ^ (-(j+1))` making the homotopies compatible with the face maps.  See §5 `HW2` of
`docs/hurewicz-plan.md`.

**Where the bound comes from, and why it is sharp.**  Compressing the `j`-simplices into `A`
consumes `π_rel j (X, A) = 0`, so the hypothesis `π_rel m (X, A) = 0` for `1 ≤ m ≤ M` produces
homotopies which land in `A` exactly in dimensions `≤ M`.  Above `M` the homotopies still exist
and are still compatible with the faces — they simply freeze at time `cutoff M` instead of
compressing — so the chain homotopy `𝟙 ≃ ρ` on `C_*(X)` is *global*, and the bound enters only
through the fact that `ρ` factors through `C_*(A)` in degree `k` exactly when `k ≤ M`.  Hence the
endomorphism induced by `ρ` on `C_*(X, A)` vanishes in degree `k ≤ M`, and therefore so does its
effect on `H_k`, which by the homotopy is the identity.  This gives `H_k(X, A) = 0` for `k ≤ M`,
which is exactly what the relative Hurewicz theorem gives for an `M`-connected pair — the bound
cannot be improved, since already `H_{M+1}(X, A) ≅ π_{M+1}(X, A)` there.

## Main results

* `Submission.exists_simplicialCompression`, `Submission.exists_simplicialDeformation` — the
  geometric input, unbounded and bounded;
* `Submission.isZero_HrelSet_of_unique_piRel`, `Submission.isZero_HrelSet_of_unique_piRel_le` —
  `H_k(X, A) = 0`;
* `Submission.isIso_relIota_of_unique_piRel`, `Submission.isIso_relIota_of_unique_piRel_le` —
  `H_k(A) → H_k(X)` is an isomorphism;
* `Submission.isIso_HgrpMap_of_isWeakHomotopyEquiv` — a weak homotopy equivalence induces
  isomorphisms on singular homology;
* `Submission.IsNEquiv`, `Submission.isIso_HgrpMap_of_isNEquiv`,
  `Submission.epi_HgrpMap_of_isNEquiv` — an `M`-equivalence induces isomorphisms on `H_k` for
  `k < M` and an epimorphism for `k = M`.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

noncomputable section

namespace Submission

/-- **The geometric core of the vanishing theorem.**

If every map of pairs `(𝔻 j, ∂𝔻 j) → (X, A)` can be compressed into `A` rel `∂𝔻 j` (which is
what the vanishing of the relative homotopy groups gives) and every point of `X` can be joined to
`A` by a path, then the singular simplices of `X` can be deformed into `A` coherently with the
face maps.

The hypothesis that `A` is nonempty cannot be dropped: `h₀` and `h` are vacuous when `A = ∅`,
while a `SimplicialCompression X ∅` cannot exist unless `X` is empty as well. -/
theorem exists_simplicialCompression (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n : ℕ, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) :
    Nonempty (SimplicialCompression X A) :=
  ⟨compression (fun j => (tower hA h₀ h j).1) (tower_isNext hA h₀ h) (fun n => (tower hA h₀ h n).2)⟩

/-- **The bounded form of the geometric core.**  If the relative homotopy groups
`π_rel m (X, A)` vanish for `1 ≤ m ≤ M`, then the singular simplices of `X` of dimension at most
`M` can be deformed into `A`, coherently with the face maps and coherently with a deformation of
the simplices of all higher dimensions. -/
theorem exists_simplicialDeformation (M : ℕ) (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) :
    Nonempty (SimplicialDeformation X A M) :=
  ⟨deformation (fun j => (towerLE M hA h₀ h j).step) (towerLE_isNext M hA h₀ h) M
    (fun n hn => (towerLE M hA h₀ h n).compresses hn)⟩

/-- **If all relative homotopy groups of `(X, A)` vanish, so does all relative homology.** -/
theorem isZero_HrelSet_of_unique_piRel (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n : ℕ, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (k : ℕ) :
    IsZero (HrelSet k A) :=
  (exists_simplicialCompression X A hA h₀ h).some.isZero_HrelSet k

/-- **If the relative homotopy groups of `(X, A)` vanish up to degree `M`, so does the relative
homology.** -/
theorem isZero_HrelSet_of_unique_piRel_le (M : ℕ) (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (k : ℕ) (hk : k ≤ M) :
    IsZero (HrelSet k A) :=
  (exists_simplicialDeformation M X A hA h₀ h).some.isZero_HrelSet k hk

/-- **If all relative homotopy groups of `(X, A)` vanish, the inclusion `A ↪ X` is a homology
isomorphism.** -/
theorem isIso_relIota_of_unique_piRel (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n : ℕ, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (k : ℕ) :
    IsIso (HgrpMap k (subIncl A)) :=
  (exists_simplicialCompression X A hA h₀ h).some.isIso_relIota k

/-- **If the relative homotopy groups of `(X, A)` vanish up to degree `M`, the inclusion
`A ↪ X` is a homology isomorphism in degrees `k` with `k + 1 ≤ M`.** -/
theorem isIso_relIota_of_unique_piRel_le (M : ℕ) (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (k : ℕ) (hk : k + 1 ≤ M) :
    IsIso (HgrpMap k (subIncl A)) :=
  (exists_simplicialDeformation M X A hA h₀ h).some.isIso_relIota k hk

/-- **If the relative homotopy groups of `(X, A)` vanish up to degree `M`, the inclusion
`A ↪ X` is a homology epimorphism in degrees `k ≤ M`.** -/
theorem epi_relIota_of_unique_piRel_le (M : ℕ) (X : TopCat.{0}) (A : Set X) (hA : A.Nonempty)
    (h₀ : ∀ a : A, Function.Surjective (RelHomotopyGroup.iStar 0 X A a))
    (h : ∀ n < M, ∀ a : A, Nonempty (Unique (π_rel (n + 1) X A a))) (k : ℕ) (hk : k ≤ M) :
    Epi (HgrpMap k (subIncl A)) :=
  (exists_simplicialDeformation M X A hA h₀ h).some.epi_relIota k hk

/-! ### Weak homotopy equivalences -/

section WeakEquiv

variable {X Y : TopCat.{0}} (φ : X ⟶ Y)

/-- The top of the mapping cylinder is exactly the image of the domain. -/
theorem mapCyl_domInclToTop_surjective :
    Function.Surjective (TopCat.MapCyl.domInclToTop φ) := fun a =>
  ⟨(TopCat.MapCyl.domHomeoTop φ).symm a, (TopCat.MapCyl.domHomeoTop φ).apply_symm_apply a⟩

/-- The inclusion of the domain into the top of the mapping cylinder is a homology
isomorphism. -/
theorem isIso_hgrpMap_domInclToTop (n : ℕ) :
    IsIso (HgrpMap n (TopCat.ofHom (TopCat.MapCyl.domInclToTop φ) :
      X ⟶ TopCat.of (TopCat.MapCyl.top φ))) := by
  have heq : (TopCat.ofHom (TopCat.MapCyl.domInclToTop φ) :
      X ⟶ TopCat.of (TopCat.MapCyl.top φ)) =
      (TopCat.isoOfHomeo (TopCat.MapCyl.domHomeoTop φ)).hom := rfl
  rw [heq]
  infer_instance

/-- The retraction of the mapping cylinder is a homology isomorphism. -/
theorem isIso_hgrpMap_retr (n : ℕ) : IsIso (HgrpMap n (TopCat.MapCyl.retr φ)) := by
  have H₁ : TopCat.Homotopy (TopCat.MapCyl.retr φ ≫ TopCat.MapCyl.inl φ)
      (𝟙 (TopCat.MapCyl φ)) := (TopCat.MapCyl.homotopyEquivBase φ).left_inv.some
  have H₂ : TopCat.Homotopy (TopCat.MapCyl.inl φ ≫ TopCat.MapCyl.retr φ) (𝟙 Y) := by
    rw [TopCat.MapCyl.inl_retr_eq_id]
    exact ContinuousMap.Homotopy.refl _
  exact (hgrpIsoOfHomotopyEquiv (TopCat.MapCyl.retr φ) (TopCat.MapCyl.inl φ) H₁ H₂ n).isIso_hom

/-- On singular homology, `φ` factors through the inclusion of the top of its mapping cylinder,
with isomorphisms on either side. -/
theorem hgrpMap_factor (n : ℕ) :
    HgrpMap n φ = HgrpMap n (TopCat.ofHom (TopCat.MapCyl.domInclToTop φ) :
        X ⟶ TopCat.of (TopCat.MapCyl.top φ)) ≫
      HgrpMap n (subIncl (TopCat.MapCyl.top φ)) ≫ HgrpMap n (TopCat.MapCyl.retr φ) := by
  rw [← HgrpMap_comp, ← HgrpMap_comp, ← Category.assoc]
  exact congrArg (HgrpMap n) (TopCat.MapCyl.domIncl_retr_eq φ).symm

variable (hφ : IsWeakHomotopyEquiv φ.hom)

include hφ in
/-- The top of the mapping cylinder is nonempty. -/
theorem nonempty_mapCyl_top : (TopCat.MapCyl.top φ).Nonempty :=
  Set.nonempty_coe_sort.1 (Nonempty.map (fun x => TopCat.MapCyl.domInclToTop φ x) hφ.1)

include hφ in
/-- All relative homotopy groups of the mapping cylinder pair vanish. -/
theorem unique_piRel_mapCyl (n : ℕ) (a : TopCat.MapCyl.top φ) :
    Nonempty (Unique (π_rel (n + 1) (TopCat.MapCyl φ) (TopCat.MapCyl.top φ) a)) := by
  obtain ⟨x₀, rfl⟩ := mapCyl_domInclToTop_surjective φ a
  exact RelHomotopyGroup.unique_pi_mapCyl_of_isWeakHomotopyEquiv n φ x₀ hφ

include hφ in
/-- The inclusion of the top of the mapping cylinder is surjective on `π₀`. -/
theorem surjective_iStar_zero_mapCyl (a : TopCat.MapCyl.top φ) :
    Function.Surjective
      (RelHomotopyGroup.iStar 0 (TopCat.MapCyl φ) (TopCat.MapCyl.top φ) a) := by
  obtain ⟨x₀, rfl⟩ := mapCyl_domInclToTop_surjective φ a
  exact (RelHomotopyGroup.bijective_iStar_mapCyl_of_isIso 0 φ x₀
    (isIso_inducedPointedHom_of_isWeakHomotopyEquiv hφ 0 x₀)).2

include hφ in
/-- **A weak homotopy equivalence induces isomorphisms on singular homology.** -/
theorem isIso_HgrpMap_of_isWeakHomotopyEquiv (n : ℕ) : IsIso (HgrpMap n φ) := by
  haveI hsub : IsIso (HgrpMap n (subIncl (TopCat.MapCyl.top φ))) :=
    isIso_relIota_of_unique_piRel (TopCat.MapCyl φ) (TopCat.MapCyl.top φ)
      (nonempty_mapCyl_top φ hφ) (surjective_iStar_zero_mapCyl φ hφ)
      (unique_piRel_mapCyl φ hφ) n
  haveI := isIso_hgrpMap_domInclToTop φ n
  haveI := isIso_hgrpMap_retr φ n
  rw [hgrpMap_factor φ n]
  infer_instance

end WeakEquiv

/-! ### `n`-equivalences -/

private theorem surj_of_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (h : Function.Surjective (g ∘ f)) : Function.Surjective g := fun c => by
  obtain ⟨a, ha⟩ := h c
  exact ⟨f a, ha⟩

private theorem surj_of_bij_comp {α β γ : Type} {f : α → β} {g : β → γ}
    (hg : Function.Bijective g) (hgf : Function.Surjective (g ∘ f)) : Function.Surjective f := by
  intro b
  obtain ⟨a, ha⟩ := hgf (g b)
  exact ⟨a, hg.1 ha⟩

/-- A surjectivity-only companion of `RelHomotopyGroup.bijective_iStar_mapCyl_of_isIso`: if `φ`
is surjective on `π_n`, then so is the map induced by the inclusion of the top of its mapping
cylinder.  The vendored library only provides the bijective version, which is what forces the
`n`-equivalence hypothesis below to be stated with an epimorphism in the top degree rather than
an isomorphism. -/
theorem surjective_iStar_mapCyl_of_surjective (n : ℕ) {X Y : TopCat.{0}} (φ : X ⟶ Y) (x₀ : X)
    (hs : Function.Surjective (HomotopyGroup.inducedMap n x₀ φ.hom)) :
    Function.Surjective (RelHomotopyGroup.iStar n (TopCat.MapCyl φ) (TopCat.MapCyl.top φ)
      (TopCat.MapCyl.domInclToTop φ x₀)) := by
  -- Surjectivity on `π_n` passes to the inclusion of the domain into the mapping cylinder,
  -- because the retraction of the cylinder is a homotopy equivalence.
  have f_i_r := HomotopyGroup.inducedPointedHom'_comp_isoTarget_eq_comp n x₀
    (TopCat.MapCyl.domIncl_retr_eq φ).symm
  haveI iso_r : IsIso (HomotopyGroup.inducedPointedHom' n
      (TopCat.MapCyl.domIncl φ x₀) (TopCat.MapCyl.retr φ)) :=
    HomotopyGroup.isIso_inducedPointedHom'_of_isHomotopyEquiv _ _ _
      (TopCat.MapCyl.isHomotopyEquiv_retr φ)
  have hdi : Function.Surjective ⇑(HomotopyGroup.inducedPointedHom' n x₀
      (TopCat.MapCyl.domIncl φ)) := by
    refine surj_of_bij_comp ((Pointed.isIso_iff_bijective _).1 iso_r) ?_
    have h1 : ⇑(HomotopyGroup.inducedPointedHom' n (TopCat.MapCyl.domIncl φ x₀)
          (TopCat.MapCyl.retr φ)) ∘ ⇑(HomotopyGroup.inducedPointedHom' n x₀
          (TopCat.MapCyl.domIncl φ)) =
        ⇑(HomotopyGroup.inducedPointedHom' n x₀ φ ≫
          (HomotopyGroup.inducedPointedHom'.isoTarget n x₀
            (TopCat.MapCyl.domIncl_retr_eq φ).symm).hom) := by
      rw [f_i_r]
      rfl
    rw [h1]
    exact ((Pointed.isIso_iff_bijective _).1 (Iso.isIso_hom _)).2.comp hs
  -- and then to the inclusion of the top, because `X → top φ` is a homeomorphism.
  have hEq := TopCat.MapCyl.domIncl_hom_eq_domInclFromTop_comp_domInclToTop φ
  have i_it_if := HomotopyGroup.inducedPointedHom_comp_isoTarget_eq_comp n x₀ hEq
  rw [← RelHomotopyGroup.inducedPointedHom_subtype_val_eq_iStar]
  intro c
  obtain ⟨b, hb⟩ := ((Pointed.isIso_iff_bijective _).1
    (Iso.isIso_hom (HomotopyGroup.inducedPointedHom.isoTarget n x₀ hEq))).2 c
  obtain ⟨a, ha⟩ := hdi b
  refine ⟨HomotopyGroup.inducedPointedHom n x₀ (TopCat.MapCyl.domInclToTop φ) a, ?_⟩
  have key := ConcreteCategory.congr_hom i_it_if a
  simp only [ConcreteCategory.comp_apply] at key
  refine key.symm.trans (Eq.trans ?_ hb)
  exact congrArg _ ha

/-- `φ` is an `M`-equivalence: its source is nonempty, it induces bijections on the homotopy
groups in degrees `< M` and a surjection in degree `M`.  This is the classical notion. -/
def IsNEquiv (M : ℕ) {X Y : TopCat.{0}} (φ : X ⟶ Y) : Prop :=
  Nonempty X ∧ (∀ n < M, ∀ x : X, Function.Bijective (HomotopyGroup.inducedMap n x φ.hom)) ∧
    ∀ x : X, Function.Surjective (HomotopyGroup.inducedMap M x φ.hom)

section NEquiv

variable {X Y : TopCat.{0}} {φ : X ⟶ Y} {M : ℕ}

/-- A weak homotopy equivalence is an `M`-equivalence for every `M`. -/
theorem isNEquiv_of_isWeakHomotopyEquiv (hφ : IsWeakHomotopyEquiv φ.hom) (M : ℕ) :
    IsNEquiv M φ :=
  ⟨hφ.1, fun n _ x => hφ.2 n x, fun x => (hφ.2 M x).2⟩

namespace IsNEquiv

/-- An `M`-equivalence is surjective on the homotopy groups in all degrees `≤ M`. -/
theorem surjective (hM : IsNEquiv M φ) (n : ℕ) (hn : n ≤ M) (x : X) :
    Function.Surjective (HomotopyGroup.inducedMap n x φ.hom) := by
  rcases lt_or_eq_of_le hn with h | rfl
  · exact (hM.2.1 n h x).2
  · exact hM.2.2 x

theorem isIso_inducedPointedHom (hM : IsNEquiv M φ) (n : ℕ) (hn : n < M) (x : X) :
    IsIso (HomotopyGroup.inducedPointedHom n x φ.hom) := by
  apply (Pointed.isIso_iff_bijective _).mpr
  have h := hM.2.1 n hn x
  rwa [HomotopyGroup.inducedMap] at h

/-- The top of the mapping cylinder is nonempty. -/
theorem nonempty_mapCyl_top (hM : IsNEquiv M φ) : (TopCat.MapCyl.top φ).Nonempty :=
  Set.nonempty_coe_sort.1 (Nonempty.map (fun x => TopCat.MapCyl.domInclToTop φ x) hM.1)

/-- The relative homotopy groups of the mapping cylinder pair vanish up to degree `M`. -/
theorem unique_piRel_mapCyl (hM : IsNEquiv M φ) (n : ℕ) (hn : n < M)
    (a : TopCat.MapCyl.top φ) :
    Nonempty (Unique (π_rel (n + 1) (TopCat.MapCyl φ) (TopCat.MapCyl.top φ) a)) := by
  obtain ⟨x₀, rfl⟩ := mapCyl_domInclToTop_surjective φ a
  exact ExactSeq.unique_mid_of_five
    (RelHomotopyGroup.iStar (n + 1) _ _ _)
    (RelHomotopyGroup.jStar (n + 1) _ _ _)
    (RelHomotopyGroup.bd n _ _ _)
    (RelHomotopyGroup.iStar n _ _ _)
    (surjective_iStar_mapCyl_of_surjective (n + 1) φ x₀ (hM.surjective (n + 1) hn x₀))
    (RelHomotopyGroup.bijective_iStar_mapCyl_of_isIso n φ x₀
      (hM.isIso_inducedPointedHom n (by omega) x₀)).injective
    (RelHomotopyGroup.isExactAt_iStar_jStar n _ _ _)
    (RelHomotopyGroup.isExactAt_jStar_bd n _ _ _)
    (RelHomotopyGroup.isExactAt_bd_iStar n _ _ _)

/-- The inclusion of the top of the mapping cylinder is surjective on `π₀`. -/
theorem surjective_iStar_zero_mapCyl (hM : IsNEquiv M φ) (a : TopCat.MapCyl.top φ) :
    Function.Surjective
      (RelHomotopyGroup.iStar 0 (TopCat.MapCyl φ) (TopCat.MapCyl.top φ) a) := by
  obtain ⟨x₀, rfl⟩ := mapCyl_domInclToTop_surjective φ a
  exact surjective_iStar_mapCyl_of_surjective 0 φ x₀ (hM.surjective 0 (Nat.zero_le M) x₀)

end IsNEquiv

/-- **An `M`-equivalence induces isomorphisms on singular homology in degrees `k < M`.** -/
theorem isIso_HgrpMap_of_isNEquiv (hM : IsNEquiv M φ) (n : ℕ) (hn : n < M) :
    IsIso (HgrpMap n φ) := by
  haveI hsub : IsIso (HgrpMap n (subIncl (TopCat.MapCyl.top φ))) :=
    isIso_relIota_of_unique_piRel_le M (TopCat.MapCyl φ) (TopCat.MapCyl.top φ)
      hM.nonempty_mapCyl_top hM.surjective_iStar_zero_mapCyl
      (fun k hk => hM.unique_piRel_mapCyl k hk) n hn
  haveI := isIso_hgrpMap_domInclToTop φ n
  haveI := isIso_hgrpMap_retr φ n
  rw [hgrpMap_factor φ n]
  infer_instance

/-- **An `M`-equivalence induces epimorphisms on singular homology in degrees `k ≤ M`.** -/
theorem epi_HgrpMap_of_isNEquiv (hM : IsNEquiv M φ) (n : ℕ) (hn : n ≤ M) :
    Epi (HgrpMap n φ) := by
  haveI hsub : Epi (HgrpMap n (subIncl (TopCat.MapCyl.top φ))) :=
    epi_relIota_of_unique_piRel_le M (TopCat.MapCyl φ) (TopCat.MapCyl.top φ)
      hM.nonempty_mapCyl_top hM.surjective_iStar_zero_mapCyl
      (fun k hk => hM.unique_piRel_mapCyl k hk) n hn
  haveI := isIso_hgrpMap_domInclToTop φ n
  haveI := isIso_hgrpMap_retr φ n
  rw [hgrpMap_factor φ n]
  infer_instance

end NEquiv

end Submission
