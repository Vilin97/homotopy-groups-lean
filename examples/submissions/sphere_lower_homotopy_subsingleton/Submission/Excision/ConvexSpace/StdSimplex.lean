/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import Submission.Excision.Perm.EquivSucc
public import Submission.Excision.ConvexSpace.AffineMap
public import Submission.Excision.Finsupp.Basic
public import Submission.Excision.Fin.Vec

/-!
# API for the standard simplex

-/

@[expose] public section

namespace Convexity

namespace StdSimplex

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

instance {M : Type*} [IsEmpty M] : IsEmpty (StdSimplex R M) where
  false x := by
    have hx : x.weights = 0 := by ext m; exfalso; exact IsEmpty.false m
    simpa [hx] using x.total

lemma eq_single_of_subsingleton
    {M : Type*} [Subsingleton M] (x : StdSimplex R M) (m : M) :
    x = .single m := by
  ext i
  obtain rfl := Subsingleton.elim m i
  simp only [weights_single, Finsupp.single_eq_same, ← x.total]
  rw [Finsupp.sum_eq_single _ ?_ (by simp)]
  intro i
  obtain rfl := Subsingleton.elim m i
  simp

instance {M : Type*} [Subsingleton M] :
    Subsingleton (StdSimplex R M) where
  allEq x y := by
    by_cases h : IsEmpty M
    · exfalso
      exact IsEmpty.false x
    · simp only [not_isEmpty_iff] at h
      simp [eq_single_of_subsingleton _ (Classical.arbitrary _)]

instance {M : Type*} [Nonempty M] :
    Nonempty (StdSimplex R M) :=
  ⟨.single (Classical.arbitrary _)⟩

@[elab_as_elim, induction_eliminator]
lemma rec' {M : Type*} {motive : StdSimplex R M → Prop}
    (sum : ∀ (n : ℕ) (w : Fin n → R) (m : Fin n → M) (_ : Function.Injective m)
      (hw₀ : ∀ i, 0 < w i) (hw : ∑ i, w i = 1),
      motive
        { weights := ∑ i, .single (m i) (w i)
          nonneg := Finset.sum_nonneg (fun i _ ↦ by simpa using (hw₀ i).le)
          total := by
            rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp)]
            simpa })
    (s : StdSimplex R M) : motive s := by
  induction s with
  | mk w hw₀ hw =>
    induction w using Finsupp.rec' with
    | sum n m a ha ha' =>
      refine sum n a m ha (fun i ↦ ?_) ?_
      · rw [lt_iff_le_and_ne']
        refine ⟨?_, ha' _⟩
        rw [Finsupp.le_def] at hw₀
        specialize hw₀ (m i)
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
          Finset.sum_apply] at hw₀
        rw [Finset.sum_eq_single i (fun j _ hj ↦ Finsupp.single_eq_of_ne' (ha.ne hj))
          (by simp)] at hw₀
        simpa using hw₀
      · rw [← hw, Finsupp.sum_finsetSum _ _ _ (by simp) (by simp)]
        simp
@[simp]
lemma iConvexComb_single {M : Type*} (x : StdSimplex R M) :
    x.iConvexComb single = x := by
  aesop

@[ext]
lemma affineMap_ext {M : Type*} {Y : Type*} [ConvexSpace R Y]
    {f g : ConvexSpace.AffineMap R (StdSimplex R M) Y}
    (h : ∀ (i : M), f (.single i) = g (.single i)) : f = g := by
  ext x
  conv_lhs => rw [← iConvexComb_single x]
  conv_rhs => rw [← iConvexComb_single x]
  rw [f.isAffineMap.map_iConvexComb, g.isAffineMap.map_iConvexComb]
  aesop

/-- The (bundled) affine map `StdSimplex R M → StdSimplex R N` induced
by a map `f : M → N`. -/
noncomputable def affineMap {M N : Type*} (f : M → N) :
    ConvexSpace.AffineMap R (StdSimplex R M) (StdSimplex R N) where
  toFun := map f

@[simp]
lemma coe_affineMap {M N : Type*} (f : M → N) :
    ⇑(affineMap (R := R) f) = map f := rfl

@[simp]
lemma affineMap_id (M : Type*) :
    affineMap (R := R) (id : M → M) = .id _ := by
  aesop

lemma mem_range_affineMap {M N : Type*} (s : StdSimplex R N) (f : M → N)
    (hf : ∀ (n : N), s.weights n ≠ 0 → n ∈ Set.range f) :
    s ∈ Set.range (StdSimplex.affineMap f) := by
  induction s using rec' with
  | sum n w p hp hw₀ hw =>
    have (i : Fin n) : ∃ (m : M), f m = p i :=
      hf _ (by
        dsimp
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        rw [Finset.sum_eq_single i (fun j _ hj ↦ by
          rw [Finsupp.single_apply_eq_zero]
          exact fun h ↦ (hj (hp h.symm)).elim) (by simp), Finsupp.single_eq_same]
        exact (hw₀ i).ne')
    choose m hm using this
    refine ⟨{
      weights := ∑ (i : Fin n), .single (m i) (w i)
      nonneg := Finset.sum_nonneg' (fun i ↦ by simpa using (hw₀ i).le)
      total := by
        rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp)]
        simpa}, ?_⟩
    ext x
    simp only [coe_affineMap, weights_map, Finsupp.coe_finsetSum, Finset.sum_apply]
    by_cases hx : x ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hx
      nth_rw 2 [Finset.sum_eq_single i]
      · simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_eq_same]
        rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp)]
        simp only [hm, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.sum_single_index]
        rw [Finset.sum_eq_single i
          (fun j _ hj ↦ Finsupp.single_eq_of_ne (hp.ne hj.symm)) (by simp), Finsupp.single_eq_same]
      · intro j _ hj
        exact Finsupp.single_eq_of_ne (fun h ↦ hj (hp h.symm))
      · simp
    · rw [Finsupp.mapDomain_of_not_mem_image_support,
        Finset.sum_eq_zero (fun _ _ ↦ Finsupp.single_eq_of_ne (by grind))]
      simp only [Set.mem_image, SetLike.mem_coe, Finsupp.mem_support_iff, Finsupp.coe_finsetSum,
        Finset.sum_apply, ne_eq, not_exists, not_and]
      intro x hx' rfl
      apply hx'
      rw [Finset.sum_eq_zero]
      intro i _
      apply Finsupp.single_eq_of_ne
      rintro rfl
      simp [← hm] at hx

@[simp]
lemma sConvexComb_map_iConvexComb {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R (StdSimplex R M)) :
    sConvexComb (map (fun s ↦ iConvexComb s f) s) = iConvexComb (sConvexComb s) f :=
  calc
    _ = iConvexComb s fun s ↦ sConvexComb (map f s) := sConvexComb_map _ _
    _ = sConvexComb (map f (sConvexComb s)) := by
        rw [StdSimplex.map_sConvexComb, sConvexComb_sConvexComb, sConvexComb_map,
          iConvexComb_map]

/-- Constructor for (bundled) affine maps from a standard simplex to a convex space. -/
noncomputable def affineMapMk {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) :
    ConvexSpace.AffineMap R (StdSimplex R M) Y where
  toFun s := iConvexComb s f
  isAffineMap_toFun.map_sConvexComb s := by simp

lemma affineMapMk_apply {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y)
    (s : StdSimplex R M) :
    affineMapMk (R := R) f s = iConvexComb s f := rfl

@[simp]
lemma affineMapMk_single {M : Type*} {Y : Type*} [ConvexSpace R Y] (f : M → Y) (m : M) :
    affineMapMk (R := R) f (.single m) = f m := by
  simp [affineMapMk_apply]

lemma affineMapMk_surjective {M : Type*} {Y : Type*} [ConvexSpace R Y]
    (s : ConvexSpace.AffineMap R (StdSimplex R M) Y) :
    ∃ (f : M → Y), affineMapMk f = s :=
  ⟨fun i ↦ s (single i), by ext; simp [affineMapMk_apply]⟩

lemma comp_affineMapMk {M : Type*} {Y Z : Type*} [ConvexSpace R Y] [ConvexSpace R Z]
    (f : ConvexSpace.AffineMap R Y Z) (g : M → Y) :
    f.comp (affineMapMk g) = affineMapMk (f ∘ g) := by
  aesop

lemma affineMapMk_apply_eq_sum
    {M : Type*} [Fintype M] {E : Type*} [AddCommMonoid E] [Module R E] [ConvexSpace R E]
    [IsModuleConvexSpace R E]
    (f : M → E) (s : StdSimplex R M) :
    affineMapMk (R := R) f s = ∑ (m : M), s.weights m • f m := by
  rw [affineMapMk_apply, iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (by simp)]

/-- In the standard simplex with vertices `M`, this is the isobarycenter of
a nonempty finite subset `S` of `M`. -/
@[simps]
noncomputable def subIsobarycenter
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m S.card⁻¹)
  nonneg := Finset.sum_nonneg (by simp)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simpa using IsUnit.mul_inv_cancel (Ne.isUnit (by simpa [← Finset.nonempty_iff_ne_empty]))

lemma subIsobarycenter_weights_apply_eq_zero
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} (S : Finset M) (hS : S.Nonempty) (m : M) (hm : m ∉ S) :
    (subIsobarycenter (K := K) S hS).weights m = 0 := by
  simp only [weights_subIsobarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_zero]
  intro x hx
  rw [Finsupp.single_apply_eq_zero]
  rintro rfl
  exact (hm hx).elim

@[simp]
lemma subIsobarycenter_singleton
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} (m : M) :
    subIsobarycenter (K := K) {m} (by simp) = .single m := by
  aesop

lemma map_subIsobarycenter_of_injective
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M N : Type*} [DecidableEq N] (S : Finset M) (hS : S.Nonempty)
    (f : M → N) (hf : Function.Injective f) :
    map f (subIsobarycenter (K := K) S hS) =
      subIsobarycenter (Finset.image f S) (by simpa) := by
  -- there must be a better proof
  ext n
  simp only [weights_map, weights_subIsobarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases! hn : ∃ (m : M) (hm : m ∈ S), f m = n
  · obtain ⟨m, hm, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply hf, Finset.sum_image hf.injOn,
      Finsupp.coe_finsetSum, Finset.sum_apply]
    congr
    ext x
    by_cases hx : m = x
    · subst hx
      simp [Finset.card_image_of_injective S hf]
    · rw [Finsupp.single_eq_of_ne hx, Finsupp.single_eq_of_ne
        (fun h ↦ hx (hf h))]
  · rw [Finsupp.mapDomain_of_not_mem_image_support,
      Finset.sum_eq_zero]
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨x, hx, rfl⟩ := hx
      rw [Finsupp.single_apply_eq_zero]
      intro h
      exact (hn x hx h.symm).elim
    · simp only [Set.mem_image, SetLike.mem_coe, Finsupp.mem_support_iff, Finsupp.coe_finsetSum,
        Finset.sum_apply, ne_eq, not_exists, not_and]
      by_contra!
      obtain ⟨m, hm, rfl⟩ := this
      replace hn : m ∉ S := fun h ↦ by simpa using hn _ h
      apply hm
      rw [Finset.sum_eq_zero]
      intro x hx
      rw [Finsupp.single_apply_eq_zero]
      rintro rfl
      tauto

/-- The isobarycenter of the standard simplex. -/
noncomputable abbrev isobarycenter
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} [Nonempty M] [Fintype M] : StdSimplex K M :=
  subIsobarycenter .univ (by simp)

lemma isobarycenter_of_unique
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
    {M : Type*} [Unique M] :
    isobarycenter (K := K) (M := M) = .single default := by
  subsingleton

@[simp]
lemma isobarycenter_fin_one
    {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] :
    isobarycenter (K := K) (M := Fin 1) = .single 0 :=
  isobarycenter_of_unique

end StdSimplex

namespace ConvexSpace.AffineMap

variable {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  {Y : Type*} [ConvexSpace K Y] {Z : Type*} [ConvexSpace K Z]

section

variable {M : Type*} (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)

/-- Given an affine map from the standard simplex with vertices `M` and
a nonempty finite subset `S` of `M`, this is the image of the isobarycenter
of the face of the standard simplex corresponding to `S`. -/
noncomputable def subIsobarycenter (S : Finset M) (hS : S.Nonempty) : Y :=
  f (.subIsobarycenter S hS)

@[simp]
lemma subIsobarycenter_single (m : M) :
    f.subIsobarycenter {m} (by simp) = f (.single m) := by
  simp [subIsobarycenter]

lemma subIsobarycenter_comp_of_injective
    [DecidableEq M] {N : Type*} (S : Finset N) (hS : S.Nonempty)
    (g : N → M) (hg : Function.Injective g) :
    (f.comp (StdSimplex.affineMap (R := K) g)).subIsobarycenter S hS =
      f.subIsobarycenter (Finset.image g S) (by simpa) := by
  simp [subIsobarycenter, StdSimplex.map_subIsobarycenter_of_injective _ _ _ hg]

/-- The image of the isobarycenter of the standard simplex by an affine map. -/
noncomputable abbrev isobarycenter [Nonempty M] [Fintype M] : Y := f .isobarycenter

end

@[simp]
lemma isobarycenter_fin_one (f : ConvexSpace.AffineMap K (StdSimplex K (Fin 1)) Y) :
    f.isobarycenter = f (.single 0) := by
  simp [isobarycenter]

lemma subIsobarycenter_mk_comp_of_injective {M N : Type*} [DecidableEq N]
    (f : N → Y) (S : Finset M) (hS : S.Nonempty) (g : M → N)
    (hg : Function.Injective g) :
    (StdSimplex.affineMapMk (R := K) (f ∘ g)).subIsobarycenter S hS =
      (StdSimplex.affineMapMk (R := K) f).subIsobarycenter (Finset.image g S)
        (by simpa) := by
  rw [← subIsobarycenter_comp_of_injective _ _ hS _ hg]
  congr
  aesop

section

variable {n : ℕ}

/-- Given an affine map `f` from the standard simplex of dimension `n - 1`,
a permutation `σ` of `Fin n` and `i : Fin n`, this is the image by `f`
of the isobarycenter of the face of the standard simplex corresponding
to `{ x : Fin n | i ≤ σ⁻¹ x}` (i.e. `{σ i, σ (i + 1), ..., σ (n - 1)}`). -/
noncomputable def sdVertex
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Y :=
  f.subIsobarycenter { x : Fin n | i ≤ σ⁻¹ x} ⟨σ i, by simp⟩

lemma sdVertex_def (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    f.sdVertex σ i = f.subIsobarycenter { x : Fin n | i ≤ σ⁻¹ x } ⟨σ i, by simp⟩ :=
  rfl

@[simp]
lemma sdVertex_zero
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ 0 = f.isobarycenter := by
  simp [sdVertex_def, subIsobarycenter]

@[simp]
lemma sdVertex_last
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y)
    (σ : Equiv.Perm (Fin (n + 1))) :
    f.sdVertex σ (Fin.last n) = f (.single (σ (Fin.last n))) := by
  have : ({ x | σ.symm x = Fin.last n } : Finset _) = {σ (Fin.last n)} := by
    ext
    simp [Equiv.symm_apply_eq]
  simp [sdVertex_def, this]

@[simp]
lemma sdVertex_mk_one (y : Y) (σ : Equiv.Perm (Fin 1)) :
    (StdSimplex.affineMapMk (R := K) ![y]).sdVertex σ = ![y] := by
  ext
  simp [sdVertex_def]

/-- Given an affine map `f` from the standard simplex of dimension `n` to `Y` and
a permutation `σ` of `Fin n`, this is the subdivision of `f` corresponding to `σ`:
this is again an affine map from the standard simplex of dimension `n`, and the
images of the vertices are given by `f.sdVertex σ : Fin n → Y` -/
noncomputable abbrev sd
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) (σ : Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y :=
  StdSimplex.affineMapMk (f.sdVertex σ)

@[simp]
lemma sd_eq_self
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin 1)) Y) (σ : Equiv.Perm (Fin 1)) :
    f.sd σ = f := by
  obtain ⟨f, rfl⟩ := StdSimplex.affineMapMk_surjective f
  obtain ⟨s, rfl⟩ := Fin.exists_vecCons₁ f
  simp [sd]

/-- The composition `sd (σ 0) ∘ ... ∘ sd (σ (k - 1))` of `k` subdivision
operators `sd` on affine maps from the standard simplex to
a convex space `Y`, where `σ : Fin k → Equiv.Perm (Fin n)` is
a family of permutations. -/
@[no_expose]
noncomputable def sdIter (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin k → Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y := by
  induction k generalizing f with
  | zero => exact f
  | succ k hk => exact (hk f (σ ∘ Fin.succ)).sd (σ 0)

@[simp]
lemma sdIter_zero
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Fin 0 → Equiv.Perm (Fin n)) :
    f.sdIter σ = f := by
  rfl

lemma sdIter_succ
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin (k + 1) → Equiv.Perm (Fin n)) :
    f.sdIter σ = (f.sdIter (σ ∘ Fin.succ)).sd (σ 0) := by
  rfl

lemma sdIter_succ'
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin (k + 1) → Equiv.Perm (Fin n)) :
    f.sdIter σ = (f.sd (σ (Fin.last _))).sdIter (σ ∘ Fin.castSucc) := by
  induction k generalizing f with
  | zero => simp [sdIter_succ]
  | succ k hk =>
    rw [sdIter_succ]
    nth_rw 2 [sdIter_succ]
    congr 1
    rw [hk]
    rfl

@[simp]
lemma sdIter_one
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Fin 1 → Equiv.Perm (Fin n)) :
    f.sdIter σ = f.sd (σ 0) := by
  rfl

variable (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
  (σ : Equiv.Perm (Fin n))
  (g : ConvexSpace.AffineMap K Y Z)

lemma comp_sd (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (g : ConvexSpace.AffineMap K Y Z) :
    g.comp (f.sd σ) = (g.comp f).sd σ := by
  rw [StdSimplex.comp_affineMapMk]
  rfl

lemma comp_sdIter (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin n))
    (g : ConvexSpace.AffineMap K Y Z) :
    g.comp (f.sdIter σ) = (g.comp f).sdIter σ := by
  induction k with
  | zero => simp
  | succ k hk => simp [sdIter_succ, comp_sd, hk]

section

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R Y]
  (f : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 2))) Y) (i : Fin (n + 2))

/-- A face of an affine map from the standard simplex. -/
noncomputable def δ : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y :=
  f.comp (StdSimplex.affineMap i.succAbove)

lemma δ_def : f.δ i = f.comp (StdSimplex.affineMap i.succAbove) := rfl

@[simp]
lemma δ_single (j : Fin (n + 1)) :
    (f.δ i) (.single j) = f (.single (i.succAbove j)) := by
  simp [δ_def]

end

open Equiv.Perm in
lemma sd_δ
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    (f.δ i).sd σ = (f.sd (equivSuccSymm i σ)).δ 0 := by
  ext j
  simp only [δ_single, Fin.zero_succAbove, StdSimplex.affineMapMk_single,
    sdVertex_def, f.δ_def]
  rw [f.subIsobarycenter_comp_of_injective _ ⟨σ j, by simp⟩ _
    Fin.succAbove_right_injective]
  congr
  ext k
  simp only [coe_inv, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨k, rfl⟩ := σ.surjective k
    simpa using hk
  · obtain ⟨k, rfl⟩ := (equivSuccSymm i σ).surjective k
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (by grind)
    simpa using h

open Equiv.Perm in
lemma exists_sdIter_δ_eq
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    ∃ (σ' : Fin k → Equiv.Perm (Fin (n + 2))) (i' : Fin (n + 2)), (f.δ i).sdIter σ =
      (f.sdIter σ').δ i' := by
  induction k generalizing n with
  | zero => simp
  | succ k hk =>
    obtain ⟨σ', i', h⟩ := hk (f.sd (equivSuccSymm i (σ (Fin.last k)))) 0 (σ ∘ Fin.castSucc)
    refine ⟨Fin.lastCases (equivSuccSymm i (σ (Fin.last k))) σ', i', ?_⟩
    rw [sdIter_succ', sd_δ, h, sdIter_succ', Fin.lastCases_last]
    congr
    aesop

end

end ConvexSpace.AffineMap

end Convexity
