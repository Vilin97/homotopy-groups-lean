/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Path
import Submission.Model.SphereConnected
import Submission.Homology.Wang
import Submission.Homology.Homotopy
import Submission.Homology.Point
import Submission.Homotopy.DiscTrivialisation

/-!
# The Wang sequence of the path fibration over a sphere

We build a `Submission.WangDatum` for the path fibration
`ev₁ : PathSpace (S^{d+1}) x₀ → S^{d+1}`, using

* the two enlarged hemispheres `sphLowerCap d`, `sphUpperCap d` of `S^{d+1}` and their meridian
  contractions (`Submission/Homotopy/ContractionData.lean`);
* the explicit trivialisation of a path fibration over a piece of the base carrying contraction
  data, **and the fact that it restricts** to a smaller piece
  (`Submission/Homotopy/DiscTrivialisation.lean`) — this is what replaces Dold's theorem;
* the product formula `H_{n+d}(F × Sᵈ) ≅ H_{n+d}(F) ⊞ Hₙ(F)`, which is **assumed** here, as
  `Submission.ProdSphereSplitting`, because it is still being built elsewhere.

## The assumed interface

```lean
structure ProdSphereSplitting (F : TopCat.{0}) (d : ℕ) where
  iso (n : ℕ) : Hgrp (n + d) (TopCat.of (↥F × Sph d)) ≅ Hgrp (n + d) F ⊞ Hgrp n F
  iso_fst (n : ℕ) : (iso n).hom ≫ biprod.fst = HgrpMap (n + d) (prodFstMap F (Sph d))
```

That is: the projection `F × Sᵈ → F` is split surjective on homology with complement
`H_{*-d}(F)`. This is exactly the statement of `(H7)` in `docs/informal-proof.md`, in the form
Wang needs (the splitting must be compatible with the projection).

## Main results

* `Submission.pathWangDatum` — the Wang datum of the path fibration;
* `Submission.pathWang_thetaIso` — `Hₙ(Ω S^{d+1}) ≅ H_{n+d}(p⁻¹(D₊))` for every `n`, since the
  path space is contractible. Composing with an identification `H_*(p⁻¹(D₊)) ≅ H_*(Ω S^{d+1})`
  gives the periodicity `H_n(Ω S^{d+1}) ≅ H_{n+d}(Ω S^{d+1})`.
-/

open CategoryTheory Limits AlgebraicTopology unitInterval

noncomputable section

namespace Submission

/-! ### Homology of a homotopy equivalence of plain spaces -/

/-- A homotopy equivalence of topological spaces induces an isomorphism on singular homology. -/
def hgrpIsoOfHEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Hgrp n (TopCat.of X) ≅ Hgrp n (TopCat.of Y) :=
  hgrpIsoOfHomotopyEquiv (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun) e.left_inv.some
    e.right_inv.some n

@[simp] theorem hgrpIsoOfHEquiv_hom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (hgrpIsoOfHEquiv e n).hom = HgrpMap n (TopCat.ofHom e.toFun) := rfl

/-! ### The assumed product formula -/

/-- The projection `F × S → F`, as a morphism of `TopCat`. -/
def prodFstMap (F : TopCat.{0}) (S : Type) [TopologicalSpace S] : TopCat.of (↥F × S) ⟶ F :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The homology of a product with a sphere, in the form the Wang sequence needs: the projection
`F × Sᵈ → F` is split surjective on homology, with complement `H_{*-d}(F)`.

This is `(H7)` of `docs/informal-proof.md`; it is assumed here rather than proved. -/
structure ProdSphereSplitting (F : TopCat.{0}) (d : ℕ) where
  /-- The splitting of `H_{n+d}(F × Sᵈ)`. -/
  iso (n : ℕ) : Hgrp (n + d) (TopCat.of (↥F × Sph d)) ≅ Hgrp (n + d) F ⊞ Hgrp n F
  /-- Its first component is induced by the projection. -/
  iso_fst (n : ℕ) : (iso n).hom ≫ biprod.fst = HgrpMap (n + d) (prodFstMap F (Sph d))

/-! ### The two hemispheres cover the sphere

The geometry is in `Submission/Homotopy/ContractionData.lean`; this is an alias fixing the
argument implicit, which is how the Wang datum below consumes it. -/

variable {d : ℕ}

theorem interior_union_sphCaps :
    interior (sphLowerCap d) ∪ interior (sphUpperCap d) = Set.univ :=
  sphCap_interior_union d

/-! ### The Wang datum of the path fibration -/

variable (d) in
/-- The total space of the path fibration over `S^{d+1}`. -/
abbrev pathTotal (x₀ : Sph (d + 1)) : TopCat.{0} := TopCat.of (PathSpace (Sph (d + 1)) x₀)

variable (d)

/-- The south pole of `S^{d+1}`, as a point of the enlarged lower hemisphere. -/
def southPole : ↥(sphLowerCap d) := capPole d (-1) (1 / 3) (by norm_num) (by norm_num)

/-- The contraction of the enlarged lower hemisphere onto the south pole. -/
def lowerContraction : ContractionData ↥(sphLowerCap d) (southPole d) := sphLowerCapContraction d

variable {d}

variable (x₀ : Sph (d + 1))

/-- `p⁻¹(D₋)`, the part of the path space lying over the enlarged lower hemisphere. -/
def pathA : Set ↥(pathTotal d x₀) := (ev₁ (Sph (d + 1)) x₀) ⁻¹' (sphLowerCap d)

/-- `p⁻¹(D₊)`, the part of the path space lying over the enlarged upper hemisphere. -/
def pathB : Set ↥(pathTotal d x₀) := (ev₁ (Sph (d + 1)) x₀) ⁻¹' (sphUpperCap d)

theorem pathA_inter_pathB :
    (pathA x₀ ∩ pathB x₀ : Set ↥(pathTotal d x₀))
      = (ev₁ (Sph (d + 1)) x₀) ⁻¹' (sphBelt d) := rfl

theorem pathCover : interior (pathA x₀) ∪ interior (pathB x₀) = Set.univ := by
  have hcont : Continuous (ev₁ (Sph (d + 1)) x₀) := (ev₁ (Sph (d + 1)) x₀).continuous
  have hA : (ev₁ (Sph (d + 1)) x₀) ⁻¹' interior (sphLowerCap d) ⊆ interior (pathA x₀) :=
    interior_maximal (Set.preimage_mono interior_subset) (isOpen_interior.preimage hcont)
  have hB : (ev₁ (Sph (d + 1)) x₀) ⁻¹' interior (sphUpperCap d) ⊆ interior (pathB x₀) :=
    interior_maximal (Set.preimage_mono interior_subset) (isOpen_interior.preimage hcont)
  refine Set.eq_univ_of_forall fun γ => ?_
  have hz : ev₁ (Sph (d + 1)) x₀ γ ∈ interior (sphLowerCap d) ∪ interior (sphUpperCap d) := by
    rw [interior_union_sphCaps]; trivial
  rcases hz with h | h
  · exact Or.inl (hA h)
  · exact Or.inr (hB h)

/-! ### The trivialisations -/

theorem sphBelt_subset_lower : sphBelt d ⊆ sphLowerCap d := Set.inter_subset_left

variable (d) in
/-- The south pole of `S^{d+1}`, as a point of the sphere. -/
def southPoleVal : Sph (d + 1) := ((southPole d : ↥(sphLowerCap d)) : Sph (d + 1))

/-- The fibre of the path fibration over the south pole. -/
abbrev pathFib : TopCat.{0} := TopCat.of (PathFibre (Sph (d + 1)) x₀ (southPoleVal d))

/-- The trivialisation of `p⁻¹(D₋)` over the enlarged lower hemisphere. -/
def trivA : ContinuousMap.HomotopyEquiv ↥(pathA x₀) (↥(pathFib x₀) × ↥(sphLowerCap d)) :=
  homotopyEquivOverDisc (x₀ := x₀) (lowerContraction d) (subset_refl (sphLowerCap d))

/-- The trivialisation of `p⁻¹(D₋ ∩ D₊)`, obtained by restricting the one over `D₋`. -/
def trivAB : ContinuousMap.HomotopyEquiv ↥(pathA x₀ ∩ pathB x₀)
    (↥(pathFib x₀) × ↥(sphBelt d)) :=
  homotopyEquivOverDisc (x₀ := x₀) (lowerContraction d) sphBelt_subset_lower

/-- The trivialisation of `p⁻¹(D₋)`, as a morphism of `TopCat`. -/
def trivAMap : TopCat.of ↥(pathA x₀) ⟶ TopCat.of (↥(pathFib x₀) × ↥(sphLowerCap d)) :=
  TopCat.ofHom (trivA x₀).toFun

/-- The trivialisation of `p⁻¹(D₋ ∩ D₊)`, as a morphism of `TopCat`. -/
def trivABMap : TopCat.of ↥(pathA x₀ ∩ pathB x₀) ⟶ TopCat.of (↥(pathFib x₀) × ↥(sphBelt d)) :=
  TopCat.ofHom (trivAB x₀).toFun

instance : ContractibleSpace ↥(sphLowerCap d) :=
  ContractionData.contractibleSpace (lowerContraction d)

theorem prodHomotopyEquivOfContractible_toFun (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace Y] :
    (prodHomotopyEquivOfContractible X Y).toFun = ⟨Prod.fst, continuous_fst⟩ :=
  ContinuousMap.ext fun _ => rfl

/-- `H_*(p⁻¹(D₋)) ≅ H_*(F)`: the enlarged lower hemisphere is contractible. -/
def isoAF (n : ℕ) : Hgrp n (TopCat.of ↥(pathA x₀)) ≅ Hgrp n (pathFib x₀) :=
  (hgrpIsoOfHEquiv (trivA x₀) n).trans
    (hgrpIsoOfHEquiv (prodHomotopyEquivOfContractible ↥(pathFib x₀) ↥(sphLowerCap d)) n)

theorem isoAF_hom (n : ℕ) :
    (isoAF x₀ n).hom
      = HgrpMap n (trivAMap x₀ ≫ prodFstMap (pathFib x₀) ↥(sphLowerCap d)) := by
  rw [isoAF, Iso.trans_hom, hgrpIsoOfHEquiv_hom, hgrpIsoOfHEquiv_hom, ← HgrpMap_comp]
  congr 2

/-- The key compatibility: the trivialisation over `D₋` restricts to `D₋ ∩ D₊`. -/
theorem trivialisation_square :
    mvInclLeft (pathA x₀) (pathB x₀) ≫ trivAMap x₀ ≫ prodFstMap (pathFib x₀) ↥(sphLowerCap d)
      = trivABMap x₀ ≫ prodFstMap (pathFib x₀) ↥(sphBelt d) := by
  refine TopCat.hom_ext (ContinuousMap.ext fun δ => ?_)
  exact (untrivialiseOver_restrict (x₀ := x₀) (lowerContraction d)
    (subset_refl (sphLowerCap d)) sphBelt_subset_lower δ).symm

/-! ### The splitting of the homology of the overlap -/

/-- Identify the overlap with `F × Sᵈ`. -/
def beltProdEquiv : ContinuousMap.HomotopyEquiv (↥(pathFib x₀) × ↥(sphBelt d))
    (↥(pathFib x₀) × Sph d) :=
  (ContinuousMap.HomotopyEquiv.refl _).prodCongr (sphBeltHomotopyEquiv d)

theorem beltProdEquiv_fst :
    TopCat.ofHom (beltProdEquiv x₀).toFun ≫ prodFstMap (pathFib x₀) (Sph d)
      = prodFstMap (pathFib x₀) ↥(sphBelt d) :=
  TopCat.hom_ext (ContinuousMap.ext fun _ => rfl)

variable (P : ProdSphereSplitting (pathFib x₀) d)

/-- The splitting `H_{n+d}(p⁻¹(D₋ ∩ D₊)) ≅ H_{n+d}(p⁻¹(D₋)) ⊞ Hₙ(F)`. -/
def pathSplit (n : ℕ) :
    Hgrp (n + d) (TopCat.of ↥(pathA x₀ ∩ pathB x₀))
      ≅ Hgrp (n + d) (TopCat.of ↥(pathA x₀)) ⊞ Hgrp n (pathFib x₀) :=
  (hgrpIsoOfHEquiv (trivAB x₀) (n + d)).trans
    (((hgrpIsoOfHEquiv (beltProdEquiv x₀) (n + d)).trans (P.iso n)).trans
      (biprod.mapIso (isoAF x₀ (n + d)).symm (Iso.refl (Hgrp n (pathFib x₀)))))

theorem pathSplit_fst (n : ℕ) :
    (pathSplit x₀ P n).hom ≫ biprod.fst
      = HgrpMap (n + d) (mvInclLeft (pathA x₀) (pathB x₀)) := by
  have key : (TopCat.ofHom (trivAB x₀).toFun ≫ TopCat.ofHom (beltProdEquiv x₀).toFun)
        ≫ prodFstMap (pathFib x₀) (Sph d)
      = mvInclLeft (pathA x₀) (pathB x₀)
        ≫ (trivAMap x₀ ≫ prodFstMap (pathFib x₀) ↥(sphLowerCap d)) := by
    rw [Category.assoc, beltProdEquiv_fst]
    exact (trivialisation_square x₀).symm
  rw [pathSplit]
  simp only [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst,
    hgrpIsoOfHEquiv_hom, Iso.symm_hom]
  rw [← Category.assoc (P.iso n).hom, P.iso_fst]
  rw [← Category.assoc, ← Category.assoc, ← HgrpMap_comp, ← HgrpMap_comp, key,
    HgrpMap_comp, ← isoAF_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ### The Wang datum -/

/-- **The Wang datum of the path fibration over `S^{d+1}`.** -/
def pathWangDatum : WangDatum (pathTotal d x₀) d where
  A := pathA x₀
  B := pathB x₀
  cover := pathCover x₀
  fibre := pathFib x₀
  split := pathSplit x₀ P
  split_fst := pathSplit_fst x₀ P

/-- The path space is contractible, so its homology vanishes in positive degrees. -/
theorem isZero_pathTotal (k : ℕ) (hk : 0 < k) : IsZero (Hgrp k (pathTotal d x₀)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact isZero_Hgrp_of_contractible (X := pathTotal d x₀) m

/-- **The Wang isomorphism for the path fibration**: since the path space is contractible, the
Wang map is an isomorphism `Hₙ(F) ≅ H_{n+d}(p⁻¹(D₊))` whenever `0 < n + d`. Here
`F = Ω S^{d+1}` is the fibre over the south pole. -/
def pathWangThetaIso (n : ℕ) (hn : 0 < n + d) :
    Hgrp n (pathFib x₀) ≅ Hgrp (n + d) (TopCat.of ↥(pathB x₀)) :=
  (pathWangDatum x₀ P).thetaIso n (isZero_pathTotal x₀ (n + d + 1) (by omega))
    (isZero_pathTotal x₀ (n + d) hn)

/-! ### The fibre over the north pole, and comparison of the two fibres -/

variable (d) in
/-- The north pole of `S^{d+1}`, as a point of the enlarged upper hemisphere. -/
def northPole : ↥(sphUpperCap d) := capPole d 1 (1 / 3) (by norm_num) (by norm_num)

variable (d) in
/-- The contraction of the enlarged upper hemisphere onto the north pole. -/
def upperContraction : ContractionData ↥(sphUpperCap d) (northPole d) := sphUpperCapContraction d

variable (d) in
/-- The north pole of `S^{d+1}`, as a point of the sphere. -/
def northPoleVal : Sph (d + 1) := ((northPole d : ↥(sphUpperCap d)) : Sph (d + 1))

instance : ContractibleSpace ↥(sphUpperCap d) :=
  ContractionData.contractibleSpace (upperContraction d)

/-- The trivialisation of `p⁻¹(D₊)` over the enlarged upper hemisphere. -/
def trivB : ContinuousMap.HomotopyEquiv ↥(pathB x₀)
    (PathFibre (Sph (d + 1)) x₀ (northPoleVal d) × ↥(sphUpperCap d)) :=
  homotopyEquivOverDisc (x₀ := x₀) (upperContraction d) (subset_refl (sphUpperCap d))

/-- The fibre over a point `q` of a piece carrying contraction data is homotopy equivalent to the
fibre over the base point of that piece: it is the trivialisation over the subset `{q}`. -/
def pathFibreEquivOfMem {X : Type} [TopologicalSpace X] {x₀ : X} {D : Set X} {b₀ : ↥D}
    (c : ContractionData ↥D b₀) {q : X} (hq : q ∈ D) :
    ContinuousMap.HomotopyEquiv (PathFibre X x₀ q) (PathFibre X x₀ (b₀ : X)) :=
  (homotopyEquivOverDisc (x₀ := x₀) c (Set.singleton_subset_iff.mpr hq)).trans
    (Homeomorph.prodUnique (PathFibre X x₀ (b₀ : X)) ↥({q} : Set X)).toHomotopyEquiv

variable (d) in
/-- A chosen point of the belt `D₋ ∩ D₊`. -/
def beltPointSub : ↥(sphBelt d) :=
  beltOfProd (Classical.arbitrary (Sph d), ⟨0, by rw [Set.mem_Icc]; norm_num⟩)

variable (d) in
/-- The chosen point of the belt, as a point of the sphere. -/
def beltPoint : Sph (d + 1) := ((beltPointSub d : ↥(sphBelt d)) : Sph (d + 1))

theorem beltPoint_mem_lower : beltPoint d ∈ sphLowerCap d := (beltPointSub d).2.1

theorem beltPoint_mem_upper : beltPoint d ∈ sphUpperCap d := (beltPointSub d).2.2

/-- The fibres over the two poles are homotopy equivalent, compared through the fibre over a point
of the belt (which lies in both hemispheres). -/
def poleFibreEquiv : ContinuousMap.HomotopyEquiv
    (PathFibre (Sph (d + 1)) x₀ (northPoleVal d)) (PathFibre (Sph (d + 1)) x₀ (southPoleVal d)) :=
  (pathFibreEquivOfMem (x₀ := x₀) (upperContraction d) (beltPoint_mem_upper (d := d))).symm.trans
    (pathFibreEquivOfMem (x₀ := x₀) (lowerContraction d) (beltPoint_mem_lower (d := d)))

/-- **`H_*(p⁻¹(D₊)) ≅ H_*(F)`**, where `F` is the fibre over the south pole. -/
def isoB (n : ℕ) : Hgrp n (TopCat.of ↥(pathB x₀)) ≅ Hgrp n (pathFib x₀) :=
  ((hgrpIsoOfHEquiv (trivB x₀) n).trans
      (hgrpIsoOfHEquiv (prodHomotopyEquivOfContractible
        (PathFibre (Sph (d + 1)) x₀ (northPoleVal d)) ↥(sphUpperCap d)) n)).trans
    (hgrpIsoOfHEquiv (poleFibreEquiv x₀) n)

/-- **The periodicity of `H_*(Ω S^{d+1})`**: the Wang map is an isomorphism
`Hₙ(F) ≅ H_{n+d}(F)` in every degree with `0 < n + d`. -/
def pathWangPeriodicity (n : ℕ) (hn : 0 < n + d) :
    Hgrp n (pathFib x₀) ≅ Hgrp (n + d) (pathFib x₀) :=
  (pathWangDatum x₀ P).thetaFIso (isoB x₀) n (isZero_pathTotal x₀ (n + d + 1) (by omega))
    (isZero_pathTotal x₀ (n + d) hn)

/-! ### Vanishing below the dimension of the sphere -/

/-- Below the dimension of the sphere, the projection `F × Sᵈ → F` is a homology isomorphism.
This is the low-degree complement of `ProdSphereSplitting`, and like it, it is assumed here. -/
def ProdSphereLowIso (F : TopCat.{0}) (d : ℕ) : Prop :=
  ∀ n : ℕ, n < d → IsIso (HgrpMap n (prodFstMap F (Sph d)))

theorem isIso_mvInclLeft_of_lt (L : ProdSphereLowIso (pathFib x₀) d) (k : ℕ) (hk : k < d) :
    IsIso (HgrpMap k (mvInclLeft (pathA x₀) (pathB x₀))) := by
  have hprod : IsIso (HgrpMap k (prodFstMap (pathFib x₀) (Sph d))) := L k hk
  have hbe : IsIso (HgrpMap k (TopCat.ofHom (beltProdEquiv x₀).toFun)) :=
    (hgrpIsoOfHEquiv (beltProdEquiv x₀) k).isIso_hom
  have hbelt : IsIso (HgrpMap k (prodFstMap (pathFib x₀) ↥(sphBelt d))) := by
    rw [← beltProdEquiv_fst, HgrpMap_comp]
    infer_instance
  have hab : IsIso (HgrpMap k (trivABMap x₀)) := (hgrpIsoOfHEquiv (trivAB x₀) k).isIso_hom
  have hAF : IsIso ((isoAF x₀ k).hom) := (isoAF x₀ k).isIso_hom
  have key : IsIso (HgrpMap k (mvInclLeft (pathA x₀) (pathB x₀)) ≫ (isoAF x₀ k).hom) := by
    rw [isoAF_hom, ← HgrpMap_comp, trivialisation_square, HgrpMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (isoAF x₀ k).hom

/-- **`H_k(Ω S^{d+1}) = 0` for `0 < k < d`.** -/
theorem isZero_pathFib_of_lt (L : ProdSphereLowIso (pathFib x₀) d) (k : ℕ) (hk0 : 0 < k)
    (hk : k < d) : IsZero (Hgrp k (pathFib x₀)) :=
  IsZero.of_iso
    (isZero_Hgrp_of_isIso_mvInclLeft (pathA x₀) (pathB x₀) (pathCover x₀) k
      (isZero_pathTotal x₀ (k + 1) (by omega)) (isZero_pathTotal x₀ k hk0)
      (isIso_mvInclLeft_of_lt x₀ L k hk))
    (isoB x₀ k).symm

/-! ### Path connectedness of the fibres, and `H₀` -/

/-- The fibre of the path fibration over `b` is the space of paths from `x₀` to `b`. -/
def pathFibreHomeo (X : Type) [TopologicalSpace X] (x₀ b : X) : PathFibre X x₀ b ≃ₜ Path x₀ b where
  toFun γ := { toContinuousMap := γ.1.1, source' := γ.1.2, target' := γ.2 }
  invFun γ := ⟨⟨γ.toContinuousMap, γ.source'⟩, γ.target'⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_induced_rng.2 (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := (continuous_induced_dom.subtype_mk _).subtype_mk _

/-- A homotopy of paths rel endpoints *is* a path in the space of paths. -/
theorem joined_of_pathHomotopy {X : Type*} [TopologicalSpace X] {x₀ b : X} {p q : Path x₀ b}
    (F : Path.Homotopy p q) : Joined p q :=
  ⟨{ toFun := fun t => F.eval t
     continuous_toFun := Path.continuous_uncurry_iff.mp F.continuous
     source' := F.eval_zero
     target' := F.eval_one }⟩

/-- If any two paths from `x₀` to `b` are homotopic rel endpoints, the space of such paths is path
connected. -/
theorem pathConnectedSpace_path {X : Type*} [TopologicalSpace X] {x₀ b : X}
    (hne : Nonempty (Path x₀ b)) (h : ∀ p q : Path x₀ b, Path.Homotopic p q) :
    PathConnectedSpace (Path x₀ b) :=
  ⟨hne, fun p q => joined_of_pathHomotopy (h p q).some⟩

/-- **The fibre of the path fibration over `b` is path connected** when the base is simply
connected in the sense that any two paths with the same endpoints are homotopic. -/
theorem pathConnectedSpace_pathFibre {X : Type} [TopologicalSpace X] {x₀ b : X}
    (hne : Nonempty (Path x₀ b)) (h : ∀ p q : Path x₀ b, Path.Homotopic p q) :
    PathConnectedSpace (PathFibre X x₀ b) :=
  haveI := pathConnectedSpace_path hne h
  Function.Surjective.pathConnectedSpace (f := (pathFibreHomeo X x₀ b).symm)
    (pathFibreHomeo X x₀ b).symm.surjective (pathFibreHomeo X x₀ b).symm.continuous

/-- **`H₀(F) ≅ ℤ`** for the fibre `F` of the path fibration over the south pole, given that the
sphere is simply connected. -/
def hgrpZeroPathFib
    (h : ∀ p q : Path x₀ (southPoleVal d), Path.Homotopic p q) :
    Hgrp 0 (pathFib x₀) ≅ AddCommGrpCat.of ℤ :=
  haveI : PathConnectedSpace (PathFibre (Sph (d + 1)) x₀ (southPoleVal d)) :=
    pathConnectedSpace_pathFibre
      ⟨(PathConnectedSpace.somePath x₀ (southPoleVal d))⟩ h
  hgrpZeroIso (pathFib x₀)

/-! ### Simple connectivity of the sphere -/

/-- If `π₁` vanishes at every base point of a path-connected space, any two paths with the same
end points are homotopic rel end points. -/
theorem paths_homotopic_of_subsingleton_pi1 {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (h : ∀ x : X, Subsingleton (HomotopyGroup.Pi 1 X x)) {x y : X}
    (p q : Path x y) : Path.Homotopic p q := by
  have hsc : SimplyConnectedSpace X := by
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨inferInstance, fun z γ => ?_⟩
    haveI := h z
    haveI : Subsingleton (FundamentalGroup X z) :=
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := z)).toEquiv.symm.subsingleton
    have heq : (⟦γ⟧ : Path.Homotopic.Quotient z z) = ⟦Path.refl z⟧ :=
      Subsingleton.elim (FundamentalGroup.fromPath ⟦γ⟧)
        (FundamentalGroup.fromPath ⟦Path.refl z⟧)
    exact Quotient.exact heq
  exact SimplyConnectedSpace.paths_homotopic p q

/-- **Any two paths with the same end points in `Sⁿ` (`n ≥ 2`) are homotopic rel end points.** -/
theorem paths_homotopic_sph {n : ℕ} (hn : 1 < n) {x y : Sph n} (p q : Path x y) :
    Path.Homotopic p q :=
  haveI : PathConnectedSpace (Sph n) := pathConnectedSpace_sph (by omega)
  paths_homotopic_of_subsingleton_pi1
    (fun z => subsingleton_homotopyGroup_sphere_of_lt 1 n hn z) p q

/-- **`H₀(Ω S^{d+1}) ≅ ℤ`** for `d ≥ 1`. -/
def hgrpZeroPathFibOfPos (hd : 0 < d) : Hgrp 0 (pathFib x₀) ≅ AddCommGrpCat.of ℤ :=
  hgrpZeroPathFib x₀ fun p q => paths_homotopic_sph (by omega) p q

/-! ### The homology of `Ω S^{d+1}` -/

/-- **`H_*(Ω S^{d+1})` is `d`-periodic** (`d ≥ 1`). -/
def pathFibPeriodicity (hd : 0 < d) (n : ℕ) : Hgrp n (pathFib x₀) ≅ Hgrp (n + d) (pathFib x₀) :=
  pathWangPeriodicity x₀ P n (by omega)

include P in
/-- **`H_{j d}(Ω S^{d+1}) ≅ ℤ`** for every `j` (`d ≥ 1`). -/
def hgrpPathFib_mul (hd : 0 < d) (j : ℕ) : Hgrp (j * d) (pathFib x₀) ≅ AddCommGrpCat.of ℤ := by
  induction j with
  | zero =>
      rw [Nat.zero_mul]
      exact hgrpZeroPathFibOfPos x₀ hd
  | succ i ih =>
      rw [Nat.succ_mul]
      exact (pathFibPeriodicity x₀ P hd (i * d)).symm.trans ih

include P in
/-- **`H_k(Ω S^{d+1}) = 0` when `d` does not divide `k`** (`d ≥ 1`). -/
theorem isZero_hgrpPathFib (L : ProdSphereLowIso (pathFib x₀) d) (hd : 0 < d) :
    ∀ k : ℕ, ¬ d ∣ k → IsZero (Hgrp k (pathFib x₀)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hlt : k < d
    · refine isZero_pathFib_of_lt x₀ L k ?_ hlt
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact absurd (dvd_zero d) hk
      · exact hpos
    · rw [not_lt] at hlt
      have hkd : k - d + d = k := by omega
      have hdvd : ¬ d ∣ (k - d) := fun hdd => hk (by
        have hrw : k = (k - d) + d := by omega
        rw [hrw]
        exact Dvd.dvd.add hdd dvd_rfl)
      have hzero := ih (k - d) (by omega) hdvd
      have e := pathFibPeriodicity x₀ P hd (k - d)
      rw [hkd] at e
      exact IsZero.of_iso hzero e.symm

end Submission
