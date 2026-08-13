/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.SphereOne
import Submission.Homotopy.HomotopyLesTools
import Submission.Homotopy.RelMap
import Submission.Pi2SphereTwo

/-!
# Higher-sphere foundations

This file exposes two group-level tools used by higher sphere calculations.  The first upgrades
the path-fibration loop-space shift to a multiplicative equivalence.  The second packages the
long-exact-sequence argument that turns a bijective comparison between relative homotopy groups
of contractible pairs into an equivalence of absolute homotopy groups.  The latter is the exact
algebraic consumer needed after a geometric suspension-excision theorem.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- **Loop spaces shift positive homotopy groups as groups.** -/
theorem nonempty_piSucc_mulEquiv_pi_loopSpace
    {X : Type*} [TopologicalSpace X] (x₀ : X) (k : ℕ) :
    Nonempty
      (π_ (k + 2) X x₀ ≃*
        π_ (k + 1) (Path x₀ x₀) (Path.refl x₀)) := by
  exact ⟨(fibDeltaMulEquiv (loopBase x₀) (isSerreFibration_ev₁ X x₀) k
    (subsingleton_pi_pathSpace x₀ (k + 2) _)
    (subsingleton_pi_pathSpace x₀ (k + 1) _)).trans
    (HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (k + 1))
      (fibreEv₁Homeomorph X x₀) rfl)⟩

/-- For a contractible ambient source, the boundary map identifies its relative homotopy group
with the homotopy group of the distinguished subspace (transported across `e`). -/
noncomputable def piRelativeSourceEquiv
    {Y L : Type*} [TopologicalSpace Y] [TopologicalSpace L]
    {C : Set Y} [ContractibleSpace Y]
    (c : C) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ) :
    π_ (n + 1) L (e c) ≃* π_rel (n + 2) Y C c := by
  have hbd : Function.Bijective (RelHomotopyGroup.bd (n + 1) Y C c) :=
    bijective_bd_of_subsingleton n c
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) _)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) _)
  let changeSpace := Classical.choice
    (nonempty_mulEquiv_of_homotopyEquiv' (N := Fin (n + 1)) e c)
  exact changeSpace.symm.trans
    (MulEquiv.ofBijective (RelHomotopyGroup.bdHom n Y C c) hbd).symm

/-- For a contractible target subspace, the relative target group is identified with the
absolute homotopy group of its ambient space. -/
noncomputable def piRelativeTargetEquiv
    {X : Type*} [TopologicalSpace X] {B : Set X} [ContractibleSpace B]
    (b : B) (n : ℕ) :
    π_rel (n + 2) X B b ≃* π_ (n + 2) X (b : X) := by
  have hjs : Function.Bijective (RelHomotopyGroup.jStar (n + 2) X B b) :=
    bijective_jStar_of_subsingleton n b
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) _)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) _)
  exact (MulEquiv.ofBijective (RelHomotopyGroup.jStarHom n X B b) hjs).symm

/-- The absolute homomorphism obtained from a relative homomorphism between a contractible
ambient source pair and a contractible-subspace target pair.  Unlike the equivalence below, this
construction retains useful information when the middle map is only surjective. -/
noncomputable def piHom_of_relativeHom
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b) :
    π_ (n + 1) L (e c) →* π_ (n + 2) X (b : X) :=
  (piRelativeTargetEquiv b n).toMonoidHom.comp
    (f.comp (piRelativeSourceEquiv c e n).toMonoidHom)

/-- Surjectivity of the relative comparison passes to its absolute homomorphism. -/
theorem piHom_of_relativeHom_surjective
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b)
    (hf : Function.Surjective f) :
    Function.Surjective (piHom_of_relativeHom c b e n f) :=
  (piRelativeTargetEquiv b n).surjective.comp
    (hf.comp (piRelativeSourceEquiv c e n).surjective)

/-- Injectivity of the relative comparison passes to its absolute homomorphism. -/
theorem piHom_of_relativeHom_injective
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b)
    (hf : Function.Injective f) :
    Function.Injective (piHom_of_relativeHom c b e n f) :=
  (piRelativeTargetEquiv b n).injective.comp
    (hf.comp (piRelativeSourceEquiv c e n).injective)

/-- Bijectivity of the relative comparison passes to its absolute homomorphism. -/
theorem piHom_of_relativeHom_bijective
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b)
    (hf : Function.Bijective f) :
    Function.Bijective (piHom_of_relativeHom c b e n f) :=
  ⟨piHom_of_relativeHom_injective c b e n f hf.1,
    piHom_of_relativeHom_surjective c b e n f hf.2⟩

/-- **Contractible-pair comparison principle.**  A bijective homomorphism between the relative
homotopy groups of two pairs with contractible ambient/sub spaces induces an equivalence between
the homotopy group of the first pair's subspace and that of the second pair's ambient space.

For a suspension cover, `f` is the excision homomorphism.  Thus this declaration isolates the
group-theoretic and long-exact-sequence part of the Freudenthal argument from its geometric
Blakers--Massey input. -/
noncomputable def piMulEquiv_of_bijective_relativeHom
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b)
    (hf : Function.Bijective f) :
    π_ (n + 1) L (e c) ≃* π_ (n + 2) X (b : X) := by
  have hbd : Function.Bijective (RelHomotopyGroup.bd (n + 1) Y C c) :=
    bijective_bd_of_subsingleton n c
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) _)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) _)
  have hjs : Function.Bijective (RelHomotopyGroup.jStar (n + 2) X B b) :=
    bijective_jStar_of_subsingleton n b
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) _)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) _)
  let changeSpace := Classical.choice
    (nonempty_mulEquiv_of_homotopyEquiv' (N := Fin (n + 1)) e c)
  exact changeSpace.symm |>.trans
    (MulEquiv.ofBijective (RelHomotopyGroup.bdHom n Y C c) hbd).symm |>.trans
    (MulEquiv.ofBijective f hf) |>.trans
    (MulEquiv.ofBijective (RelHomotopyGroup.jStarHom n X B b) hjs).symm

/-- **Functorial contractible-pair comparison.** A based map of pairs whose induced relative
homotopy homomorphism is bijective yields the absolute equivalence used in the Freudenthal
argument. Unlike `piMulEquiv_of_bijective_relativeHom`, this version requires the middle map to
come from an actual continuous map of pairs. -/
noncomputable def piMulEquiv_of_bijective_relativeMap
    {Y X L : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace L]
    {C : Set Y} {B : Set X} [ContractibleSpace Y] [ContractibleSpace B]
    (c : C) (b : B) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (f : BasedPairMap C B c b)
    (hf : Function.Bijective (RelHomotopyGroup.mapHom n f)) :
    π_ (n + 1) L (e c) ≃* π_ (n + 2) X (b : X) :=
  piMulEquiv_of_bijective_relativeHom c b e n (RelHomotopyGroup.mapHom n f) hf

end Submission
