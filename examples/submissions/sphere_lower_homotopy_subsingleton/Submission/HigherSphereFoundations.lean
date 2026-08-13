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

/-- For a contractible ambient space, the boundary map of its pair is a multiplicative
equivalence from relative homotopy to the homotopy of the distinguished subspace. -/
noncomputable def piRelativeBoundaryEquiv
    {Y : Type*} [TopologicalSpace Y] {C : Set Y} [ContractibleSpace Y]
    (c : C) (n : ℕ) :
    π_rel (n + 2) Y C c ≃* π_ (n + 1) C c := by
  have hbd : Function.Bijective (RelHomotopyGroup.bd (n + 1) Y C c) :=
    bijective_bd_of_subsingleton n c
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 2)) _)
      (subsingleton_homotopyGroup_of_contractible (N := Fin (n + 1)) _)
  exact MulEquiv.ofBijective (RelHomotopyGroup.bdHom n Y C c) hbd

/-- For a contractible ambient source, the boundary map identifies its relative homotopy group
with the homotopy group of the distinguished subspace, transported across the supplied
homotopy equivalence by its actual forward map. -/
noncomputable def piRelativeSourceEquiv
    {Y L : Type*} [TopologicalSpace Y] [TopologicalSpace L]
    {C : Set Y} [ContractibleSpace Y]
    (c : C) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ) :
    π_ (n + 1) L (e c) ≃* π_rel (n + 2) Y C c :=
  (homotopyGroupMulEquivOfHomotopyEquiv (N := Fin (n + 1)) e c).symm.trans
    (piRelativeBoundaryEquiv c n).symm

/-- Applying the source coordinate means postcomposing by the maintained homotopy inverse,
transporting along its selected left-inverse homotopy, and then inverting the pair boundary
map.  In particular no anonymous homotopy-group equivalence remains in this construction. -/
@[simp]
theorem piRelativeSourceEquiv_apply
    {Y L : Type*} [TopologicalSpace Y] [TopologicalSpace L]
    {C : Set Y} [ContractibleSpace Y]
    (c : C) (e : ContinuousMap.HomotopyEquiv C L) (n : ℕ)
    (a : π_ (n + 1) L (e c)) :
    piRelativeSourceEquiv c e n a =
      (piRelativeBoundaryEquiv c n).symm
        (HomotopyGroup.transport
          ((homotopyEquivLeftHomotopy e).evalAt c)
          (HomotopyGroup.map e.invFun rfl a)) := by
  rw [piRelativeSourceEquiv, MulEquiv.trans_apply,
    homotopyGroupMulEquivOfHomotopyEquiv_symm_apply]
  rfl

/-- The source coordinate is natural for a map of contractible pairs whose distinguished
subspace map commutes with the supplied homotopy-equivalence coordinates. -/
theorem piRelativeSourceEquiv_natural
    {Y Y' L L' : Type*}
    [TopologicalSpace Y] [TopologicalSpace Y']
    [TopologicalSpace L] [TopologicalSpace L']
    {C : Set Y} {C' : Set Y'} [ContractibleSpace Y] [ContractibleSpace Y']
    (c : C) (c' : C')
    (e : ContinuousMap.HomotopyEquiv C L)
    (e' : ContinuousMap.HomotopyEquiv C' L') (n : ℕ)
    (f : BasedPairMap C C' c c') (g : C(L, L'))
    (hg : g (e c) = e' c')
    (hsquare : e'.toFun.comp f.subspaceMap = g.comp e.toFun)
    (a : π_ (n + 1) L (e c)) :
    piRelativeSourceEquiv c' e' n (HomotopyGroup.map g hg a) =
      RelHomotopyGroup.mapHom n f (piRelativeSourceEquiv c e n a) := by
  apply (piRelativeBoundaryEquiv c' n).injective
  rw [piRelativeSourceEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  change
    (homotopyGroupMulEquivOfHomotopyEquiv (N := Fin (n + 1)) e' c').symm
        (HomotopyGroup.map g hg a) =
      RelHomotopyGroup.bdHom n Y' C' c'
        (RelHomotopyGroup.mapHom n f (piRelativeSourceEquiv c e n a))
  rw [← MonoidHom.comp_apply, RelHomotopyGroup.bdHom_comp_mapHom,
    MonoidHom.comp_apply]
  change
    (homotopyGroupMulEquivOfHomotopyEquiv (N := Fin (n + 1)) e' c').symm
        (HomotopyGroup.map g hg a) =
      HomotopyGroup.map f.subspaceMap f.subspaceMap_basepoint
        ((piRelativeBoundaryEquiv c n) (piRelativeSourceEquiv c e n a))
  rw [piRelativeSourceEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  apply (homotopyGroupMulEquivOfHomotopyEquiv
    (N := Fin (n + 1)) e' c').injective
  rw [MulEquiv.apply_symm_apply,
    homotopyGroupMulEquivOfHomotopyEquiv_apply]
  let E := homotopyGroupMulEquivOfHomotopyEquiv
    (N := Fin (n + 1)) e c
  calc
    HomotopyGroup.map g hg a =
        HomotopyGroup.map g hg (E (E.symm a)) := by
      rw [E.apply_symm_apply]
    _ = HomotopyGroup.map g hg
        (HomotopyGroup.map e.toFun rfl (E.symm a)) := by
      rw [homotopyGroupMulEquivOfHomotopyEquiv_apply]
    _ = HomotopyGroup.map (g.comp e.toFun) (by simp [hg]) (E.symm a) :=
      HomotopyGroup.map_comp_apply g hg e.toFun rfl (E.symm a)
    _ = HomotopyGroup.map (e'.toFun.comp f.subspaceMap)
        (by rw [ContinuousMap.comp_apply, f.subspaceMap_basepoint]) (E.symm a) :=
      HomotopyGroup.map_congr hsquare.symm _ _ (E.symm a)
    _ = HomotopyGroup.map e'.toFun rfl
        (HomotopyGroup.map f.subspaceMap f.subspaceMap_basepoint (E.symm a)) :=
      (HomotopyGroup.map_comp_apply e'.toFun rfl f.subspaceMap
        f.subspaceMap_basepoint (E.symm a)).symm

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

/-- The target coordinate is natural for based maps of pairs with contractible distinguished
subspaces. -/
theorem piRelativeTargetEquiv_natural
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    {B : Set X} {B' : Set X'} [ContractibleSpace B] [ContractibleSpace B']
    (b : B) (b' : B') (n : ℕ) (f : BasedPairMap B B' b b')
    (a : π_rel (n + 2) X B b) :
    HomotopyGroup.map f.toContinuousMap f.map_basepoint'
        (piRelativeTargetEquiv b n a) =
      piRelativeTargetEquiv b' n (RelHomotopyGroup.mapHom n f a) := by
  apply (piRelativeTargetEquiv b' n).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change RelHomotopyGroup.jStar (n + 2) X' B' b'
      (HomotopyGroup.map f.toContinuousMap f.map_basepoint'
        (piRelativeTargetEquiv b n a)) =
    RelHomotopyGroup.mapHom n f a
  rw [← RelHomotopyGroup.map_jStar]
  change RelHomotopyGroup.map f
      ((piRelativeTargetEquiv b n).symm (piRelativeTargetEquiv b n a)) =
    RelHomotopyGroup.mapHom n f a
  rw [MulEquiv.symm_apply_apply]
  rfl

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

/-- The absolute comparison induced from a relative homomorphism is natural whenever the maps
of source and target pairs form a commuting relative square. -/
theorem piHom_of_relativeHom_natural
    {Y Y' X X' L L' : Type*}
    [TopologicalSpace Y] [TopologicalSpace Y']
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace L] [TopologicalSpace L']
    {C : Set Y} {C' : Set Y'} {B : Set X} {B' : Set X'}
    [ContractibleSpace Y] [ContractibleSpace Y']
    [ContractibleSpace B] [ContractibleSpace B']
    (c : C) (c' : C') (b : B) (b' : B')
    (e : ContinuousMap.HomotopyEquiv C L)
    (e' : ContinuousMap.HomotopyEquiv C' L') (n : ℕ)
    (sourceMap : BasedPairMap C C' c c')
    (targetMap : BasedPairMap B B' b b')
    (g : C(L, L')) (hg : g (e c) = e' c')
    (hsource : e'.toFun.comp sourceMap.subspaceMap = g.comp e.toFun)
    (f : π_rel (n + 2) Y C c →* π_rel (n + 2) X B b)
    (f' : π_rel (n + 2) Y' C' c' →* π_rel (n + 2) X' B' b')
    (hrelative : (RelHomotopyGroup.mapHom n targetMap).comp f =
      f'.comp (RelHomotopyGroup.mapHom n sourceMap))
    (a : π_ (n + 1) L (e c)) :
    HomotopyGroup.map targetMap.toContinuousMap targetMap.map_basepoint'
        (piHom_of_relativeHom c b e n f a) =
      piHom_of_relativeHom c' b' e' n f'
        (HomotopyGroup.map g hg a) := by
  change HomotopyGroup.map targetMap.toContinuousMap targetMap.map_basepoint'
      (piRelativeTargetEquiv b n
        (f (piRelativeSourceEquiv c e n a))) =
    piRelativeTargetEquiv b' n
      (f' (piRelativeSourceEquiv c' e' n (HomotopyGroup.map g hg a)))
  rw [piRelativeTargetEquiv_natural]
  change piRelativeTargetEquiv b' n
      (RelHomotopyGroup.mapHom n targetMap
        (f (piRelativeSourceEquiv c e n a))) =
    piRelativeTargetEquiv b' n
      (f' (piRelativeSourceEquiv c' e' n (HomotopyGroup.map g hg a)))
  have hrel := DFunLike.congr_fun hrelative (piRelativeSourceEquiv c e n a)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hrel
  apply congrArg (piRelativeTargetEquiv b' n)
  rw [hrel,
    piRelativeSourceEquiv_natural c c' e e' n sourceMap g hg hsource]

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
  let changeSpace :=
    homotopyGroupMulEquivOfHomotopyEquiv (N := Fin (n + 1)) e c
  exact changeSpace.symm |>.trans
    (piRelativeBoundaryEquiv c n).symm |>.trans
    (MulEquiv.ofBijective f hf) |>.trans
    (piRelativeTargetEquiv b n)

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
