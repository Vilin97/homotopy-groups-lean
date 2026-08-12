/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Hurewicz.AbsoluteNaturality
import Submission.Hurewicz.ConnectedPair
import Submission.Hurewicz.CubicalDegreeOne
import Submission.SphereSuspensionHomologyExcision

/-!
# Hurewicz-range homology of the sphere suspension pairs

The two cap/overlap pairs used by sphere suspension excision are already proved `m`-connected.
The bounded singular-simplex compression theorem therefore kills their relative homology through
degree `m`.  Homological excision transports the same vanishing to the target pair consisting of
the sphere and its upper cap.

Together with the top-degree computations in `Submission.SphereSuspensionHomologyExcision`, this
identifies the complete first-nonzero relative-homology pattern needed by a future natural
relative Hurewicz comparison.
-/

open CategoryTheory Limits AlgebraicTopology
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- The standard sphere basepoint regarded as a point of the overlap inside the upper cap. -/
noncomputable def sphCapOverlapInUpperBase (m : ℕ) : sphCapOverlapInUpper m :=
  ⟨sphUpperCapBase m, sphereBasepoint_mem_sphLowerCap m⟩

/-- Relative homology of the lower-cap/overlap pair vanishes through its full connectivity
range. -/
theorem isZero_sphLowerCap_overlap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (sphLowerCap m)) k (sphCapOverlapInLower m)) :=
  (isNConnectedPair_sphLowerCap_overlap m hm).isZero_relativeHomology
    ⟨(sphCapOverlapBase m).1, (sphCapOverlapBase m).2⟩ k hk

/-- Relative homology of the upper-cap/overlap pair vanishes through its full connectivity
range. -/
theorem isZero_sphUpperCap_overlap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (sphUpperCap m)) k (sphCapOverlapInUpper m)) :=
  (isNConnectedPair_sphUpperCap_overlap m hm).isZero_relativeHomology
    ⟨(sphCapOverlapInUpperBase m).1, (sphCapOverlapInUpperBase m).2⟩ k hk

/-- Homological excision transports lower-cap connectivity to the target sphere/upper-cap pair:
its relative homology also vanishes through degree `m`. -/
theorem isZero_sphSphere_upperCap_relativeHomology (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m) :
    IsZero (HrelSet (Y := TopCat.of (Sph (m + 1))) k (sphUpperCap m)) := by
  letI := isIso_sphereCapInclusionHrelMap m k
  exact IsZero.of_iso (isZero_sphLowerCap_overlap_relativeHomology m k hm hk)
    (asIso (sphereCapInclusionHrelMap m k)).symm

/-- The relative Hurewicz map for the target sphere/upper-cap pair is an isomorphism in the top
suspension degree.  This is the contractible-subspace form of absolute Hurewicz. -/
theorem sphereSuspensionTargetRelativeHurewiczAdd_bijective (n : ℕ) :
    Function.Bijective
      (relativeHurewiczAdd n (sphUpperCap (n + 1)) (sphUpperCapBase (n + 1))) :=
  (isNConnected_sphere_succ_succ n).relativeHurewiczAdd_bijective_of_contractibleSubspace
    (sphUpperCap (n + 1)) (sphUpperCapBase (n + 1))

/-- The target relative Hurewicz isomorphism, bundled additively. -/
noncomputable def sphereSuspensionTargetRelativeHurewiczAddEquiv (n : ℕ) :
    Additive
        (π_rel (n + 2) (Sph (n + 2)) (sphUpperCap (n + 1))
          (sphUpperCapBase (n + 1))) ≃+
      (HrelSet (Y := TopCat.of (Sph (n + 2))) (n + 2)
        (sphUpperCap (n + 1)) : Type) :=
  AddEquiv.ofBijective
    (relativeHurewiczAdd n (sphUpperCap (n + 1)) (sphUpperCapBase (n + 1)))
    (sphereSuspensionTargetRelativeHurewiczAdd_bijective n)

/-- The canonical cap inclusion commutes with relative Hurewicz in the top suspension degree. -/
theorem sphereSuspensionExcision_relativeHurewicz_naturality (n : ℕ)
    (x : π_rel (n + 2) (sphLowerCap (n + 1))
      (sphCapOverlapInLower (n + 1)) (sphCapOverlapBase (n + 1))) :
    sphereSuspensionExcisionHrelMap n
        (relativeHurewicz n (sphCapOverlapInLower (n + 1))
          (sphCapOverlapBase (n + 1)) x) =
      relativeHurewicz n (sphUpperCap (n + 1)) (sphUpperCapBase (n + 1))
        (sphereSuspensionExcisionHom n x) :=
  relativeHurewicz_naturality n (sphCapInclusionPairMap (n + 1)) x

/-- After the target-side Hurewicz theorem and homological excision, homotopy excision for the
canonical sphere caps is equivalent to the single remaining source-side relative Hurewicz
isomorphism.  This isolates the precise unsolved comparison rather than leaving two relative
groups and an unspecified map. -/
theorem sphereSuspensionExcisionHom_bijective_iff_sourceRelativeHurewiczAdd
    (n : ℕ) :
    Function.Bijective (sphereSuspensionExcisionHom n) ↔
      Function.Bijective
        (relativeHurewiczAdd n (sphCapOverlapInLower (n + 1))
          (sphCapOverlapBase (n + 1))) := by
  let f := sphereSuspensionExcisionHom n
  let fAdd := f.toAdditive
  let hS := relativeHurewiczAdd n (sphCapOverlapInLower (n + 1))
    (sphCapOverlapBase (n + 1))
  let hT := relativeHurewiczAdd n (sphUpperCap (n + 1))
    (sphUpperCapBase (n + 1))
  let hRel := sphereSuspensionExcisionHrelMap n
  have htag : Function.Bijective f ↔ Function.Bijective fAdd := by
    change Function.Bijective f ↔
      Function.Bijective (Additive.ofMul ∘ f ∘ Additive.toMul)
    exact ((Function.Bijective.of_comp_iff' Additive.ofMul.bijective _).trans
      (Function.Bijective.of_comp_iff _ Additive.toMul.bijective)).symm
  have hRelBij : Function.Bijective hRel := by
    letI := isIso_sphereSuspensionExcisionHrelMap n
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hTBij : Function.Bijective hT :=
    sphereSuspensionTargetRelativeHurewiczAdd_bijective n
  have hcomm : (hRel ∘ hS) = (hT ∘ fAdd) := by
    funext z
    exact sphereSuspensionExcision_relativeHurewicz_naturality n z.toMul
  refine htag.trans ?_
  calc
    Function.Bijective fAdd ↔ Function.Bijective (hT ∘ fAdd) :=
      (Function.Bijective.of_comp_iff' hTBij fAdd).symm
    _ ↔ Function.Bijective (hRel ∘ hS) := by rw [hcomm]
    _ ↔ Function.Bijective hS :=
      Function.Bijective.of_comp_iff' hRelBij hS

/-- The overlap in the lower cap of `S^(n+3)` is `(n+1)`-connected.  This is the precise
absolute connectivity input needed to apply higher Hurewicz to its first nonzero homotopy
group. -/
theorem isNConnected_sphCapOverlapInLower_succ (n : ℕ) :
    IsNConnected (n + 1) (sphCapOverlapInLower (n + 2)) where
  nonempty := ⟨sphCapOverlapBase (n + 2)⟩
  pathConnected := pathConnectedSpace_sphCapOverlapInLower (n + 2) (by omega)
  subsingleton_pi k hk c :=
    subsingleton_pi_sphCapOverlapInLower (n + 2) (k + 1) (by omega) (by omega) c

/-- For every suspension degree at least one, the source-side relative Hurewicz map is an
isomorphism.  The cap is contractible, and the overlap is connected through the required
degree. -/
theorem sphereSuspensionSourceRelativeHurewiczAdd_bijective_succ (n : ℕ) :
    Function.Bijective
      (relativeHurewiczAdd (n + 1) (sphCapOverlapInLower (n + 2))
        (sphCapOverlapBase (n + 2))) :=
  IsNConnected.relativeHurewiczAdd_bijective_of_contractibleAmbient
    (isNConnected_sphCapOverlapInLower_succ n)
    (sphCapOverlapBase (n + 2))

/-- In every suspension degree at least one, the canonical cap-excision map is bijective. -/
theorem sphereSuspensionExcisionHom_bijective_succ (n : ℕ) :
    Function.Bijective (sphereSuspensionExcisionHom (n + 1)) :=
  (sphereSuspensionExcisionHom_bijective_iff_sourceRelativeHurewiczAdd (n + 1)).2
    (sphereSuspensionSourceRelativeHurewiczAdd_bijective_succ n)

/-- The circle-shaped overlap in the first cap pair is path connected. -/
theorem isNConnected_sphCapOverlapInLower_one :
    IsNConnected 0 (sphCapOverlapInLower 1) :=
  IsNConnected.zero ⟨sphCapOverlapBase 1⟩
    (pathConnectedSpace_sphCapOverlapInLower 1 (by omega))

/-- The fundamental group of the circle-shaped cap overlap is commutative. -/
theorem mul_comm_pi_sphCapOverlapInLower_one
    (u v : π_ 1 (sphCapOverlapInLower 1) (sphCapOverlapBase 1)) :
    u * v = v * u := by
  let e := sphCapOverlapHomotopyEquiv 1
  obtain ⟨changeSpace⟩ :=
    nonempty_mulEquiv_of_homotopyEquiv' (N := Fin 1) e (sphCapOverlapBase 1)
  obtain ⟨circle⟩ := pi1_sph_one_at_mulEquiv_int (e (sphCapOverlapBase 1))
  let total := changeSpace.trans circle
  apply total.injective
  simpa only [map_mul] using mul_comm (total u) (total v)

/-- In the first suspension degree, the source-side relative Hurewicz map is an isomorphism by
the degree-one Hurewicz theorem for the circle-shaped overlap. -/
theorem sphereSuspensionSourceRelativeHurewiczAdd_bijective_zero :
    Function.Bijective
      (relativeHurewiczAdd 0 (sphCapOverlapInLower 1)
        (sphCapOverlapBase 1)) :=
  IsNConnected.relativeHurewiczAdd_bijective_of_contractibleAmbient_one
    isNConnected_sphCapOverlapInLower_one (sphCapOverlapBase 1)
    mul_comm_pi_sphCapOverlapInLower_one

/-- The index-zero cap-excision homomorphism is bijective. -/
theorem sphereSuspensionExcisionHom_bijective_zero :
    Function.Bijective (sphereSuspensionExcisionHom 0) :=
  (sphereSuspensionExcisionHom_bijective_iff_sourceRelativeHurewiczAdd 0).2
    sphereSuspensionSourceRelativeHurewiczAdd_bijective_zero

/-- The canonical cap-excision homomorphism is bijective in every degree. -/
theorem sphereSuspensionExcisionHom_bijective (n : ℕ) :
    Function.Bijective (sphereSuspensionExcisionHom n) := by
  cases n with
  | zero => exact sphereSuspensionExcisionHom_bijective_zero
  | succ n => exact sphereSuspensionExcisionHom_bijective_succ n

/-- The cap-excision route now gives an unconditional second proof of the exact integral sphere
diagonal.  Only positive cap indices are needed because the first two diagonal groups were
computed separately. -/
theorem sphere_diagonal_mulEquiv_int_via_capExcision (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  apply sphere_diagonal_mulEquiv_int_of_capExcision_from_two
  intro m hm
  cases m with
  | zero => omega
  | succ m => exact sphereSuspensionExcisionHom_bijective_succ m

/-- Full cap-excision diagonal proof, now including the first circle-to-two-sphere step. -/
theorem sphere_diagonal_mulEquiv_int_via_all_capExcision (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) :=
  sphere_diagonal_mulEquiv_int_of_capExcision
    sphereSuspensionExcisionHom_bijective n

end Submission
