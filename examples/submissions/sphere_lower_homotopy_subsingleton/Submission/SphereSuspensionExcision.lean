/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.DiagonalInduction
import Submission.HigherSphereFoundations
import Submission.Homotopy.ContractionData
import Submission.IndependentResults

/-!
# The relative excision map for suspension of a sphere

The metric `(m+1)`-sphere is covered by two enlarged hemispheres. Both hemispheres are
contractible, their interiors cover the sphere, and their overlap is homotopy-equivalent to the
metric `m`-sphere. Inclusion of the lower hemisphere into the full sphere is therefore the
canonical map of pairs to which homotopy excision applies.

This file packages that inclusion as a based map of pairs and defines its induced relative
homotopy homomorphism. Bijectivity of this one concrete map gives the successive diagonal
equivalence, and bijectivity in every dimension gives the exact integral diagonal. Thus the
remaining Freudenthal gap is reduced to the geometric Blakers--Massey assertion itself, with no
unbundled or unspecified comparison map.
-/

open HomotopyGroups
open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- The distinguished point of `Sph (m+1)` has suspension height zero. -/
theorem sphHeight_sphereBasepoint_succ (m : ℕ) :
    sphHeight (sphereBasepoint (m + 1)) = 0 := by
  change (EuclideanSpace.single (0 : Fin (m + 2)) (1 : ℝ)) (Fin.last (m + 1)) = 0
  rw [PiLp.single_apply]
  simp [Fin.ext_iff]

/-- The distinguished point lies in the enlarged lower hemisphere. -/
theorem sphereBasepoint_mem_sphLowerCap (m : ℕ) :
    sphereBasepoint (m + 1) ∈ sphLowerCap m := by
  rw [mem_sphLowerCap, sphHeight_sphereBasepoint_succ]
  norm_num

/-- The distinguished point lies in the enlarged upper hemisphere. -/
theorem sphereBasepoint_mem_sphUpperCap (m : ℕ) :
    sphereBasepoint (m + 1) ∈ sphUpperCap m := by
  rw [mem_sphUpperCap, sphHeight_sphereBasepoint_succ]
  norm_num

/-- The upper-cap part of the lower cap, regarded as a subset of the lower-cap subtype. -/
def sphCapOverlapInLower (m : ℕ) : Set (sphLowerCap m) :=
  {z | (z.1 : Sph (m + 1)) ∈ sphUpperCap m}

/-- The lower-cap part of the upper cap, regarded as a subset of the upper-cap subtype. -/
def sphCapOverlapInUpper (m : ℕ) : Set (sphUpperCap m) :=
  {z | (z.1 : Sph (m + 1)) ∈ sphLowerCap m}

/-- The standard sphere basepoint as a point of the lower cap. -/
noncomputable def sphLowerCapBase (m : ℕ) : sphLowerCap m :=
  ⟨sphereBasepoint (m + 1), sphereBasepoint_mem_sphLowerCap m⟩

/-- The standard sphere basepoint as a point of the upper cap. -/
noncomputable def sphUpperCapBase (m : ℕ) : sphUpperCap m :=
  ⟨sphereBasepoint (m + 1), sphereBasepoint_mem_sphUpperCap m⟩

/-- The standard sphere basepoint as a point of the overlap inside the lower cap. -/
noncomputable def sphCapOverlapBase (m : ℕ) : sphCapOverlapInLower m :=
  ⟨sphLowerCapBase m, sphereBasepoint_mem_sphUpperCap m⟩

/-- Inclusion of the lower cap in the sphere, as a based map from the overlap/lower-cap pair to
the upper-cap/sphere pair. This is the relative map used by suspension excision. -/
noncomputable def sphCapInclusionPairMap (m : ℕ) :
    BasedPairMap (sphCapOverlapInLower m) (sphUpperCap m)
      (sphCapOverlapBase m) (sphUpperCapBase m) where
  toContinuousMap := ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo' := fun _ hz => hz
  map_basepoint' := rfl

/-- Reassociating nested subtypes identifies the overlap inside the lower cap with the ordinary
intersection of the two caps. -/
def sphCapOverlapHomeoBelt (m : ℕ) :
    sphCapOverlapInLower m ≃ₜ sphBelt m where
  toFun z := ⟨z.1.1, z.1.2, z.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Reassociating nested subtypes also identifies the overlap inside the upper cap with the
ordinary intersection of the two caps. -/
def sphCapOverlapInUpperHomeoBelt (m : ℕ) :
    sphCapOverlapInUpper m ≃ₜ sphBelt m where
  toFun z := ⟨z.1.1, z.2, z.1.2⟩
  invFun z := ⟨⟨z.1, z.2.2⟩, z.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The overlap in the lower cap is homotopy-equivalent to the equatorial metric sphere. -/
noncomputable def sphCapOverlapHomotopyEquiv (m : ℕ) :
    ContinuousMap.HomotopyEquiv (sphCapOverlapInLower m) (Sph m) :=
  (sphCapOverlapHomeoBelt m).toHomotopyEquiv.trans (sphBeltHomotopyEquiv m)

/-- The overlap in the upper cap is homotopy-equivalent to the equatorial metric sphere. -/
noncomputable def sphCapOverlapInUpperHomotopyEquiv (m : ℕ) :
    ContinuousMap.HomotopyEquiv (sphCapOverlapInUpper m) (Sph m) :=
  (sphCapOverlapInUpperHomeoBelt m).toHomotopyEquiv.trans (sphBeltHomotopyEquiv m)

/-- For positive-dimensional equators, the overlap inside the lower cap is path connected. -/
theorem pathConnectedSpace_sphCapOverlapInLower (m : ℕ) (hm : 1 ≤ m) :
    PathConnectedSpace (sphCapOverlapInLower m) := by
  letI : PathConnectedSpace (Sph m) := pathConnectedSpace_sph hm
  letI : ContractibleSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by rw [Set.mem_Icc]; norm_num⟩
  letI : PathConnectedSpace (sphBelt m) :=
    Function.Surjective.pathConnectedSpace (f := (sphBeltHomeo m).symm)
      (sphBeltHomeo m).symm.surjective (sphBeltHomeo m).symm.continuous
  exact Function.Surjective.pathConnectedSpace (f := (sphCapOverlapHomeoBelt m).symm)
    (sphCapOverlapHomeoBelt m).symm.surjective (sphCapOverlapHomeoBelt m).symm.continuous

/-- For positive-dimensional equators, the overlap inside the upper cap is path connected. -/
theorem pathConnectedSpace_sphCapOverlapInUpper (m : ℕ) (hm : 1 ≤ m) :
    PathConnectedSpace (sphCapOverlapInUpper m) := by
  letI : PathConnectedSpace (Sph m) := pathConnectedSpace_sph hm
  letI : ContractibleSpace (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) :=
    (convex_Icc _ _).contractibleSpace ⟨0, by rw [Set.mem_Icc]; norm_num⟩
  letI : PathConnectedSpace (sphBelt m) :=
    Function.Surjective.pathConnectedSpace (f := (sphBeltHomeo m).symm)
      (sphBeltHomeo m).symm.surjective (sphBeltHomeo m).symm.continuous
  exact Function.Surjective.pathConnectedSpace (f := (sphCapOverlapInUpperHomeoBelt m).symm)
    (sphCapOverlapInUpperHomeoBelt m).symm.surjective
    (sphCapOverlapInUpperHomeoBelt m).symm.continuous

/-- The homotopy groups of the lower-cap overlap vanish below the equator dimension. -/
theorem subsingleton_pi_sphCapOverlapInLower (m k : ℕ) (hm : 1 ≤ m) (hk : k < m)
    (c : sphCapOverlapInLower m) :
    Subsingleton (HomotopyGroup.Pi k (sphCapOverlapInLower m) c) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · letI : PathConnectedSpace (sphCapOverlapInLower m) :=
      pathConnectedSpace_sphCapOverlapInLower m hm
    exact subsingleton_homotopyGroup_zero c
  · letI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
    exact subsingleton_homotopyGroup_of_homotopyEquiv
      (sphCapOverlapHomotopyEquiv m)
      (fun z => subsingleton_homotopyGroup_sphere_of_lt k m hk z) c

/-- The homotopy groups of the upper-cap overlap vanish below the equator dimension. -/
theorem subsingleton_pi_sphCapOverlapInUpper (m k : ℕ) (hm : 1 ≤ m) (hk : k < m)
    (c : sphCapOverlapInUpper m) :
    Subsingleton (HomotopyGroup.Pi k (sphCapOverlapInUpper m) c) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · letI : PathConnectedSpace (sphCapOverlapInUpper m) :=
      pathConnectedSpace_sphCapOverlapInUpper m hm
    exact subsingleton_homotopyGroup_zero c
  · letI : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
    exact subsingleton_homotopyGroup_of_homotopyEquiv
      (sphCapOverlapInUpperHomotopyEquiv m)
      (fun z => subsingleton_homotopyGroup_sphere_of_lt k m hk z) c

/-- The lower-cap/overlap pair is as connected as the equatorial sphere. -/
theorem isNConnectedPair_sphLowerCap_overlap (m : ℕ) (hm : 1 ≤ m) :
    IsNConnectedPair m (sphLowerCap m) (sphCapOverlapInLower m) :=
  isNConnectedPair_of_contractible (sphCapOverlapInLower m) m fun k hk c =>
    subsingleton_pi_sphCapOverlapInLower m k hm hk c

/-- The upper-cap/overlap pair is as connected as the equatorial sphere. -/
theorem isNConnectedPair_sphUpperCap_overlap (m : ℕ) (hm : 1 ≤ m) :
    IsNConnectedPair m (sphUpperCap m) (sphCapOverlapInUpper m) :=
  isNConnectedPair_of_contractible (sphCapOverlapInUpper m) m fun k hk c =>
    subsingleton_pi_sphCapOverlapInUpper m k hm hk c

/-- The canonical relative homotopy homomorphism appearing in suspension excision, in an
arbitrary relative degree.  The cap index `m` is the dimension of the equatorial sphere, while
`q + 2` is the relative homotopy degree. -/
noncomputable def sphereSuspensionExcisionHomAt (m q : ℕ) :
    π_rel (q + 2) (sphLowerCap m) (sphCapOverlapInLower m)
        (sphCapOverlapBase m) →*
      π_rel (q + 2) (Sph (m + 1)) (sphUpperCap m)
        (sphUpperCapBase m) :=
  RelHomotopyGroup.mapHom q (sphCapInclusionPairMap m)

/-- The canonical relative homotopy homomorphism appearing in suspension excision for the
`(n+1)`-sphere, specialized to the first nonzero relative degree. -/
noncomputable def sphereSuspensionExcisionHom (n : ℕ) :
    π_rel (n + 2) (sphLowerCap (n + 1)) (sphCapOverlapInLower (n + 1))
        (sphCapOverlapBase (n + 1)) →*
      π_rel (n + 2) (Sph (n + 2)) (sphUpperCap (n + 1))
        (sphUpperCapBase (n + 1)) :=
  RelHomotopyGroup.mapHom n (sphCapInclusionPairMap (n + 1))

/-- The original diagonal cap-excision map is exactly the corresponding specialization of the
arbitrary-degree construction. -/
theorem sphereSuspensionExcisionHomAt_diagonal (n : ℕ) :
    sphereSuspensionExcisionHomAt (n + 1) n = sphereSuspensionExcisionHom n :=
  rfl

/-- Bijectivity of cap excision in any relative degree gives the corresponding absolute
equivalence between the equatorial sphere and its suspension. -/
theorem nonempty_sphereSuspensionMulEquiv_of_capExcisionAt
    (m q : ℕ) (hm : 1 ≤ m)
    (hbij : Function.Bijective (sphereSuspensionExcisionHomAt m q)) :
    Nonempty
      (HomotopyGroup.Pi (q + 1) (Sph m) (sphereBasepoint m) ≃*
        HomotopyGroup.Pi (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1))) := by
  let e := sphCapOverlapHomotopyEquiv m
  let raw := piMulEquiv_of_bijective_relativeMap
    (sphCapOverlapBase m) (sphUpperCapBase m) e q
    (sphCapInclusionPairMap m) hbij
  letI : PathConnectedSpace (Sph m) := pathConnectedSpace_sph hm
  let p : Path (sphereBasepoint m) (e (sphCapOverlapBase m)) :=
    PathConnectedSpace.somePath _ _
  let change := Classical.choice
    (homotopyGroup_change_basepoint q (Sph m)
      (sphereBasepoint m) (e (sphCapOverlapBase m)) p)
  exact ⟨change.trans raw⟩

/-- The sphere/upper-cap target pair has the same connectivity as the lower-cap/overlap source
pair.  This records the elementary range of cap excision independently of Hurewicz. -/
theorem isNConnectedPair_sphSphere_upperCap (m : ℕ) :
    IsNConnectedPair m (Sph (m + 1)) (sphUpperCap m) := by
  letI : PathConnectedSpace (Sph (m + 1)) := pathConnectedSpace_sph (by omega)
  constructor
  · intro a z
    exact ⟨default,
      ((RelHomotopyGroup.iStar_isPointedMap 0 (Sph (m + 1)) (sphUpperCap m) a).map_default).trans
        ((subsingleton_homotopyGroup_zero (a : Sph (m + 1))).elim _ z)⟩
  · intro k hk a
    apply nonempty_unique_relHomotopyGroup k a
    · exact subsingleton_homotopyGroup_sphere_of_lt (k + 1) (m + 1) (by omega) _
    · cases k with
      | zero =>
          letI : PathConnectedSpace (sphUpperCap m) := inferInstance
          exact subsingleton_homotopyGroup_zero a
      | succ k =>
          exact subsingleton_homotopyGroup_of_contractible (N := Fin (k + 1)) a

/-- In relative degrees at most the cap connectivity, both sides of cap excision are trivial, so
the arbitrary-degree cap map is automatically bijective. -/
theorem sphereSuspensionExcisionHomAt_bijective_below
    (m q : ℕ) (hm : 1 ≤ m) (hq : q + 2 ≤ m) :
    Function.Bijective (sphereSuspensionExcisionHomAt m q) := by
  obtain ⟨sourceUnique⟩ :=
    (isNConnectedPair_sphLowerCap_overlap m hm).unique_piRel (q + 1) (by omega)
      (sphCapOverlapBase m)
  obtain ⟨targetUnique⟩ :=
    (isNConnectedPair_sphSphere_upperCap m).unique_piRel (q + 1) (by omega)
      (sphUpperCapBase m)
  letI := sourceUnique
  letI := targetUnique
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  · intro y
    exact ⟨1, Subsingleton.elim _ y⟩

/-- Bijectivity of the canonical cap-excision map yields the equivalence between successive
metric-sphere diagonal groups. -/
theorem nonempty_sphereDiagonalSuspensionMulEquiv_of_capExcision
    (n : ℕ) (hbij : Function.Bijective (sphereSuspensionExcisionHom n)) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        HomotopyGroup.Pi (n + 2) (Sph (n + 2)) (sphereBasepoint (n + 2))) := by
  let e := sphCapOverlapHomotopyEquiv (n + 1)
  let raw := piMulEquiv_of_bijective_relativeMap
    (sphCapOverlapBase (n + 1)) (sphUpperCapBase (n + 1)) e n
    (sphCapInclusionPairMap (n + 1)) hbij
  letI : PathConnectedSpace (Sph (n + 1)) := pathConnectedSpace_sph (Nat.succ_le_succ (Nat.zero_le n))
  let p : Path (sphereBasepoint (n + 1)) (e (sphCapOverlapBase (n + 1))) :=
    PathConnectedSpace.somePath _ _
  let change := Classical.choice
    (homotopyGroup_change_basepoint n (Sph (n + 1))
      (sphereBasepoint (n + 1)) (e (sphCapOverlapBase (n + 1))) p)
  exact ⟨change.trans raw⟩

/-- Exact integral diagonal reduced to bijectivity of the canonical relative cap-inclusion maps.
This is the precise homotopy-excision form of the remaining Freudenthal input. -/
theorem sphere_diagonal_mulEquiv_int_of_capExcision
    (hbij : ∀ n : ℕ, Function.Bijective (sphereSuspensionExcisionHom n))
    (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  apply sphere_diagonal_mulEquiv_int_of_suspension_steps
  intro m
  exact nonempty_sphereDiagonalSuspensionMulEquiv_of_capExcision m (hbij m)

/-- The already-computed `π₂(S²)` base case means cap-excision bijectivity is needed only from
the `S² → S³` suspension step onward, exactly as in the Freudenthal isomorphism range. -/
theorem sphere_diagonal_mulEquiv_int_of_capExcision_from_two
    (hbij : ∀ n : ℕ, 1 ≤ n → Function.Bijective (sphereSuspensionExcisionHom n))
    (n : ℕ) :
    Nonempty
      (HomotopyGroup.Pi (n + 1) (Sph (n + 1)) (sphereBasepoint (n + 1)) ≃*
        Multiplicative ℤ) := by
  apply sphere_diagonal_mulEquiv_int_of_suspension_steps_from_two
  intro m hm
  exact nonempty_sphereDiagonalSuspensionMulEquiv_of_capExcision m (hbij m hm)

end Submission
