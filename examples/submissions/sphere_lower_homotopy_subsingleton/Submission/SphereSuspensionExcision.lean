/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.DiagonalInduction
import Submission.HigherSphereFoundations
import Submission.Homotopy.ContractionData
import Submission.IndependentResults
import Submission.SphereSuspension

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

/-- Zero height as a point of the closed belt interval. -/
def sphBeltZeroHeight : Set.Icc (-(1 / 3) : ℝ) (1 / 3) :=
  ⟨0, by constructor <;> norm_num⟩

/-- The belt-coordinate homeomorphism sends the chosen overlap basepoint to the standard sphere
basepoint at height zero. -/
theorem sphBeltHomeo_capOverlapBase (m : ℕ) :
    sphBeltHomeo m (sphCapOverlapHomeoBelt m (sphCapOverlapBase m)) =
      (sphereBasepoint m, sphBeltZeroHeight) := by
  apply (sphBeltHomeo m).symm.injective
  rw [Homeomorph.symm_apply_apply]
  change sphCapOverlapHomeoBelt m (sphCapOverlapBase m) =
    beltOfProd (sphereBasepoint m, sphBeltZeroHeight)
  apply Subtype.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp [sphCapOverlapHomeoBelt, sphCapOverlapBase, sphLowerCapBase,
        sphBeltZeroHeight, beltOfProd, beltVec, sphereBasepoint, snocLp, Fin.snoc]
  | cast j =>
      have hj : (j : ℕ) ≤ m := Nat.le_of_lt_succ j.isLt
      by_cases h : j = 0
      · subst j
        simp [sphCapOverlapHomeoBelt, sphCapOverlapBase, sphLowerCapBase,
          sphBeltZeroHeight, beltOfProd, beltVec, sphereBasepoint, snocLp,
          Fin.snoc, Pi.single_apply]
        apply Fin.ext
        rfl
      · simp [sphCapOverlapHomeoBelt, sphCapOverlapBase, sphLowerCapBase,
          sphBeltZeroHeight, beltOfProd, beltVec, sphereBasepoint, snocLp, Fin.snoc, hj, h]

/-- The maintained overlap equivalence preserves the chosen sphere basepoint exactly. -/
@[simp]
theorem sphCapOverlapHomotopyEquiv_basepoint (m : ℕ) :
    sphCapOverlapHomotopyEquiv m (sphCapOverlapBase m) = sphereBasepoint m := by
  change sphBeltHomotopyEquiv m
      (sphCapOverlapHomeoBelt m (sphCapOverlapBase m)) = sphereBasepoint m
  change (sphBeltHomeo m
      (sphCapOverlapHomeoBelt m (sphCapOverlapBase m))).1 = sphereBasepoint m
  rw [sphBeltHomeo_capOverlapBase]

/-- The constant path, typed using the exact basepoint calculation for the overlap equivalence. -/
noncomputable def sphCapOverlapBasePath (m : ℕ) :
    Path (sphereBasepoint m)
      (sphCapOverlapHomotopyEquiv m (sphCapOverlapBase m)) :=
  (Path.refl (sphereBasepoint m)).cast rfl
    (sphCapOverlapHomotopyEquiv_basepoint m)

@[simp]
theorem sphCapOverlapBasePath_apply (m : ℕ) (t : unitInterval) :
    sphCapOverlapBasePath m t = sphereBasepoint m := by
  change ((Path.refl (sphereBasepoint m)).cast rfl
    (sphCapOverlapHomotopyEquiv_basepoint m)) t = sphereBasepoint m
  rw [congrFun (Path.cast_coe _ _ _) t]
  rfl

/-! ### Functoriality of the cap model -/

/-- Suspension preserves the height coordinate in the metric-sphere model. -/
theorem sphHeight_sphereSuspensionMap (m n : ℕ)
    (f : C(Sph m, Sph n)) (z : Sph (m + 1)) :
    sphHeight (sphereSuspensionMap m n f z) = sphHeight z := by
  obtain ⟨q, rfl⟩ := (suspSphHomeo m).surjective z
  rw [sphereSuspensionMap_apply_susp, suspSphHomeo_apply,
    suspSphHomeo_apply, sphHeight_suspSphLift, sphHeight_suspSphLift]
  induction q using Susp.ind with
  | h p => rfl

/-- A sphere self-map suspends to a self-map of the enlarged lower cap. -/
noncomputable def sphLowerCapSuspensionMap (m : ℕ)
    (f : C(Sph m, Sph m)) : C(sphLowerCap m, sphLowerCap m) where
  toFun z := ⟨sphereSuspensionMap m m f z.1, by
    rw [mem_sphLowerCap, sphHeight_sphereSuspensionMap]
    exact mem_sphLowerCap.mp z.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((sphereSuspensionMap m m f).continuous.comp continuous_subtype_val) _

/-- The suspended self-map on the lower-cap/overlap pair. -/
noncomputable def sphCapSourcePairMap (m : ℕ)
    (f : C(Sph m, Sph m))
    (hf : f (sphereBasepoint m) = sphereBasepoint m) :
    BasedPairMap (sphCapOverlapInLower m) (sphCapOverlapInLower m)
      (sphCapOverlapBase m) (sphCapOverlapBase m) where
  toContinuousMap := sphLowerCapSuspensionMap m f
  mapsTo' := by
    intro z hz
    change sphereSuspensionMap m m f z.1 ∈ sphUpperCap m
    rw [mem_sphUpperCap, sphHeight_sphereSuspensionMap]
    exact mem_sphUpperCap.mp hz
  map_basepoint' := by
    apply Subtype.ext
    exact sphereSuspensionMap_basepoint m m f hf

/-- The suspended self-map on the full-sphere/upper-cap pair. -/
noncomputable def sphCapTargetPairMap (m : ℕ)
    (f : C(Sph m, Sph m))
    (hf : f (sphereBasepoint m) = sphereBasepoint m) :
    BasedPairMap (sphUpperCap m) (sphUpperCap m)
      (sphUpperCapBase m) (sphUpperCapBase m) where
  toContinuousMap := sphereSuspensionMap m m f
  mapsTo' := by
    intro z hz
    rw [mem_sphUpperCap, sphHeight_sphereSuspensionMap]
    exact mem_sphUpperCap.mp hz
  map_basepoint' := sphereSuspensionMap_basepoint m m f hf

/-- The cap inclusion square commutes with suspended sphere self-maps. -/
theorem sphCapPairMap_square (m : ℕ)
    (f : C(Sph m, Sph m))
    (hf : f (sphereBasepoint m) = sphereBasepoint m) :
    (sphCapTargetPairMap m f hf).comp (sphCapInclusionPairMap m) =
      (sphCapInclusionPairMap m).comp (sphCapSourcePairMap m f hf) := by
  rfl

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

/-- The relative cap-excision map is natural under suspension of a based sphere self-map. -/
theorem sphereSuspensionExcisionHomAt_natural (m q : ℕ)
    (f : C(Sph m, Sph m))
    (hf : f (sphereBasepoint m) = sphereBasepoint m) :
    (RelHomotopyGroup.mapHom q (sphCapTargetPairMap m f hf)).comp
        (sphereSuspensionExcisionHomAt m q) =
      (sphereSuspensionExcisionHomAt m q).comp
        (RelHomotopyGroup.mapHom q (sphCapSourcePairMap m f hf)) := by
  rw [sphereSuspensionExcisionHomAt,
    RelHomotopyGroup.mapHom_comp, RelHomotopyGroup.mapHom_comp,
    sphCapPairMap_square]

/-- The absolute cap-excision comparison before changing the source basepoint. -/
noncomputable def sphereCapSuspensionRawHomAt (m q : ℕ) :
    π_ (q + 1) (Sph m)
        (sphCapOverlapHomotopyEquiv m (sphCapOverlapBase m)) →*
      π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1)) :=
  piHom_of_relativeHom (sphCapOverlapBase m) (sphUpperCapBase m)
    (sphCapOverlapHomotopyEquiv m) q (sphereSuspensionExcisionHomAt m q)

/-- Naturality of the raw absolute cap comparison, assuming the chosen overlap equivalence
intertwines the induced overlap map with the original sphere self-map. -/
theorem sphereCapSuspensionRawHomAt_natural (m q : ℕ)
    (f : C(Sph m, Sph m))
    (hf : f (sphereBasepoint m) = sphereBasepoint m)
    (hsource : (sphCapOverlapHomotopyEquiv m).toFun.comp
        (sphCapSourcePairMap m f hf).subspaceMap =
      f.comp (sphCapOverlapHomotopyEquiv m).toFun)
    (a : π_ (q + 1) (Sph m)
      (sphCapOverlapHomotopyEquiv m (sphCapOverlapBase m))) :
    HomotopyGroup.map (sphereSuspensionMap m m f)
        (sphereSuspensionMap_basepoint m m f hf)
        (sphereCapSuspensionRawHomAt m q a) =
      sphereCapSuspensionRawHomAt m q
        (HomotopyGroup.map f (by simpa using hf) a) := by
  exact piHom_of_relativeHom_natural
    (sphCapOverlapBase m) (sphCapOverlapBase m)
    (sphUpperCapBase m) (sphUpperCapBase m)
    (sphCapOverlapHomotopyEquiv m) (sphCapOverlapHomotopyEquiv m) q
    (sphCapSourcePairMap m f hf) (sphCapTargetPairMap m f hf)
    f (by simpa using hf) hsource
    (sphereSuspensionExcisionHomAt m q) (sphereSuspensionExcisionHomAt m q)
    (sphereSuspensionExcisionHomAt_natural m q f hf) a

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

/-- The absolute sphere homomorphism obtained from cap excision by the two contractible-pair
long exact sequences.  It is an abstract suspension comparison; identifying it with either
concrete geometric suspension construction is a separate problem. -/
noncomputable def sphereCapSuspensionHomAt (m q : ℕ) (_hm : 1 ≤ m) :
    π_ (q + 1) (Sph m) (sphereBasepoint m) →*
      π_ (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1)) := by
  let change := HomotopyGroup.transportMulEquiv (N := Fin (q + 1))
    (sphCapOverlapBasePath m)
  exact (sphereCapSuspensionRawHomAt m q).comp change.toMonoidHom

/-- A surjective cap-excision map induces a surjective absolute sphere comparison. -/
theorem sphereCapSuspensionHomAt_surjective_of_capExcision
    (m q : ℕ) (hm : 1 ≤ m)
    (hsurj : Function.Surjective (sphereSuspensionExcisionHomAt m q)) :
    Function.Surjective (sphereCapSuspensionHomAt m q hm) := by
  let e := sphCapOverlapHomotopyEquiv m
  let change := HomotopyGroup.transportMulEquiv (N := Fin (q + 1))
    (sphCapOverlapBasePath m)
  change Function.Surjective
    ((piHom_of_relativeHom (sphCapOverlapBase m) (sphUpperCapBase m) e q
      (sphereSuspensionExcisionHomAt m q)).comp change.toMonoidHom)
  exact (piHom_of_relativeHom_surjective
    (sphCapOverlapBase m) (sphUpperCapBase m) e q
      (sphereSuspensionExcisionHomAt m q) hsurj).comp change.surjective

/-- An injective cap-excision map induces an injective absolute sphere comparison. -/
theorem sphereCapSuspensionHomAt_injective_of_capExcision
    (m q : ℕ) (hm : 1 ≤ m)
    (hinj : Function.Injective (sphereSuspensionExcisionHomAt m q)) :
    Function.Injective (sphereCapSuspensionHomAt m q hm) := by
  let e := sphCapOverlapHomotopyEquiv m
  let change := HomotopyGroup.transportMulEquiv (N := Fin (q + 1))
    (sphCapOverlapBasePath m)
  change Function.Injective
    ((piHom_of_relativeHom (sphCapOverlapBase m) (sphUpperCapBase m) e q
      (sphereSuspensionExcisionHomAt m q)).comp change.toMonoidHom)
  exact (piHom_of_relativeHom_injective
    (sphCapOverlapBase m) (sphUpperCapBase m) e q
      (sphereSuspensionExcisionHomAt m q) hinj).comp change.injective

/-- A bijective cap-excision map induces a bijective named absolute sphere comparison. -/
theorem sphereCapSuspensionHomAt_bijective_of_capExcision
    (m q : ℕ) (hm : 1 ≤ m)
    (hbij : Function.Bijective (sphereSuspensionExcisionHomAt m q)) :
    Function.Bijective (sphereCapSuspensionHomAt m q hm) :=
  ⟨sphereCapSuspensionHomAt_injective_of_capExcision m q hm hbij.1,
    sphereCapSuspensionHomAt_surjective_of_capExcision m q hm hbij.2⟩

/-- Bijectivity of cap excision in any relative degree gives the corresponding absolute
equivalence between the equatorial sphere and its suspension. -/
theorem nonempty_sphereSuspensionMulEquiv_of_capExcisionAt
    (m q : ℕ) (hm : 1 ≤ m)
    (hbij : Function.Bijective (sphereSuspensionExcisionHomAt m q)) :
    Nonempty
      (HomotopyGroup.Pi (q + 1) (Sph m) (sphereBasepoint m) ≃*
        HomotopyGroup.Pi (q + 2) (Sph (m + 1)) (sphereBasepoint (m + 1))) := by
  exact ⟨MulEquiv.ofBijective (sphereCapSuspensionHomAt m q hm)
    (sphereCapSuspensionHomAt_bijective_of_capExcision m q hm hbij)⟩

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
  let change := HomotopyGroup.transportMulEquiv (N := Fin (n + 1))
    (sphCapOverlapBasePath (n + 1))
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
