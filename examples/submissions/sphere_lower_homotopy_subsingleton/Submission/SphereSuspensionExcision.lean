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

/-- The overlap in the lower cap is homotopy-equivalent to the equatorial metric sphere. -/
noncomputable def sphCapOverlapHomotopyEquiv (m : ℕ) :
    ContinuousMap.HomotopyEquiv (sphCapOverlapInLower m) (Sph m) :=
  (sphCapOverlapHomeoBelt m).toHomotopyEquiv.trans (sphBeltHomotopyEquiv m)

/-- The canonical relative homotopy homomorphism appearing in suspension excision for the
`(n+1)`-sphere. -/
noncomputable def sphereSuspensionExcisionHom (n : ℕ) :
    π_rel (n + 2) (sphLowerCap (n + 1)) (sphCapOverlapInLower (n + 1))
        (sphCapOverlapBase (n + 1)) →*
      π_rel (n + 2) (Sph (n + 2)) (sphUpperCap (n + 1))
        (sphUpperCapBase (n + 1)) :=
  RelHomotopyGroup.mapHom n (sphCapInclusionPairMap (n + 1))

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

end Submission
