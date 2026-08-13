/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Approximation.SphereCapExcisionSurjective
import Submission.SphereReducedSuspensionBijective
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas

/-!
# A one-generator presentation of the first stable stem

Freudenthal edge surjectivity presents `pi_4(S^3)` as a quotient of the already computed group
`pi_3(S^2) ≃ Z`.  This file uses the concrete Hopf-map image of the canonical generator upstairs,
names its cap-suspension image downstairs, and records the resulting one-generator presentation.
Consequently the exact first-stem computation is reduced to the concrete assertion that this
edge generator has order two.
-/

open scoped Topology Topology.Homotopy

noncomputable section

namespace Submission

/-- The concrete Hopf map sends the canonical generator of `pi_3(S^3)` to a generator of
`pi_3(S^2)`. -/
noncomputable def piThreeSphereTwoHopfGenerator :
    π_ 3 (Sph 2) (sphereBasepoint 2) :=
  hopfPiThreeHom (sphereGeneratorClass 3)

/-- This chosen generator is exactly the cubical class represented by the concrete quadratic
Hopf map. -/
theorem piThreeSphereTwoHopfGenerator_eq_hopfMapClass :
    piThreeSphereTwoHopfGenerator =
      sphereTargetMapClass 3 hopfMap hopfMap_basepoint := by
  rw [sphereTargetMapClass_eq_map_generator]
  rfl

/-- The Hopf-map image is indeed a generator of `pi_3(S^2)`. -/
theorem piThreeSphereTwoHopfGenerator_generates :
    ∀ x : π_ 3 (Sph 2) (sphereBasepoint 2),
      x ∈ Subgroup.zpowers piThreeSphereTwoHopfGenerator := by
  simpa only [piThreeSphereTwoHopfGenerator, hopfPiThreeEquiv,
    MulEquiv.ofBijective_apply] using
    (forall_mem_zpowers_map_mulEquiv
      (hopfPiThreeEquiv hopfMap_isSerreFibration)
      (sphereGeneratorClass_generates_succ 1))

/-- The distinguished first-stem element is the cap-suspension image of the concrete Hopf
generator. -/
noncomputable def piFourSphereThreeEdgeGenerator :
    π_ 4 (Sph 3) (sphereBasepoint 3) :=
  sphereCapSuspensionHomAt 2 2 (by omega) piThreeSphereTwoHopfGenerator

/-- The Freudenthal edge presentation of `pi_4(S^3)` by integer powers of the distinguished
edge generator. -/
noncomputable def piFourSphereThreePresentationHom :
    Multiplicative ℤ →* π_ 4 (Sph 3) (sphereBasepoint 3) :=
  zpowersHom (π_ 4 (Sph 3) (sphereBasepoint 3)) piFourSphereThreeEdgeGenerator

/-- The edge presentation is onto. -/
theorem piFourSphereThreePresentationHom_surjective :
    Function.Surjective piFourSphereThreePresentationHom := by
  intro y
  obtain ⟨x, hx⟩ := sphereCapSuspensionHomAt_two_two_surjective y
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.mp (piThreeSphereTwoHopfGenerator_generates x)
  refine ⟨Multiplicative.ofAdd k, ?_⟩
  rw [piFourSphereThreePresentationHom, zpowersHom_apply]
  change
    (sphereCapSuspensionHomAt 2 2 (by omega) piThreeSphereTwoHopfGenerator) ^ k = y
  rw [← map_zpow, hk, hx]

/-- The edge presentation is the universal integer-power homomorphism associated to its
distinguished generator. -/
theorem piFourSphereThreePresentationHom_eq_zpowersHom :
    piFourSphereThreePresentationHom =
      zpowersHom (π_ 4 (Sph 3) (sphereBasepoint 3)) piFourSphereThreeEdgeGenerator :=
  rfl

/-- The distinguished Freudenthal-edge element generates all of `pi_4(S^3)`. -/
theorem piFourSphereThreeEdgeGenerator_zpowers_eq_top :
    Subgroup.zpowers piFourSphereThreeEdgeGenerator = ⊤ := by
  rw [← Subgroup.range_zpowersHom, ← piFourSphereThreePresentationHom_eq_zpowersHom]
  exact MonoidHom.range_eq_top.mpr piFourSphereThreePresentationHom_surjective

/-- The order of the edge generator is precisely the previously isolated cardinal modulus. -/
theorem orderOf_piFourSphereThreeEdgeGenerator :
    orderOf piFourSphereThreeEdgeGenerator = piFourSphereThreeModulus := by
  rw [piFourSphereThreeModulus]
  exact orderOf_eq_card_of_zpowers_eq_top piFourSphereThreeEdgeGenerator_zpowers_eq_top

/-- The kernel of the integer presentation consists exactly of the multiples of the first-stem
modulus.  Proving that this is the even subgroup is therefore equivalent to computing the stem. -/
theorem piFourSphereThreePresentationHom_ker :
    piFourSphereThreePresentationHom.ker =
      Subgroup.zpowers
        (Multiplicative.ofAdd (piFourSphereThreeModulus : ℤ)) := by
  rw [piFourSphereThreePresentationHom_eq_zpowersHom, zpowersHom_ker_eq,
    orderOf_piFourSphereThreeEdgeGenerator]

/-- Equivalently, the exact first-stem computation says that the kernel of its integer
presentation is the subgroup of even integers. -/
theorem piFourSphereThreePresentationHom_ker_eq_even_iff :
    piFourSphereThreePresentationHom.ker =
        Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ)) ↔
      piFourSphereThreeModulus = 2 := by
  constructor
  · intro hker
    have hz :
        Subgroup.zpowers (Multiplicative.ofAdd (2 : ℤ)) =
          Subgroup.zpowers
            (Multiplicative.ofAdd (piFourSphereThreeModulus : ℤ)) := by
      rw [← piFourSphereThreePresentationHom_ker, hker]
    rcases (Subgroup.zpowers_eq_zpowers_iff
      (by simp [isOfFinOrder_iff_pow_eq_one] :
        ¬ IsOfFinOrder (Multiplicative.ofAdd (2 : ℤ)))).mp hz with h | h
    · have hi := congrArg Multiplicative.toAdd h
      norm_num at hi ⊢
      omega
    · have hi := congrArg Multiplicative.toAdd h
      simp at hi
  · intro hmod
    rw [piFourSphereThreePresentationHom_ker, hmod]
    norm_num

/-- A generator-compatible cyclic coordinate on the first stable representative. -/
noncomputable def piFourSphereThreeEdgeMulEquivZMod :
    π_ 4 (Sph 3) (sphereBasepoint 3) ≃*
      Multiplicative (ZMod piFourSphereThreeModulus) :=
  (zmodMulEquivOfGenerator
    (fun x ↦ by rw [piFourSphereThreeEdgeGenerator_zpowers_eq_top]; exact trivial)
    rfl).symm

/-- In the generator-compatible coordinate, the edge generator is the residue class of one. -/
@[simp]
theorem piFourSphereThreeEdgeMulEquivZMod_generator :
    piFourSphereThreeEdgeMulEquivZMod piFourSphereThreeEdgeGenerator =
      Multiplicative.ofAdd (1 : ZMod piFourSphereThreeModulus) := by
  exact zmodMulEquivOfGenerator_symm_apply_generator
    (fun x ↦ by rw [piFourSphereThreeEdgeGenerator_zpowers_eq_top]; exact trivial) rfl

/-- The first stable-stem benchmark is exactly the assertion that the distinguished edge
generator has order two. -/
theorem orderOf_piFourSphereThreeEdgeGenerator_eq_two_iff :
    orderOf piFourSphereThreeEdgeGenerator = 2 ↔
      Nonempty
        (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) := by
  rw [orderOf_piFourSphereThreeEdgeGenerator]
  exact piFourSphereThreeModulus_eq_two_iff

/-- The exact benchmark splits into its two geometric halves: the edge generator is killed by
doubling, but is not itself null. -/
theorem piFourSphereThree_mulEquiv_zmod_two_iff_edge_square_and_nontrivial :
    Nonempty
        (π_ 4 (Sph 3) (sphereBasepoint 3) ≃* Multiplicative (ZMod 2)) ↔
      piFourSphereThreeEdgeGenerator ^ 2 = 1 ∧
        piFourSphereThreeEdgeGenerator ≠ 1 := by
  rw [← orderOf_piFourSphereThreeEdgeGenerator_eq_two_iff]
  exact orderOf_eq_prime_iff

/-- Once the edge generator is shown to have order two, the proved stable cap-excision theorem
propagates the computation through the entire first stable stem. -/
theorem sphereFirstStableStem_mulEquiv_zmod_two_of_orderOf_edgeGenerator
    (r : ℕ) (horder : orderOf piFourSphereThreeEdgeGenerator = 2) :
    Nonempty
      (π_ (3 + r + 1) (Sph (3 + r)) (sphereBasepoint (3 + r)) ≃*
        Multiplicative (ZMod 2)) := by
  have h := sphere_stable_stem_mulEquiv_of_capExcision
    sphereSuspensionExcisionStableRange_proved 1 r
    (orderOf_piFourSphereThreeEdgeGenerator_eq_two_iff.mp horder)
  exact h

/-- Usual sphere-dimension indexing of the same conditional first-stable-stem theorem. -/
theorem sphere_first_stable_homotopy_mulEquiv_zmod_two_of_orderOf_edgeGenerator
    (n : ℕ) (hn : 3 ≤ n)
    (horder : orderOf piFourSphereThreeEdgeGenerator = 2) :
    Nonempty
      (π_ (n + 1) (Sph n) (sphereBasepoint n) ≃*
        Multiplicative (ZMod 2)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact sphereFirstStableStem_mulEquiv_zmod_two_of_orderOf_edgeGenerator r horder

end Submission
