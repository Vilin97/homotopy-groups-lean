/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Cohomology.Cup
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Simplicial cohomology and the cup product on it

We define the cohomology of the cochain complex of `Submission/Cohomology/Cochain.lean` *by hand*,
as the quotient `ker δₙ ⧸ (im δₙ₋₁ ∩ ker δₙ)`, rather than through Mathlib's
`HomologicalComplex.homology`.

The reason for this design choice (option (b) in the brief) is that the whole point of this
development is the **cup product**, which is a *bilinear* map
`H^p × H^q → H^{p+q}`.  A concrete quotient of `R`-modules lets us build that bilinear map with
two applications of `Submodule.liftQ`, whereas producing a bilinear map out of a categorical
`HomologicalComplex.homology` object in `ModuleCat R` would require first transporting it to a
concrete `ker/range` description anyway.  No long exact sequence is needed for the cup product, so
nothing is lost.

## Main definitions

* `Submission.cocycles S R n`, `Submission.coboundaries S R n` : submodules of `Cochain S R n`.
* `Submission.Hcoh n S R` : the `n`-th cohomology module.
* `Submission.Hcoh.mk` : the class of a cocycle.
* `Submission.Hcoh.map φ n : Hcoh n T R →ₗ[R] Hcoh n S R` : contravariant functoriality.
* `Submission.cupH h : Hcoh p S R →ₗ[R] Hcoh q S R →ₗ[R] Hcoh n S R` : the cup product on
  cohomology.

## Main results

* `Submission.cupH_mk` : the cup product on cohomology is computed by the cup product of
  representing cocycles.
* `Submission.cupH_assoc` : associativity.
* `Submission.one_cupH`, `Submission.cupH_one` : unitality.
* `Submission.map_cupH` : naturality.
-/

namespace Submission

open CategoryTheory Simplicial

section Defs

variable (S : SSet.{0}) (R : Type) [CommRing R]

/-- The submodule of `n`-cocycles: cochains killed by the coboundary operator. -/
def cocycles (n : ℕ) : Submodule R (Cochain S R n) := LinearMap.ker (coboundary S R n)

/-- The submodule of `n`-coboundaries. -/
def coboundaries : ∀ n : ℕ, Submodule R (Cochain S R n)
  | 0 => ⊥
  | m + 1 => LinearMap.range (coboundary S R m)

@[simp]
theorem coboundaries_zero : coboundaries S R 0 = ⊥ := rfl

@[simp]
theorem coboundaries_succ (m : ℕ) :
    coboundaries S R (m + 1) = LinearMap.range (coboundary S R m) := rfl

variable {S R}

theorem mem_cocycles_iff {n : ℕ} (f : Cochain S R n) :
    f ∈ cocycles S R n ↔ coboundary S R n f = 0 := Iff.rfl

theorem coboundaries_le_cocycles (n : ℕ) : coboundaries S R n ≤ cocycles S R n := by
  cases n with
  | zero => exact bot_le
  | succ m =>
      rintro _ ⟨f, rfl⟩
      exact coboundary_coboundary f

variable (S R)

/-- The coboundaries, viewed as a submodule of the cocycles. -/
def coboundariesIn (n : ℕ) : Submodule R (cocycles S R n) :=
  Submodule.comap (cocycles S R n).subtype (coboundaries S R n)

/-- The `n`-th cohomology module of a simplicial set with coefficients in `R`. -/
def Hcoh (n : ℕ) (S : SSet.{0}) (R : Type) [CommRing R] : Type :=
  (cocycles S R n) ⧸ (coboundariesIn S R n)

instance (n : ℕ) : AddCommGroup (Hcoh n S R) :=
  inferInstanceAs (AddCommGroup ((cocycles S R n) ⧸ (coboundariesIn S R n)))

instance (n : ℕ) : Module R (Hcoh n S R) :=
  inferInstanceAs (Module R ((cocycles S R n) ⧸ (coboundariesIn S R n)))

end Defs

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- The cohomology class of a cocycle. -/
def Hcoh.mk {n : ℕ} (f : cocycles S R n) : Hcoh n S R :=
  Submodule.Quotient.mk (p := coboundariesIn S R n) f

theorem Hcoh.mk_surjective {n : ℕ} (x : Hcoh n S R) : ∃ f : cocycles S R n, Hcoh.mk f = x :=
  Quotient.exists_rep x

theorem Hcoh.mk_eq_zero_iff {n : ℕ} (f : cocycles S R n) :
    Hcoh.mk f = 0 ↔ (f : Cochain S R n) ∈ coboundaries S R n :=
  Submodule.Quotient.mk_eq_zero _

@[elab_as_elim]
theorem Hcoh.induction_on {n : ℕ} {motive : Hcoh n S R → Prop} (x : Hcoh n S R)
    (h : ∀ f : cocycles S R n, motive (Hcoh.mk f)) : motive x :=
  Quotient.inductionOn' x h

/-- The canonical projection from cocycles to cohomology, as a linear map. -/
def Hcoh.mkₗ (n : ℕ) : cocycles S R n →ₗ[R] Hcoh n S R :=
  (coboundariesIn S R n).mkQ

@[simp]
theorem Hcoh.mkₗ_apply {n : ℕ} (f : cocycles S R n) : Hcoh.mkₗ n f = Hcoh.mk f := rfl

/-! ### The cup product on cohomology -/

/-- The cup product of two cocycles is a cocycle. -/
theorem cupOfEq_mem_cocycles {p q n : ℕ} (h : p + q = n) {f : Cochain S R p} {g : Cochain S R q}
    (hf : f ∈ cocycles S R p) (hg : g ∈ cocycles S R q) : cupOfEq h f g ∈ cocycles S R n := by
  rw [mem_cocycles_iff, coboundary_cupOfEq h, (mem_cocycles_iff f).1 hf,
    (mem_cocycles_iff g).1 hg, zero_cupOfEq, cupOfEq_zero, smul_zero, add_zero]

/-- The cup product of a coboundary with a cocycle is a coboundary. -/
theorem cupOfEq_mem_coboundaries_left {p q n : ℕ} (h : p + q = n) {f : Cochain S R p}
    {g : Cochain S R q} (hf : f ∈ coboundaries S R p) (hg : g ∈ cocycles S R q) :
    cupOfEq h f g ∈ coboundaries S R n := by
  cases p with
  | zero =>
      rw [coboundaries_zero, Submodule.mem_bot] at hf
      subst hf
      rw [zero_cupOfEq]
      exact Submodule.zero_mem _
  | succ p' =>
      obtain ⟨f', rfl⟩ := hf
      cases n with
      | zero => omega
      | succ m =>
          refine ⟨cupOfEq (by omega : p' + q = m) f' g, ?_⟩
          rw [coboundary_cupOfEq (by omega : p' + q = m), (mem_cocycles_iff g).1 hg,
            cupOfEq_zero, smul_zero, add_zero]

/-- The cup product of a cocycle with a coboundary is a coboundary. -/
theorem cupOfEq_mem_coboundaries_right {p q n : ℕ} (h : p + q = n) {f : Cochain S R p}
    {g : Cochain S R q} (hf : f ∈ cocycles S R p) (hg : g ∈ coboundaries S R q) :
    cupOfEq h f g ∈ coboundaries S R n := by
  cases q with
  | zero =>
      rw [coboundaries_zero, Submodule.mem_bot] at hg
      subst hg
      rw [cupOfEq_zero]
      exact Submodule.zero_mem _
  | succ q' =>
      obtain ⟨g', rfl⟩ := hg
      cases n with
      | zero => omega
      | succ m =>
          refine ⟨(-1 : R) ^ p • cupOfEq (by omega : p + q' = m) f g', ?_⟩
          rw [map_smul, coboundary_cupOfEq (by omega : p + q' = m), (mem_cocycles_iff f).1 hf,
            zero_cupOfEq, zero_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp

variable (S R) in
/-- The cup product of cocycles, as an `R`-bilinear map. -/
def cupCocyclesₗ {p q n : ℕ} (h : p + q = n) :
    cocycles S R p →ₗ[R] cocycles S R q →ₗ[R] cocycles S R n :=
  LinearMap.mk₂ R
    (fun f g ↦ ⟨cupOfEq h (f : Cochain S R p) (g : Cochain S R q),
      cupOfEq_mem_cocycles h f.2 g.2⟩)
    (fun f₁ f₂ g ↦ by
      apply Subtype.ext
      ext σ
      simp only [cupOfEq_apply, Submodule.coe_add, Cochain.add_apply]
      ring)
    (fun r f g ↦ by
      apply Subtype.ext
      ext σ
      simp only [cupOfEq_apply, SetLike.val_smul, Cochain.smul_apply]
      ring)
    (fun f g₁ g₂ ↦ by
      apply Subtype.ext
      ext σ
      simp only [cupOfEq_apply, Submodule.coe_add, Cochain.add_apply]
      ring)
    (fun r f g ↦ by
      apply Subtype.ext
      ext σ
      simp only [cupOfEq_apply, SetLike.val_smul, Cochain.smul_apply]
      ring)

@[simp]
theorem cupCocyclesₗ_apply_coe {p q n : ℕ} (h : p + q = n) (f : cocycles S R p)
    (g : cocycles S R q) :
    ((cupCocyclesₗ S R h f g : cocycles S R n) : Cochain S R n) =
      cupOfEq h (f : Cochain S R p) (g : Cochain S R q) := rfl

/-- The cup product on cohomology, as an `R`-bilinear map. -/
def cupH {p q n : ℕ} (h : p + q = n) :
    Hcoh p S R →ₗ[R] Hcoh q S R →ₗ[R] Hcoh n S R :=
  Submodule.liftQ _
    (Submodule.liftQ (coboundariesIn S R q)
      (LinearMap.compr₂ (cupCocyclesₗ S R h) (Hcoh.mkₗ n)).flip
      (by
        rintro g hg
        ext f
        exact (Hcoh.mk_eq_zero_iff _).2
          (cupOfEq_mem_coboundaries_right h f.2 hg))).flip
    (by
      rintro f hf
      ext x
      refine Hcoh.induction_on x fun g ↦ ?_
      exact (Hcoh.mk_eq_zero_iff _).2 (cupOfEq_mem_coboundaries_left h hf g.2))

@[simp]
theorem cupH_mk {p q n : ℕ} (h : p + q = n) (f : cocycles S R p) (g : cocycles S R q) :
    cupH h (Hcoh.mk f) (Hcoh.mk g) = Hcoh.mk (cupCocyclesₗ S R h f g) := rfl

/-! ### The unit -/

/-- The unit cochain is a cocycle. -/
def oneCocycle (S : SSet.{0}) (R : Type) [CommRing R] : cocycles S R 0 :=
  ⟨Cochain.one S R, coboundary_one⟩

/-- The unit class in `H⁰`. -/
def Hcoh.one (S : SSet.{0}) (R : Type) [CommRing R] : Hcoh 0 S R := Hcoh.mk (oneCocycle S R)

theorem one_cupH {q : ℕ} (x : Hcoh q S R) : cupH (Nat.zero_add q) (Hcoh.one S R) x = x := by
  refine Hcoh.induction_on x fun g ↦ ?_
  rw [Hcoh.one, cupH_mk]
  congr 1
  ext1
  exact one_cup (g : Cochain S R q)

theorem cupH_one {p : ℕ} (x : Hcoh p S R) : cupH (Nat.add_zero p) x (Hcoh.one S R) = x := by
  refine Hcoh.induction_on x fun f ↦ ?_
  rw [Hcoh.one, cupH_mk]
  congr 1
  ext1
  exact cup_one (f : Cochain S R p)

/-! ### Associativity -/

theorem cupH_assoc {p q r m n k : ℕ} (hm : p + q = m) (hn : q + r = n) (hk : p + q + r = k)
    (x : Hcoh p S R) (y : Hcoh q S R) (z : Hcoh r S R) :
    cupH (by omega : m + r = k) (cupH hm x y) z =
      cupH (by omega : p + n = k) x (cupH hn y z) := by
  refine Hcoh.induction_on x fun f ↦ Hcoh.induction_on y fun g ↦ Hcoh.induction_on z fun h ↦ ?_
  simp only [cupH_mk]
  congr 1
  ext1
  exact cupOfEq_assoc hm hn hk (f : Cochain S R p) (g : Cochain S R q) (h : Cochain S R r)

/-! ### Functoriality -/

/-- Pullback of cochains restricts to cocycles. -/
theorem pullback_mem_cocycles {S T : SSet.{0}} (φ : S ⟶ T) {n : ℕ} {f : Cochain T R n}
    (hf : f ∈ cocycles T R n) : Cochain.pullback φ n f ∈ cocycles S R n := by
  have := congrArg (fun m ↦ (m : Cochain T R n →ₗ[R] Cochain S R (n + 1)) f)
    (pullback_coboundary (R := R) φ n)
  simpa [(mem_cocycles_iff f).1 hf, mem_cocycles_iff] using this.symm

/-- Pullback of cochains sends coboundaries to coboundaries. -/
theorem pullback_mem_coboundaries {S T : SSet.{0}} (φ : S ⟶ T) {n : ℕ} {f : Cochain T R n}
    (hf : f ∈ coboundaries T R n) : Cochain.pullback φ n f ∈ coboundaries S R n := by
  cases n with
  | zero =>
      rw [coboundaries_zero, Submodule.mem_bot] at hf
      subst hf
      simp
  | succ m =>
      obtain ⟨f', rfl⟩ := hf
      refine ⟨Cochain.pullback φ m f', ?_⟩
      exact congrArg (fun l ↦ (l : Cochain T R m →ₗ[R] Cochain S R (m + 1)) f')
        (pullback_coboundary (R := R) φ m).symm

variable (R) in
/-- Pullback of cocycles along a morphism of simplicial sets. -/
def cocyclesMap {S T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) :
    cocycles T R n →ₗ[R] cocycles S R n :=
  ((Cochain.pullback φ n).comp (cocycles T R n).subtype).codRestrict _
    fun f ↦ pullback_mem_cocycles φ f.2

variable (R) in
/-- The map induced on cohomology by a morphism of simplicial sets. -/
def Hcoh.map {S T : SSet.{0}} (φ : S ⟶ T) (n : ℕ) : Hcoh n T R →ₗ[R] Hcoh n S R :=
  Submodule.mapQ _ _ (cocyclesMap R φ n) (by
    rintro f hf
    exact pullback_mem_coboundaries φ hf)

@[simp]
theorem Hcoh.map_mk {S T : SSet.{0}} (φ : S ⟶ T) {n : ℕ} (f : cocycles T R n) :
    Hcoh.map R φ n (Hcoh.mk f) = Hcoh.mk (cocyclesMap R φ n f) := rfl

@[simp]
theorem Hcoh.map_id (S : SSet.{0}) (n : ℕ) :
    Hcoh.map R (𝟙 S) n = LinearMap.id (R := R) (M := Hcoh n S R) := by
  ext x
  refine Hcoh.induction_on x fun f ↦ ?_
  rfl

theorem Hcoh.map_comp {S T U : SSet.{0}} (φ : S ⟶ T) (ψ : T ⟶ U) (n : ℕ) :
    Hcoh.map R (φ ≫ ψ) n = (Hcoh.map R φ n).comp (Hcoh.map R ψ n) := by
  ext x
  refine Hcoh.induction_on x fun f ↦ ?_
  rfl

/-- **Naturality** of the cup product on cohomology. -/
theorem map_cupH {S T : SSet.{0}} (φ : S ⟶ T) {p q n : ℕ} (h : p + q = n)
    (x : Hcoh p T R) (y : Hcoh q T R) :
    Hcoh.map R φ n (cupH h x y) = cupH h (Hcoh.map R φ p x) (Hcoh.map R φ q y) := by
  refine Hcoh.induction_on x fun f ↦ Hcoh.induction_on y fun g ↦ ?_
  simp only [cupH_mk, Hcoh.map_mk]
  congr 1
  ext1
  exact pullback_cupOfEq φ h (f : Cochain T R p) (g : Cochain T R q)

end Submission
