/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homotopy.CubePair
import Submission.ForMathlib.HomotopyGroup.Map
import Submission.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq

/-!
# The long exact sequence of a Serre fibration

Let `p : C(E, B)` be a Serre fibration, `b : B`, `F := p ⁻¹' {b}` the fibre and `e : F` a
basepoint. Postcomposition with `p` gives a map
`pStar : π_rel n E F e → π_ n B b` from the relative homotopy set of the pair `(E, F)` to the
`n`-th homotopy group of the base, and the central theorem of this file is that `pStar` is a
bijection in positive degrees (Hatcher, Theorem 4.41).

Splicing that bijection into the long exact sequence of the pair `(E, F)` — which the vendored
`WhiteheadTheorem` library provides — gives the long exact sequence of the fibration

`… → π_(n+1)(F) → π_(n+1)(E) → π_(n+1)(B) --∂--> π_n(F) → π_n(E) → π_n(B) → …`

as a sequence of pointed sets, with `∂ = bd ∘ pStar⁻¹`.

## Main definitions

* `Submission.pStar` — the map `π_rel n E F e → π_ n B b`.
* `Submission.pStarAbs` — the map `π_ n E e → π_ n B b` induced by `p`.
* `Submission.fibDelta` — the connecting map `π_ (n+1) B b → π_ n F e`.

## Main results

* `Submission.bijective_pStar` — `pStar` is bijective in positive degrees.
* `Submission.isExactAt_iStar_pStarAbs`, `Submission.isExactAt_pStarAbs_fibDelta`,
  `Submission.isExactAt_fibDelta_iStar` — exactness of the three consecutive spots.
* `Submission.pStarAbsHom`, `Submission.iStarFibHom` — the two maps `π_(k+1)(F) → π_(k+1)(E)`
  and `π_(k+1)(E) → π_(k+1)(B)` are group homomorphisms.
* `Submission.bijective_pStarAbs_of_subsingleton_fibre` — if the fibre is weakly contractible,
  `π_(k+1)(E) → π_(k+1)(B)` is bijective.
* `Submission.surjective_fibDelta_of_subsingleton`,
  `Submission.fibDelta_eq_default_iff_of_subsingleton` — behaviour of `∂` when the total space
  is weakly contractible.
-/

noncomputable section

namespace Submission

open scoped unitInterval Topology Topology.Homotopy

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)} {b : B}

section PStar

variable (e : (⇑p ⁻¹' {b} : Set E))

/-- A point of the fibre is sent to the basepoint of the base. -/
theorem apply_coe_fibre : p ↑e = b := e.2

/-- Postcomposition with `p` turns a relative loop of the pair `(E, p ⁻¹' {b})` into a
generalized loop in `B`. -/
def pGenLoop {n : ℕ} (f : RelGenLoop n E (⇑p ⁻¹' {b}) e) : Ω^ (Fin n) B b :=
  ⟨p.comp f.1, fun y hy => f.2.1 y hy⟩

@[simp]
theorem pGenLoop_apply {n : ℕ} (f : RelGenLoop n E (⇑p ⁻¹' {b}) e) (y : I^ Fin n) :
    (pGenLoop e f : C(I^ Fin n, B)) y = p (f.1 y) := rfl

/-- The map `π_rel n (E, F, e) → π_ n B b` induced by `p`. -/
def pStar (n : ℕ) : π_rel n E (⇑p ⁻¹' {b}) e → π_ n B b :=
  Quotient.lift (fun f => (⟦pGenLoop e f⟧ : π_ n B b)) <| by
    rintro f g ⟨H⟩
    refine Quotient.sound (Nonempty.intro ?_)
    exact
      { toFun := fun z => p (H z)
        continuous_toFun := p.continuous.comp (map_continuous H)
        map_zero_left := fun y => congrArg p (H.apply_zero y)
        map_one_left := fun y => congrArg p (H.apply_one y)
        prop' := fun t y hy => by
          have h1 : p (H (t, y)) = b := (H.prop t).1 y hy
          have h2 : p (f.1 y) = b := f.2.1 y hy
          simpa [h2] using h1 }

@[simp]
theorem pStar_mk {n : ℕ} (f : RelGenLoop n E (⇑p ⁻¹' {b}) e) :
    pStar e n ⟦f⟧ = ⟦pGenLoop e f⟧ := rfl

/-! ### Surjectivity -/

theorem surjective_pStar (hp : IsSerreFibration p) (n : ℕ) :
    Function.Surjective (pStar e (n + 1)) := by
  refine Quotient.ind fun f => ?_
  obtain ⟨G, hG₁, hG₂⟩ := hp.hasRLPAlong_boundaryJarIncl n (f : C(I^ Fin (n + 1), B))
    (ContinuousMap.const _ (e : E)) (fun a => by
      have ha : (a : I^ Fin (n + 1)) ∈ (∂I^(n+1)) := Cube.boundaryJar_subset_boundary _ a.2
      exact e.2.trans (f.2 _ ha).symm)
  have hmem : G ∈ RelGenLoop (n + 1) E (⇑p ⁻¹' {b}) e := by
    refine ⟨fun y hy => ?_, fun y hy => hG₁ ⟨y, hy⟩⟩
    show p (G y) = b
    exact (hG₂ y).trans (f.2 y hy)
  refine ⟨⟦⟨G, hmem⟩⟧, ?_⟩
  rw [pStar_mk]
  exact congrArg _ (Subtype.ext (ContinuousMap.ext hG₂))

/-! ### Injectivity -/

/-- The partial lift used to prove injectivity of `pStar`: on the homotopy jar it is the first
relative loop near time `0`, the second one near time `1`, and the basepoint on the jar of the
cube (where the two agree). -/
def injLift {n : ℕ} (f g : RelGenLoop (n + 1) E (⇑p ⁻¹' {b}) e) :
    C(homotopyJarSet n, E) where
  toFun z := if ((z : I × (I^ Fin (n + 1))).1 : ℝ) ≤ 1 / 2 then f.1 z.1.2 else g.1 z.1.2
  continuous_toFun := by
    refine Continuous.if_le
      (f.1.continuous.comp (continuous_snd.comp continuous_subtype_val))
      (g.1.continuous.comp (continuous_snd.comp continuous_subtype_val))
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
      continuous_const (fun z hz => ?_)
    have hjar : (z : I × (I^ Fin (n + 1))).2 ∈ (⊔I^(n+1)) := by
      rcases z.2 with h | h | h
      · exact h
      · exfalso; rw [h] at hz; norm_num at hz
      · exfalso; rw [h] at hz; norm_num at hz
    rw [f.2.2 _ hjar, g.2.2 _ hjar]

theorem injLift_of_fst_le {n : ℕ} (f g : RelGenLoop (n + 1) E (⇑p ⁻¹' {b}) e)
    (z : homotopyJarSet n) (hz : ((z : I × (I^ Fin (n + 1))).1 : ℝ) ≤ 1 / 2) :
    injLift e f g z = f.1 z.1.2 := if_pos hz

theorem injLift_of_not_fst_le {n : ℕ} (f g : RelGenLoop (n + 1) E (⇑p ⁻¹' {b}) e)
    (z : homotopyJarSet n) (hz : ¬ ((z : I × (I^ Fin (n + 1))).1 : ℝ) ≤ 1 / 2) :
    injLift e f g z = g.1 z.1.2 := if_neg hz

theorem injective_pStar (hp : IsSerreFibration p) (n : ℕ) :
    Function.Injective (pStar e (n + 1)) := by
  refine Quotient.ind fun f => Quotient.ind fun g => fun hfg => ?_
  obtain ⟨H⟩ := Quotient.exact hfg
  -- `H` is a homotopy from `p ∘ f` to `p ∘ g` which is constant equal to `b` on `∂I^(n+1)`.
  have hHbdry : ∀ (t : I) (y : I^ Fin (n + 1)), y ∈ (∂I^(n+1)) → H (t, y) = b := by
    intro t y hy
    have h1 : H (t, y) = (pGenLoop e f : C(I^ Fin (n + 1), B)) y := H.prop t y hy
    exact h1.trans (f.2.1 y hy)
  have hcompat : ∀ a : homotopyJarSet n,
      p (injLift e f g a) = H.toHomotopy.toContinuousMap (homotopyJarIncl n a) := by
    intro a
    rcases a.2 with h | h | h
    · have hb : H (a.1) = b := hHbdry a.1.1 a.1.2 (Cube.boundaryJar_subset_boundary _ h)
      show p (injLift e f g a) = H a.1
      rw [hb]
      by_cases hc : ((a.1.1 : ℝ)) ≤ 1 / 2
      · rw [injLift_of_fst_le e f g a hc, f.2.2 _ h]; exact e.2
      · rw [injLift_of_not_fst_le e f g a hc, g.2.2 _ h]; exact e.2
    · have hc : ((a.1.1 : ℝ)) ≤ 1 / 2 := by rw [h]; norm_num
      rw [injLift_of_fst_le e f g a hc]
      show p (f.1 a.1.2) = H a.1
      conv_rhs => rw [show a.1 = ((0 : I), a.1.2) from Prod.ext h rfl]
      exact (H.apply_zero a.1.2).symm
    · have hc : ¬ ((a.1.1 : ℝ)) ≤ 1 / 2 := by rw [h]; norm_num
      rw [injLift_of_not_fst_le e f g a hc]
      show p (g.1 a.1.2) = H a.1
      conv_rhs => rw [show a.1 = ((1 : I), a.1.2) from Prod.ext h rfl]
      exact (H.apply_one a.1.2).symm
  obtain ⟨K, hK₁, hK₂⟩ := hp.hasRLPAlong_homotopyJarIncl n H.toHomotopy.toContinuousMap
    (injLift e f g) hcompat
  have hK₁' : ∀ (z : I × (I^ Fin (n + 1))) (hz : z ∈ homotopyJarSet n),
      K z = injLift e f g ⟨z, hz⟩ := fun z hz => hK₁ ⟨z, hz⟩
  have hzero : ∀ y : I^ Fin (n + 1), K (0, y) = f.1 y := by
    intro y
    have hmem : ((0 : I), y) ∈ homotopyJarSet n := Or.inr (Or.inl rfl)
    rw [hK₁' _ hmem, injLift_of_fst_le e f g ⟨((0 : I), y), hmem⟩ (by norm_num)]
  have hone : ∀ y : I^ Fin (n + 1), K (1, y) = g.1 y := by
    intro y
    have hmem : ((1 : I), y) ∈ homotopyJarSet n := Or.inr (Or.inr rfl)
    rw [hK₁' _ hmem, injLift_of_not_fst_le e f g ⟨((1 : I), y), hmem⟩ (by norm_num)]
  have hjar : ∀ (t : I) (y : I^ Fin (n + 1)), y ∈ (⊔I^(n+1)) → K (t, y) = (e : E) := by
    intro t y hy
    have hmem : ((t : I), y) ∈ homotopyJarSet n := Or.inl hy
    rw [hK₁' _ hmem]
    by_cases h : ((t : ℝ)) ≤ 1 / 2
    · rw [injLift_of_fst_le e f g ⟨(t, y), hmem⟩ h]; exact f.2.2 _ hy
    · rw [injLift_of_not_fst_le e f g ⟨(t, y), hmem⟩ h]; exact g.2.2 _ hy
  refine Quotient.sound (Nonempty.intro ?_)
  exact
    { toFun := fun z => K z
      continuous_toFun := K.continuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := fun t =>
        ⟨fun y hy => by
          show p (K (t, y)) = b
          exact (hK₂ (t, y)).trans (hHbdry t y hy),
         fun y hy => hjar t y hy⟩ }

/-- **The key theorem**: for a Serre fibration, postcomposition with `p` is a bijection from the
relative homotopy set of the pair `(E, p ⁻¹' {b})` to the homotopy group of the base, in every
positive degree. -/
theorem bijective_pStar (hp : IsSerreFibration p) (n : ℕ) :
    Function.Bijective (pStar e (n + 1)) :=
  ⟨injective_pStar e hp n, surjective_pStar e hp n⟩

end PStar

/-! ## The long exact sequence -/

section LES

variable (e : (⇑p ⁻¹' {b} : Set E))

/-- The inclusion of the fibre into the total space. -/
def fibIncl (p : C(E, B)) (b : B) : C((⇑p ⁻¹' {b} : Set E), E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem fibIncl_apply (x : (⇑p ⁻¹' {b} : Set E)) : fibIncl p b x = ↑x := rfl

/-- The map `π_ n (p ⁻¹' {b}) e → π_ n E e` induced by the inclusion of the fibre. -/
def iStarFib (n : ℕ) : π_ n (⇑p ⁻¹' {b}) e → π_ n E ↑e :=
  RelHomotopyGroup.iStar n E (⇑p ⁻¹' {b}) e

/-- The map `π_ n E e → π_ n B b` induced by `p`. -/
def pStarAbs (n : ℕ) : π_ n E ↑e → π_ n B b :=
  pStar e n ∘ RelHomotopyGroup.jStar n E (⇑p ⁻¹' {b}) e

theorem iStarFib_eq_map (n : ℕ) :
    iStarFib e n
      = HomotopyGroup.map (N := Fin n) (x := e) (y := (e : E)) (fibIncl p b) rfl := by
  funext x
  induction x using Quotient.ind with
  | _ f => rfl

theorem pStarAbs_eq_map (n : ℕ) :
    pStarAbs e n = HomotopyGroup.map (N := Fin n) (x := (e : E)) (y := b) p e.2 := by
  funext x
  induction x using Quotient.ind with
  | _ f => rfl

/-! ### The three maps are pointed -/

theorem pStar_default (n : ℕ) : pStar e n default = default := by
  have h : pGenLoop e (default : RelGenLoop n E (⇑p ⁻¹' {b}) e) = (default : Ω^ (Fin n) B b) :=
    Subtype.ext (ContinuousMap.ext fun _ => e.2)
  exact congrArg (fun q : Ω^ (Fin n) B b => (⟦q⟧ : π_ n B b)) h

theorem iStarFib_default (n : ℕ) : iStarFib e n default = default :=
  (RelHomotopyGroup.iStar_isPointedMap n E (⇑p ⁻¹' {b}) e).map_default

theorem pStarAbs_default (n : ℕ) : pStarAbs e n default = default := by
  show pStar e n (RelHomotopyGroup.jStar n E (⇑p ⁻¹' {b}) e default) = default
  rw [(RelHomotopyGroup.jStar_isPointedMap n E (⇑p ⁻¹' {b}) e).map_default, pStar_default]

/-! ### The connecting map -/

/-- The bijection `pStar` of `bijective_pStar`, packaged as an equivalence. -/
def pStarEquiv (hp : IsSerreFibration p) (n : ℕ) :
    π_rel (n + 1) E (⇑p ⁻¹' {b}) e ≃ π_ (n + 1) B b :=
  Equiv.ofBijective _ (bijective_pStar e hp n)

@[simp]
theorem pStarEquiv_apply (hp : IsSerreFibration p) (n : ℕ)
    (x : π_rel (n + 1) E (⇑p ⁻¹' {b}) e) : pStarEquiv e hp n x = pStar e (n + 1) x := rfl

/-- The connecting map `∂ : π_(n+1)(B) → π_n(F)` of the long exact sequence of the fibration. -/
def fibDelta (hp : IsSerreFibration p) (n : ℕ) :
    π_ (n + 1) B b → π_ n (⇑p ⁻¹' {b}) e :=
  RelHomotopyGroup.bd n E (⇑p ⁻¹' {b}) e ∘ (pStarEquiv e hp n).symm

theorem fibDelta_default (hp : IsSerreFibration p) (n : ℕ) : fibDelta e hp n default = default := by
  have h : (pStarEquiv e hp n).symm default = default :=
    (pStarEquiv e hp n).symm_apply_eq.2 (pStar_default e (n + 1)).symm
  show RelHomotopyGroup.bd n E (⇑p ⁻¹' {b}) e ((pStarEquiv e hp n).symm default) = default
  rw [h]
  exact (RelHomotopyGroup.bd_isPointedMap n E (⇑p ⁻¹' {b}) e).map_default

/-! ### Exactness -/

theorem preimage_default_pStar (hp : IsSerreFibration p) (n : ℕ) :
    pStar e (n + 1) ⁻¹' {default} = {default} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun h => injective_pStar e hp n ?_, fun h => h ▸ pStar_default e (n + 1)⟩
  rw [h, pStar_default]

/-- Exactness at `π_(n+1)(E)` of `π_(n+1)(F) → π_(n+1)(E) → π_(n+1)(B)`. -/
theorem isExactAt_iStarFib_pStarAbs (hp : IsSerreFibration p) (n : ℕ) :
    ExactSeq.IsExactAt (iStarFib e (n + 1)) (pStarAbs e (n + 1)) := by
  have h := RelHomotopyGroup.isExactAt_iStar_jStar n E (⇑p ⁻¹' {b}) e
  show pStarAbs e (n + 1) ⁻¹' {default} = Set.range (iStarFib e (n + 1))
  rw [show pStarAbs e (n + 1)
      = pStar e (n + 1) ∘ RelHomotopyGroup.jStar (n + 1) E (⇑p ⁻¹' {b}) e from rfl,
    Set.preimage_comp, preimage_default_pStar e hp n]
  exact h

/-- Exactness at `π_(n+1)(B)` of `π_(n+1)(E) → π_(n+1)(B) --∂--> π_n(F)`. -/
theorem isExactAt_pStarAbs_fibDelta (hp : IsSerreFibration p) (n : ℕ) :
    ExactSeq.IsExactAt (pStarAbs e (n + 1)) (fibDelta e hp n) := by
  have h := RelHomotopyGroup.isExactAt_jStar_bd n E (⇑p ⁻¹' {b}) e
  show fibDelta e hp n ⁻¹' {default} = Set.range (pStarAbs e (n + 1))
  rw [fibDelta, Set.preimage_comp]
  show (pStarEquiv e hp n).symm ⁻¹' (RelHomotopyGroup.bd n E (⇑p ⁻¹' {b}) e ⁻¹' {default}) = _
  rw [h, ← Equiv.image_eq_preimage_symm, ← Set.range_comp]
  rfl

/-- Exactness at `π_n(F)` of `π_(n+1)(B) --∂--> π_n(F) → π_n(E)`. -/
theorem isExactAt_fibDelta_iStarFib (hp : IsSerreFibration p) (n : ℕ) :
    ExactSeq.IsExactAt (fibDelta e hp n) (iStarFib e n) := by
  have h := RelHomotopyGroup.isExactAt_bd_iStar n E (⇑p ⁻¹' {b}) e
  show iStarFib e n ⁻¹' {default} = Set.range (fibDelta e hp n)
  rw [show iStarFib e n = RelHomotopyGroup.iStar n E (⇑p ⁻¹' {b}) e from rfl, h, fibDelta,
    Set.range_comp, (pStarEquiv e hp n).symm.range_eq_univ, Set.image_univ]

/-! ### The absolute maps are group homomorphisms -/

/-- `π_(k+1)(F) → π_(k+1)(E)`, as a group homomorphism. -/
def iStarFibHom (k : ℕ) : π_ (k + 1) (⇑p ⁻¹' {b}) e →* π_ (k + 1) E ↑e :=
  HomotopyGroup.mapHom (N := Fin (k + 1)) (x := e) (y := (e : E)) (fibIncl p b) rfl

@[simp]
theorem iStarFibHom_apply (k : ℕ) (x : π_ (k + 1) (⇑p ⁻¹' {b}) e) :
    iStarFibHom e k x = iStarFib e (k + 1) x := by
  rw [iStarFib_eq_map]
  rfl

/-- `π_(k+1)(E) → π_(k+1)(B)`, as a group homomorphism. -/
def pStarAbsHom (k : ℕ) : π_ (k + 1) E ↑e →* π_ (k + 1) B b :=
  HomotopyGroup.mapHom (N := Fin (k + 1)) (x := (e : E)) (y := b) p e.2

@[simp]
theorem pStarAbsHom_apply (k : ℕ) (x : π_ (k + 1) E ↑e) :
    pStarAbsHom e k x = pStarAbs e (k + 1) x := by
  rw [pStarAbs_eq_map]
  rfl

end LES

/-! ## Consequences -/

section Consequences

variable (e : (⇑p ⁻¹' {b} : Set E))

/-- In positive degrees the distinguished point of a homotopy group is its unit. -/
theorem default_eq_one {N : Type*} [DecidableEq N] [Nonempty N] {X : Type*} [TopologicalSpace X]
    (x : X) : (default : HomotopyGroup N X x) = 1 :=
  _root_.HomotopyGroup.one_def.symm

/-- If the fibre is weakly contractible in degrees `k` and `k+1`, then `p` induces a bijection
`π_(k+1)(E) → π_(k+1)(B)`. -/
theorem bijective_pStarAbs_of_subsingleton_fibre (hp : IsSerreFibration p) (k : ℕ)
    (h₁ : Subsingleton (π_ (k + 1) (⇑p ⁻¹' {b}) e))
    (h₂ : Subsingleton (π_ k (⇑p ⁻¹' {b}) e)) :
    Function.Bijective (pStarAbs e (k + 1)) := by
  have hker : ∀ a : π_ (k + 1) E ↑e, pStarAbs e (k + 1) a = default → a = default := by
    intro a ha
    have hmem : a ∈ pStarAbs e (k + 1) ⁻¹' {default} := ha
    rw [isExactAt_iStarFib_pStarAbs e hp k] at hmem
    obtain ⟨y, rfl⟩ := hmem
    rw [Subsingleton.elim y default, iStarFib_default]
  have key : Function.Injective (pStarAbsHom e k) := by
    refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    rw [← default_eq_one (N := Fin (k + 1)) (↑e : E)]
    refine hker a ?_
    rw [← pStarAbsHom_apply, ha, default_eq_one]
  refine ⟨fun a₁ a₂ h => key ?_, fun y => ?_⟩
  · simpa only [pStarAbsHom_apply] using h
  · have hmem : y ∈ Set.range (pStarAbs e (k + 1)) := by
      rw [← isExactAt_pStarAbs_fibDelta e hp k]
      show fibDelta e hp k y = default
      exact Subsingleton.elim _ _
    exact hmem

/-- If the total space is weakly contractible in degree `k`, the connecting map is surjective. -/
theorem surjective_fibDelta_of_subsingleton (hp : IsSerreFibration p) (k : ℕ)
    (h : Subsingleton (π_ k E ↑e)) : Function.Surjective (fibDelta e hp k) := by
  intro y
  have hmem : y ∈ Set.range (fibDelta e hp k) := by
    rw [← isExactAt_fibDelta_iStarFib e hp k]
    show iStarFib e k y = default
    exact Subsingleton.elim _ _
  exact hmem

/-- If the total space is weakly contractible in degree `k+1`, the connecting map has trivial
kernel. -/
theorem fibDelta_eq_default_iff (hp : IsSerreFibration p) (k : ℕ)
    (h : Subsingleton (π_ (k + 1) E ↑e)) (x : π_ (k + 1) B b) :
    fibDelta e hp k x = default ↔ x = default := by
  refine ⟨fun hx => ?_, fun hx => hx ▸ fibDelta_default e hp k⟩
  have hmem : x ∈ fibDelta e hp k ⁻¹' {default} := hx
  rw [isExactAt_pStarAbs_fibDelta e hp k] at hmem
  obtain ⟨y, rfl⟩ := hmem
  rw [Subsingleton.elim y default, pStarAbs_default]

/-- If the boundary map of the pair `(E, F)` is injective — which follows from the group structure
on `π_rel` in degrees `≥ 2` — and the total space is weakly contractible in degree `k`, then the
connecting map `∂ : π_(k+1)(B) → π_k(F)` is a bijection. -/
theorem bijective_fibDelta_of_injective_bd (hp : IsSerreFibration p) (k : ℕ)
    (h : Subsingleton (π_ k E ↑e))
    (hbd : Function.Injective (RelHomotopyGroup.bd k E (⇑p ⁻¹' {b}) e)) :
    Function.Bijective (fibDelta e hp k) :=
  ⟨hbd.comp (pStarEquiv e hp k).symm.injective, surjective_fibDelta_of_subsingleton e hp k h⟩

end Consequences

end Submission
