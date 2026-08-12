/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# A concrete handle on the homology of a complex of abelian groups

Mathlib's `HomologicalComplex.homology` is defined through the abstract `ShortComplex` homology
API.  For the element chases needed by the universal coefficient theorem it is convenient to have
a *constructor* `Submission.homologyMk` producing the class of a cycle, together with the facts
that pin it down:

* every homology class is the class of a cycle (`Submission.homologyMk_surjective`);
* the class of a cycle vanishes iff the cycle is a boundary
  (`Submission.homologyMk_eq_zero_iff`);
* chain maps send classes to classes (`Submission.homologyMap_homologyMk`).

Everything is stated for `HomologicalComplex AddCommGrpCat.{0} c` and an arbitrary complex shape
`c`, so that it applies both to chain complexes and to the dual cochain complexes of
`Submission/Homology/UCT/Dual.lean`.
-/

open CategoryTheory Limits

noncomputable section

namespace Submission

variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex AddCommGrpCat.{0} c}

/-- The subgroup of `i`-cycles of a complex of abelian groups. -/
abbrev cyclesSub (K : HomologicalComplex AddCommGrpCat.{0} c) (i : ι) : AddSubgroup (K.X i) :=
  AddMonoidHom.ker ((K.sc i).g).hom

variable (K) in
/-- The homology class of a cycle, as an additive homomorphism defined on the cycles. -/
def homologyMkHom (i : ι) : cyclesSub K i →+ K.homology i :=
  ((K.sc i).abHomologyIso.inv).hom.comp
    (QuotientAddGroup.mk' (AddMonoidHom.range (K.sc i).abToCycles))

/-- The homology class of a cycle `x` of `K` in degree `i`. -/
def homologyMk {i : ι} (x : K.X i) (hx : K.d i (c.next i) x = 0) : K.homology i :=
  homologyMkHom K i ⟨x, hx⟩

variable {i : ι}

/-- The class constructed by `homologyMk` depends only on the underlying cycle, not on the proof
that it is a cycle. -/
theorem homologyMk_congr {x y : K.X i} (hx : K.d i (c.next i) x = 0)
    (hy : K.d i (c.next i) y = 0) (hxy : x = y) :
    homologyMk x hx = homologyMk y hy := by
  subst y
  rfl

theorem homologyMk_eq_homologyMkHom (z : cyclesSub K i) :
    homologyMk (z : K.X i) z.2 = homologyMkHom K i z := rfl

@[simp]
theorem homologyMk_zero : homologyMk (0 : K.X i) (map_zero _) = 0 :=
  map_zero (homologyMkHom K i)

theorem homologyMk_add (x y : K.X i) (hx : K.d i (c.next i) x = 0)
    (hy : K.d i (c.next i) y = 0) :
    homologyMk (x + y) (by rw [map_add, hx, hy, add_zero]) =
      homologyMk x hx + homologyMk y hy :=
  map_add (homologyMkHom K i) ⟨x, hx⟩ ⟨y, hy⟩

theorem homologyMk_neg (x : K.X i) (hx : K.d i (c.next i) x = 0) :
    homologyMk (-x) (by rw [map_neg, hx, neg_zero]) = -homologyMk x hx :=
  map_neg (homologyMkHom K i) ⟨x, hx⟩

theorem homologyMk_sub (x y : K.X i) (hx : K.d i (c.next i) x = 0)
    (hy : K.d i (c.next i) y = 0) :
    homologyMk (x - y) (by rw [map_sub, hx, hy, sub_zero]) =
      homologyMk x hx - homologyMk y hy :=
  map_sub (homologyMkHom K i) ⟨x, hx⟩ ⟨y, hy⟩

private theorem abHomologyIso_inv_injective (K : HomologicalComplex AddCommGrpCat.{0} c) (i : ι) :
    Function.Injective ⇑(K.sc i).abHomologyIso.inv := fun a b hab => by
  have h := congrArg (⇑(K.sc i).abHomologyIso.hom) hab
  rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply, ConcreteCategory.id_apply] at h

/-- Every homology class is the class of a cycle. -/
theorem homologyMk_surjective (z : K.homology i) :
    ∃ (x : K.X i) (hx : K.d i (c.next i) x = 0), homologyMk x hx = z := by
  obtain ⟨q, hq⟩ : ∃ q, (K.sc i).abHomologyIso.inv q = z :=
    ⟨(K.sc i).abHomologyIso.hom z, by
      rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨x, hx, hq⟩

/-- A cycle has trivial homology class exactly when it is a boundary. -/
theorem homologyMk_eq_zero_iff (x : K.X i) (hx : K.d i (c.next i) x = 0) :
    homologyMk x hx = 0 ↔ ∃ y : K.X (c.prev i), K.d (c.prev i) i y = x := by
  have hinj : Function.Injective ((K.sc i).abHomologyIso.inv).hom :=
    abHomologyIso_inv_injective K i
  refine (map_eq_zero_iff _ hinj).trans ((QuotientAddGroup.eq_zero_iff _).trans ?_)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- `homologyMk` transported through `ShortComplex.abHomologyIso` is the class in the explicit
quotient description of the homology. -/
theorem abHomologyIso_hom_homologyMk (x : K.X i) (hx : K.d i (c.next i) x = 0) :
    (K.sc i).abHomologyIso.hom (homologyMk x hx) =
      QuotientAddGroup.mk' (AddMonoidHom.range (K.sc i).abToCycles) ⟨x, hx⟩ := by
  have h := ConcreteCategory.congr_hom (K.sc i).abHomologyIso.inv_hom_id
    (QuotientAddGroup.mk' (AddMonoidHom.range (K.sc i).abToCycles) ⟨x, hx⟩)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  exact h

/-- `homologyMk` in terms of the projection `cycles ⟶ homology` of the `ShortComplex` API. -/
theorem homologyMk_eq_homologyπ (x : K.X i) (hx : K.d i (c.next i) x = 0) :
    homologyMk x hx = (K.sc i).homologyπ ((K.sc i).abCyclesIso.inv ⟨x, hx⟩) := by
  have h := ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.π_comp_homologyIso_inv (K.sc i) (K.sc i).abLeftHomologyData)
    (⟨x, hx⟩ : cyclesSub K i)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- Chain maps send the class of a cycle to the class of its image. -/
theorem homologyMap_homologyMk (f : K ⟶ L) (x : K.X i) (hx : K.d i (c.next i) x = 0)
    (hfx : L.d i (c.next i) (f.f i x) = 0) :
    HomologicalComplex.homologyMap f i (homologyMk x hx) = homologyMk (f.f i x) hfx := by
  have hinj : Function.Injective ⇑(L.sc i).iCycles :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hA : ShortComplex.cyclesMap
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} c i).map f)
      ((K.sc i).abCyclesIso.inv ⟨x, hx⟩) = (L.sc i).abCyclesIso.inv ⟨f.f i x, hfx⟩ := by
    apply hinj
    rw [ShortComplex.abCyclesIso_inv_apply_iCycles, ← ConcreteCategory.comp_apply,
      ShortComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
    rfl
  have hnat := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_naturality
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} c i).map f))
    ((K.sc i).abCyclesIso.inv ⟨x, hx⟩)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hA] at hnat
  rw [homologyMk_eq_homologyπ, homologyMk_eq_homologyπ]
  exact hnat

/-- A chain map sends the class of a cycle to the class of any equal target cycle. -/
theorem homologyMap_homologyMk_congr (f : K ⟶ L) (x : K.X i)
    (hx : K.d i (c.next i) x = 0) (y : L.X i) (hy : L.d i (c.next i) y = 0)
    (hxy : f.f i x = y) :
    HomologicalComplex.homologyMap f i (homologyMk x hx) = homologyMk y hy := by
  have hfx : L.d i (c.next i) (f.f i x) = 0 := by
    rw [hxy]
    exact hy
  exact (homologyMap_homologyMk f x hx hfx).trans (homologyMk_congr hfx hy hxy)

theorem homologyMkHom_surjective : Function.Surjective (homologyMkHom K i) := by
  intro z
  obtain ⟨x, hx, h⟩ := homologyMk_surjective z
  exact ⟨⟨x, hx⟩, h⟩

theorem ker_homologyMkHom :
    AddMonoidHom.ker (homologyMkHom K i) =
      (AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i) := by
  ext z
  exact homologyMk_eq_zero_iff (z : K.X i) z.2

/-- The homology of `K` in degree `i` is the quotient of the cycles by the boundaries. -/
def homologyQuotEquiv :
    (cyclesSub K i ⧸ (AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i))
      ≃+ K.homology i :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_homologyMkHom.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ homologyMkHom_surjective)

@[simp]
theorem homologyQuotEquiv_mk (z : cyclesSub K i) :
    homologyQuotEquiv
        (QuotientAddGroup.mk'
          ((AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i)) z) =
      homologyMk z.1 z.2 := by
  rfl

/-- Two maps out of `K.homology i` agree as soon as they agree on the classes of cycles. -/
theorem homology_hom_ext {A : AddCommGrpCat.{0}} {u v : K.homology i ⟶ A}
    (h : ∀ (x : K.X i) (hx : K.d i (c.next i) x = 0), u (homologyMk x hx) = v (homologyMk x hx)) :
    u = v := by
  ext z
  obtain ⟨x, hx, rfl⟩ := homologyMk_surjective z
  exact h x hx

/-- An additive map on one chain group which annihilates the incoming differential descends to
homology.  This is the concrete cycles-modulo-boundaries universal property, phrased directly in
terms of `HomologicalComplex.homology`. -/
noncomputable def homologyDescAddHom {A : AddCommGrpCat.{0}} (f : K.X i ⟶ A)
    (hf : K.d (c.prev i) i ≫ f = 0) : (K.homology i : Type) →+ (A : Type) :=
  (QuotientAddGroup.lift
      ((AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i))
      (f.hom.comp (AddSubgroup.subtype (cyclesSub K i))) (by
        rintro z ⟨y, hy⟩
        rw [AddMonoidHom.mem_ker]
        change f z.1 = 0
        change K.d (c.prev i) i y = z.1 at hy
        rw [← hy]
        rw [← ConcreteCategory.comp_apply, hf]
        simp)).comp
      (homologyQuotEquiv (K := K) (i := i)).symm.toAddMonoidHom

variable (K i) in
/-- Categorified form of `homologyDescAddHom`. -/
noncomputable def homologyDesc {A : AddCommGrpCat.{0}} (f : K.X i ⟶ A)
    (hf : K.d (c.prev i) i ≫ f = 0) : K.homology i ⟶ A :=
  AddCommGrpCat.ofHom (homologyDescAddHom f hf)

@[simp]
theorem homologyDesc_homologyMk {A : AddCommGrpCat.{0}} (f : K.X i ⟶ A)
    (hf : K.d (c.prev i) i ≫ f = 0) (x : K.X i)
    (hx : K.d i (c.next i) x = 0) :
    homologyDesc K i f hf (homologyMk x hx) = f x := by
  let B := (AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i)
  have hq :
      (homologyQuotEquiv (K := K) (i := i)).symm (homologyMk x hx) =
        QuotientAddGroup.mk' B ⟨x, hx⟩ := by
    apply (homologyQuotEquiv (K := K) (i := i)).injective
    rw [AddEquiv.apply_symm_apply]
    change homologyMk x hx =
      homologyQuotEquiv
        (QuotientAddGroup.mk'
          ((AddMonoidHom.range (K.d (c.prev i) i).hom).addSubgroupOf (cyclesSub K i))
          ⟨x, hx⟩)
    exact (homologyQuotEquiv_mk ⟨x, hx⟩).symm
  change homologyDescAddHom f hf (homologyMk x hx) = f x
  rw [homologyDescAddHom, AddMonoidHom.comp_apply]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rw [hq]
  rfl

end Submission
