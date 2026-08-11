{-# OPTIONS --lossy-unification #-}

-- Copyright (c) 2026 Vasily Ilin.
-- Released under Apache 2.0; see the repository LICENSE.
--
-- A small, source-auditable Cubical Agda companion to the Lean development.
-- It is checked against agda/cubical commit
-- 92166033326aa59800a580b428125f3c654b5e45.
module SecondBatch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Hopf
open S¹Hopf
open import Cubical.Homotopy.HopfInvariant.HopfMap
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.SuspensionMap
open import Cubical.Homotopy.Group.LES
import Cubical.Homotopy.Group.PinSn as PinSn
open import Cubical.Homotopy.Group.Pi3S2 as Pi3S2
import Cubical.Homotopy.Group.Pi4S3.Summary as Pi4S3

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Exact

open Iso

private
  S¹-hLevel : (n : ℕ) → isOfHLevel (3 + n) S¹
  S¹-hLevel zero = isGroupoidS¹
  S¹-hLevel (suc n) = isOfHLevelSuc (3 + n) (S¹-hLevel n)

  isContr-π≥3-S¹ : (n : ℕ) → isContr (π (3 + n) (S₊∙ 1))
  fst (isContr-π≥3-S¹ n) = ∣ refl ∣₂
  snd (isContr-π≥3-S¹ n) =
    ST.elim (λ _ → isSetPathImplicit)
      (λ p → cong ∣_∣₂
        (isContr→isProp
          (hLevΩ+ 0 (3 + n)
            (subst (λ k → isOfHLevel k S¹) (sym (+-zero (3 + n))) (S¹-hLevel n)))
          refl p))

private
  firstStemSuspMap : (n : ℕ)
    → (S₊∙ (4 + n) →∙ S₊∙ (3 + n))
    → (S₊∙ (5 + n) →∙ S₊∙ (4 + n))
  firstStemSuspMap n = suspMap {A = S₊∙ (3 + n)} (3 + n)

  is2ConnectedFirstStemSuspMap : (n : ℕ)
    → isConnectedFun 2 (firstStemSuspMap n)
  is2ConnectedFirstStemSuspMap n =
    isConnectedFunSubtr 2 n _
      (subst (λ x → isConnectedFun x (firstStemSuspMap n))
        (+∸ (2 + n) (suc (2 + n)) ∙ +-comm 2 n)
        (isConnectedSuspMap (suc (2 + n)) (2 + n)))

{- Suspension is an isomorphism along the first stable stem, starting at
π₄(S³) → π₅(S⁴). -}
firstStemSuspIso : (n : ℕ)
  → GroupIso ( π'Gr (3 + n) (S₊∙ (3 + n)))
             ( π'Gr (4 + n) (S₊∙ (4 + n)))
firstStemSuspIso n =
  (compIso setTruncTrunc2Iso
    (compIso
      (connectedTruncIso 2 (firstStemSuspMap n)
        (is2ConnectedFirstStemSuspMap n))
      (invIso setTruncTrunc2Iso)))
  , makeIsGroupHom
      (ST.elim2 (λ _ _ → isSetPathImplicit)
        λ f g → IsGroupHom.pres· (suspMapπ'Hom (3 + n) .snd) ∣ f ∣₂ ∣ g ∣₂)

{- In every degree at least three, projection in the Hopf fibration is
an equivalence on homotopy groups. -}
hopfTotalToBase : (n : ℕ) → GroupEquiv
  (πGr (2 + n) (Σ (S₊ 2) S¹Hopf , north , base))
  (πGr (2 + n) (S₊∙ 2))
hopfTotalToBase zero = Pi3S2.π₃S²≅π₃TotalHopf
fst (fst (hopfTotalToBase (suc n))) = fst (πLES.A→B TotalHopf→∙S² (3 + n))
snd (fst (hopfTotalToBase (suc n))) =
  SES→isEquiv
    (isContr→≡UnitGroup
      (subst isContr (cong (π (4 + n)) (sym IsoFiberTotalHopfS¹∙≡))
        (isContr-π≥3-S¹ (suc n))))
    (isContr→≡UnitGroup
      (subst isContr (cong (π (3 + n)) (sym IsoFiberTotalHopfS¹∙≡))
        (isContr-π≥3-S¹ n)))
    (πLES.fib→A TotalHopf→∙S² (3 + n))
    (πLES.A→B TotalHopf→∙S² (3 + n))
    (πLES.B→fib TotalHopf→∙S² (2 + n))
    (πLES.Ker-A→B⊂Im-fib→A TotalHopf→∙S² (3 + n))
    (πLES.Ker-B→fib⊂Im-A→B TotalHopf→∙S² (2 + n))
snd (hopfTotalToBase (suc n)) = snd (πLES.A→B TotalHopf→∙S² (3 + n))

{- Hence πₘ(S³) ≅ πₘ(S²) for every m ≥ 3.  The parameter is m - 3. -}
πS³≃πS² : (n : ℕ) → GroupEquiv
  (π'Gr (2 + n) (S₊∙ 3))
  (π'Gr (2 + n) (S₊∙ 2))
πS³≃πS² n =
  compGroupEquiv
    (Pi3S2.πS³≅πTotalHopf (2 + n))
    (compGroupEquiv
      (GroupIso→GroupEquiv (π'Gr≅πGr (2 + n) _))
      (compGroupEquiv
        (hopfTotalToBase n)
        (GroupIso→GroupEquiv (invGroupIso (π'Gr≅πGr (2 + n) _)))))

{- The fourth homotopy group of the 2-sphere is cyclic of order two. -}
π₄S²≃ℤ/2ℤ : GroupEquiv (π'Gr 3 (S₊∙ 2)) (ℤGroup/ 2)
π₄S²≃ℤ/2ℤ =
  compGroupEquiv
    (invGroupEquiv (πS³≃πS² 1))
    Pi4S3.π₄S³≃ℤ/2ℤ

{- The complete first stable stem: πₙ₊₁(Sⁿ) ≅ ℤ/2 for every n ≥ 3.
The natural-number parameter is the offset from the base case n = 3. -}
firstStableStem : (n : ℕ)
  → GroupEquiv (π'Gr (3 + n) (S₊∙ (3 + n))) (ℤGroup/ 2)
firstStableStem zero = Pi4S3.π₄S³≃ℤ/2ℤ
firstStableStem (suc n) =
  compGroupEquiv
    (invGroupEquiv (GroupIso→GroupEquiv (firstStemSuspIso n)))
    (firstStableStem n)
