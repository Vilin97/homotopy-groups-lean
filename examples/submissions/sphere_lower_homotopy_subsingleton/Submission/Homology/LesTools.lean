/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Homology.Pair

/-!
# Tools for extracting information from the long exact sequence of a pair

Small lemmas that turn vanishing statements into isomorphisms, which is how every homology
computation in this development proceeds.
-/

open CategoryTheory Limits AlgebraicTopology

noncomputable section

namespace Submission

variable {A X : TopCat.{0}} (i : A ⟶ X) [Mono i]

/-- If `H_n(A) → H_n(X)` is epi then `H_n(X) → H_n(X,A)` vanishes. -/
theorem relJ_eq_zero_of_epi (n : ℕ) (h : Epi (relIota n i)) : relJ n i = 0 :=
  (pair_exact_iota_j n i).epi_f_iff.1 h

/-- If `H_n(A) → H_n(X)` is mono then the connecting map `H_{n+1}(X,A) → H_n(A)` vanishes. -/
theorem relδ_eq_zero_of_mono (n : ℕ) (h : Mono (relIota n i)) : relδ n i = 0 :=
  (pair_exact_δ_iota n i).mono_g_iff.1 h

/-- If `H_{n+1}(A) → H_{n+1}(X)` is epi and `H_n(A) → H_n(X)` is mono, the relative homology
`H_{n+1}(X, A)` vanishes. -/
theorem isZero_Hrel_of_epi_of_mono (n : ℕ) (he : Epi (relIota (n + 1) i))
    (hm : Mono (relIota n i)) : IsZero (Hrel (n + 1) i) := by
  have hmono : Mono (relδ n i) := (pair_exact_j_δ n i).mono_g (relJ_eq_zero_of_epi i (n + 1) he)
  have hz : relδ n i = 0 := relδ_eq_zero_of_mono i n hm
  refine (IsZero.iff_id_eq_zero _).2 (hmono.right_cancellation _ _ ?_)
  rw [hz, comp_zero, comp_zero]

/-- If `H_{n+1}(A) → H_{n+1}(X)` vanishes and `H_n(A) → H_n(X)` is mono, then
`H_{n+1}(X) → H_{n+1}(X,A)` is an isomorphism. -/
theorem isIso_relJ (n : ℕ) (h₁ : relIota (n + 1) i = 0) (hm : Mono (relIota n i)) :
    IsIso (relJ (n + 1) i) :=
  have : Mono (relJ (n + 1) i) := (pair_exact_iota_j (n + 1) i).mono_g h₁
  have : Epi (relJ (n + 1) i) := (pair_exact_j_δ n i).epi_f (relδ_eq_zero_of_mono i n hm)
  isIso_of_mono_of_epi _

/-- If `H_{n+1}(X)` and `H_n(X)` both vanish, the connecting map
`H_{n+1}(X,A) → H_n(A)` is an isomorphism. -/
theorem isIso_relδ (n : ℕ) (h₁ : IsZero (Hgrp (n + 1) X)) (h₂ : IsZero (Hgrp n X)) :
    IsIso (relδ n i) :=
  have : Mono (relδ n i) := (pair_exact_j_δ n i).mono_g (h₁.eq_zero_of_src _)
  have : Epi (relδ n i) := (pair_exact_δ_iota n i).epi_f (h₂.eq_zero_of_tgt _)
  isIso_of_mono_of_epi _

end Submission
