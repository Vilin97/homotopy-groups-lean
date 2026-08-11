/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Vendored from https://github.com/joelriou/excision (Apache 2.0), commit 1a9f442.
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# ...

-/

@[expose] public section

public section

namespace Fin

variable {T : Type*}

lemma exists_vecCons₁ (f : Fin 1 → T) : ∃ (t : T), f = ![t] :=
  ⟨f 0, by ext i; fin_cases i; rfl⟩

lemma exists_vecCons₂ (f : Fin 2 → T) : ∃ (t₀ t₁ : T), f = ![t₀, t₁] :=
  ⟨f 0, f 1, by ext i; fin_cases i <;> rfl⟩

lemma exists_vecCons₃ (f : Fin 3 → T) : ∃ (t₀ t₁ t₂ : T), f = ![t₀, t₁, t₂] :=
  ⟨f 0, f 1, f 2, by ext i; fin_cases i <;> rfl⟩

end Fin
