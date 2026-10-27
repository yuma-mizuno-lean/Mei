/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Completing a subspace of codimension two

Two successive vectors outside a subspace of codimension two span a complement.
This supplies complementary planes by avoiding a single hyperplane after the
first transverse vector is fixed. The dimension calculation uses Mathlib's
`Submodule.finrank_sup_span_singleton` and the dimension formula for a sum.
-/

public section

open Module

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Two vectors added successively outside a subspace of codimension two span
an actual complement to it. -/
theorem isCompl_span_pair_of_notMem (W : Submodule K V)
    (hdim : finrank K W + 2 = finrank K V) {v w : V}
    (hv : v ∉ W) (hw : w ∉ W ⊔ K ∙ v) :
    IsCompl W (span K {v, w}) := by
  classical
  have hd₁ := finrank_sup_span_singleton hv
  have hd₂ := finrank_sup_span_singleton hw
  have htop : (W ⊔ K ∙ v) ⊔ K ∙ w = ⊤ :=
    eq_top_of_finrank_eq (by omega)
  have hsup : W ⊔ span K {v, w} = ⊤ := by
    simpa only [span_insert, sup_assoc] using htop
  have hv₀ : v ≠ 0 := fun he => hv (he ▸ W.zero_mem)
  have hw' : w ∉ K ∙ v := fun he => hw (mem_sup_right he)
  have hd : finrank K (span K {v, w}) = 2 := by
    rw [span_insert, finrank_sup_span_singleton hw', finrank_span_singleton hv₀]
  have hinf := finrank_sup_add_finrank_inf_eq W (span K {v, w})
  rw [hsup, finrank_top] at hinf
  exact ⟨disjoint_iff.mpr (finrank_eq_zero.mp (by omega)), codisjoint_iff.mpr hsup⟩

end Submodule
