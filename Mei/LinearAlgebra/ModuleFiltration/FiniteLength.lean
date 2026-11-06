/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3, Codex
-/
module

public import Mei.LinearAlgebra.ModuleFiltration.Basic

/-!
# Finite-length filtrations

An endomorphism raising a module filtration by one sends every input into the
`n`-th filtration step after `n` applications (`pow_apply_mem` in
`ModuleFiltration/Basic`). When the filtration itself vanishes at a finite
order — the finite-length case — the endomorphism is globally nilpotent on the
whole module, not only on each finite quotient. Every nonzero element has a
last order of filtration membership below the vanishing order; these orders
can rank the surviving components of a propagation history. The nilpotence
bound is what the shared semimodule recursion needs; over rings this case
supplies the recursion's filtration-raising instances.
-/

public section

namespace Mei.ModuleFiltration

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (F : ModuleFiltration R M)

/-- A nonzero element of a finite-length filtration has a last order of
membership, strictly below the vanishing order. -/
theorem exists_mem_notMem_succ {r : ℕ} (hr : F.submodule r = ⊥)
    {x : M} (hx : x ≠ 0) :
    ∃ k < r, x ∈ F.submodule k ∧ x ∉ F.submodule (k + 1) := by
  classical
  have hex : ∃ k, x ∉ F.submodule (k + 1) := by
    refine ⟨r, fun h => hx ?_⟩
    exact (Submodule.mem_bot R).mp (hr ▸ F.antitone (Nat.le_succ r) h)
  let k := Nat.find hex
  have hnot : x ∉ F.submodule (k + 1) := Nat.find_spec hex
  have hmem : x ∈ F.submodule k := by
    by_cases hk : k = 0
    · simp [hk]
    · by_contra h
      have hle := Nat.find_min' hex (m := k - 1) (by
        simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)] using h)
      omega
  refine ⟨k, ?_, hmem, hnot⟩
  by_contra h
  exact hx ((Submodule.mem_bot R).mp (hr ▸ F.antitone (Nat.le_of_not_gt h) hmem))

variable (f : Module.End R M)
  (hf : ∀ k, F.submodule k ≤ (F.submodule (k + 1)).comap f)

include hf in
/-- A filtration that vanishes at order `r` makes a filtration-raising
endomorphism globally nilpotent: the `r`-th power vanishes on the whole
module, not only on a quotient. The finiteness is exactly the vanishing
hypothesis. -/
theorem pow_eq_zero_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥) :
    f ^ r = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  exact (Submodule.mem_bot R).mp (hr ▸ F.pow_apply_mem f hf r x)

include hf in
/-- A finite-length filtration makes a filtration-raising endomorphism
nilpotent on the original module. -/
theorem isNilpotent_of_submodule_eq_bot {r : ℕ} (hr : F.submodule r = ⊥) :
    IsNilpotent f :=
  ⟨r, F.pow_eq_zero_of_submodule_eq_bot f hf hr⟩

end Mei.ModuleFiltration
