/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Binomial

/-!
# Binomial labels on supported rays

Let `n` be a nonzero allowed degree tangent to an integral character `μ`, and `w` a supported ray
with `n ∈ w`. The binomial label `exp(log(1 + c z^n) ∂_μ)` (`Mei.binomialLabel`) lies in the
completed ray subgroup of `w` (`Mei.binomialLabel_mem_completedRaySubgroup`) and in the tropical
vertex wall group of `w` and `μ` (`Mei.binomialLabel_mem_wallGroup`). Hence it is its own ray
factor on `w` (`Mei.rayFactor_binomialLabel_self`), and its ray factors on all other supported rays
are trivial (`Mei.rayFactor_binomialLabel_of_ne`): the ray presentation of a binomial function
wall has a single nontrivial wall. This is the case of one term of the splitting of function
walls into ray walls in Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1.1, arXiv:1411.1394v2.
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [AddCommMonoid Λ]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (μ : Λ →+ ℤ)
  {n : Γ} (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hμ : μ (ρ n) = 0) (c : R)
  {w : SupportedRay d} (hw : n ∈ w.rayDegrees)

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

include hw in
/-- The binomial label `exp(log(1 + c z^n) ∂_μ)` lies on every supported ray through `n`. -/
theorem binomialLabel_mem_completedRaySubgroup :
    binomialLabel d ρ μ hn hn0 hμ c ∈ d.completedRaySubgroup ℒ w := by
  rw [PositiveDegrees.mem_completedRaySubgroup_iff_logComponent]
  intro q hq
  by_contra hne
  have hq0 := (d.mem_monoid_and_ne_zero_of_logComponent_ne_zero ℒ hne).2
  apply hne
  -- The binomial is supported on the multiples `k n`, which lie on `w` for `k > 0`.
  rw [binomialLabel_def]
  refine logComponent_completedBCHExp_completedTropicalTangentField_completedLog_eq_zero d ρ μ
    (AddSubmonoid.closure {binomialExponent d ρ μ hn hμ})
    (1 + single ⟨_, AddSubmonoid.subset_closure rfl⟩ c) (by
      simp only [map_add, map_one, mapDomainRingHom_apply, mapDomain_single,
        AddSubmonoid.subtype_apply]) _ fun t ht => ?_
  obtain ⟨k, hk⟩ := AddSubmonoid.mem_closure_singleton.mp t.property
  rw [← hk, AddSubmonoidClass.coe_nsmul, coe_binomialExponent] at ht
  rcases k with _ | k
  · exact hq0 (by rw [← ht, zero_nsmul])
  · exact hq (ht ▸ w.succ_nsmul_mem_rayDegrees hw k)

include hw in
/-- The binomial label `exp(log(1 + c z^n) ∂_μ)` is a wall label of every supported ray through
`n`, with the normal `μ`. -/
theorem binomialLabel_mem_wallGroup : binomialLabel d ρ μ hn hn0 hμ c ∈ (H).wallGroup w μ := by
  rw [← d.rayFactor_eq_self ℒ (binomialLabel_mem_completedRaySubgroup d ρ μ hn hn0 hμ c hw),
    binomialLabel_def]
  exact rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup d ρ μ _ w

include hw in
/-- The binomial label is its own ray factor on every supported ray through `n`. -/
theorem rayFactor_binomialLabel_self :
    d.rayFactor ℒ (binomialLabel d ρ μ hn hn0 hμ c) w = binomialLabel d ρ μ hn hn0 hμ c :=
  d.rayFactor_eq_self ℒ (binomialLabel_mem_completedRaySubgroup d ρ μ hn hn0 hμ c hw)

include hw in
/-- The ray factors of the binomial label on the supported rays not through `n` are trivial. -/
theorem rayFactor_binomialLabel_of_ne [HasUniqueDiv Γ] {v : SupportedRay d} (hv : v ≠ w) :
    d.rayFactor ℒ (binomialLabel d ρ μ hn hn0 hμ c) v = 1 :=
  d.rayFactor_eq_one ℒ (binomialLabel_mem_completedRaySubgroup d ρ μ hn hn0 hμ c hw) hv.symm

end Mei
