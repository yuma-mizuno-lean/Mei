/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Component
public import Mei.Algebra.Lie.Filtered.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.Overlap

/-!
# Positive component shifts of BCH actions

A completed positive Lie action preserves every smaller translated coefficient
support. On a homogeneous input of degree `r`, every nonzero output component
has degree in `r + P`, and the degree-`r` component is exactly the input. Thus
a change of degree strictly increases relative order, including when a spatial
projection identifies the input and output degrees. These statements also hold
for components of the finite action of every truncated group label.

The support comparison uses `shiftedCompletedInclusion` and the naturality of
filtered BCH actions. The diagonal comparison uses the leading-component theorem
at the input's own origin, rather than requiring the input to have relative
order zero in the original shifted module. Labels are arbitrary, so the results
apply equally to inverse labels and signed wall products. Homogeneous pieces
need not be free or finite, and the positive monoid need not be saturated or
finitely generated.

For the interpretation as component propagation along broken lines, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Definition 2.10 and Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]

/-- Containment of translated supports intertwines the completed BCH actions,
including on arbitrary completed inputs. -/
theorem shiftedCompletedInclusion_completedBCHAction (r p : Γ)
    (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : d.ShiftedCoefficients ℳ r) :
    d.shiftedCompletedInclusion ℳ r p hrp
        ((d.shiftedLieFiltration ℒ ℳ r).completedBCHAction d ℒ g a) =
      (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
        (d.shiftedCompletedInclusion ℳ r p hrp a) := by
  let ψ : d.shiftedLieSubmodule ℒ ℳ r →ₗ[R] d.shiftedLieSubmodule ℒ ℳ p :=
    shiftedSupportInclusion ℳ d.monoid r p hrp
  have hψ (a : d.shiftedLieSubmodule ℒ ℳ r) : (ψ a : M) = a :=
    coe_shiftedSupportInclusion ℳ d.monoid r p hrp a
  have hequiv (x : L) (a : d.shiftedLieSubmodule ℒ ℳ r) :
      ψ ⁅x, a⁆ = ⁅(GradedLieHom.id (d := d) ℒ) x, ψ a⁆ := by
    apply Subtype.ext
    simp only [hψ, LieSubmodule.coe_bracket, GradedLieHom.id_apply]
  simpa only [shiftedCompletedInclusion_def, GradedLieHom.completedMap_id, MonoidHom.id_apply] using
    (d.shiftedLieFiltration ℒ ℳ r).completionMap_completedBCHAction_of_gradedLieHom
      (d.shiftedLieFiltration ℒ ℳ p) (GradedLieHom.id (d := d) ℒ)
      ψ id monotone_id
      (fun k => d.shiftedSupportInclusion_filtered ℳ r p hrp (k + 1)) hequiv g a

/-- The action preserves and reflects support in any contained translate.
This applies to arbitrary completed coefficients, not only homogeneous inputs. -/
theorem completedBCHAction_mem_range_shiftedCompletedInclusion_iff (r p : Γ)
    (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : d.ShiftedCoefficients ℳ p) :
    (d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g a ∈
        LinearMap.range (d.shiftedCompletedInclusion ℳ r p hrp) ↔
      a ∈ LinearMap.range (d.shiftedCompletedInclusion ℳ r p hrp) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(d.shiftedLieFiltration ℒ ℳ r).completedBCHAction d ℒ g⁻¹ b, ?_⟩
    rw [shiftedCompletedInclusion_completedBCHAction, hb]
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g) a
  · rintro ⟨b, rfl⟩
    exact ⟨(d.shiftedLieFiltration ℒ ℳ r).completedBCHAction d ℒ g b,
      d.shiftedCompletedInclusion_completedBCHAction ℒ ℳ r p hrp g b⟩

/-- If a coefficient has support in `r + P`, so does its image under any BCH label.
The ambient origin `p` may be strictly below `r`. -/
theorem shiftedHomogeneousComponent_completedBCHAction_eq_zero_of_support
    (r p : Γ) (hrp : r - p ∈ d.monoid) (g : d.completedBCHGroup ℒ)
    (a : d.ShiftedCoefficients ℳ p)
    (ha : ∀ q, q - r ∉ d.monoid → d.shiftedHomogeneousComponent ℳ p q a = 0)
    {q : Γ} (hq : q - r ∉ d.monoid) :
    d.shiftedHomogeneousComponent ℳ p q
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g a) = 0 := by
  apply (d.mem_range_shiftedCompletedInclusion_iff ℳ r p hrp _).mp _ q hq
  exact (d.completedBCHAction_mem_range_shiftedCompletedInclusion_iff ℒ ℳ r p hrp g a).mpr
    ((d.mem_range_shiftedCompletedInclusion_iff ℳ r p hrp a).mpr ha)

/-- A homogeneous input has no output component outside its positive translate,
regardless of its order relative to the ambient origin. -/
theorem shiftedHomogeneousComponent_completedBCHAction_of_mem_eq_zero
    (p : Γ) {r q : Γ} (hrp : r - p ∈ d.monoid)
    (g : d.completedBCHGroup ℒ) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r) (hq : q - r ∉ d.monoid) :
    d.shiftedHomogeneousComponent ℳ p q
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
        ((d.shiftedFiltration ℳ p).of a)) = 0 := by
  apply d.shiftedHomogeneousComponent_completedBCHAction_eq_zero_of_support ℒ ℳ r p hrp g
    ((d.shiftedFiltration ℳ p).of a) _ hq
  intro u hu
  rw [shiftedHomogeneousComponent_of]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne ℳ ha (by rintro rfl; simp at hu)

/-- The unchanged-degree component of a homogeneous input is exactly that input,
including when the input has positive relative order. -/
@[simp]
theorem shiftedHomogeneousComponent_completedBCHAction_of_mem_same
    (p : Γ) {r : Γ} (hrp : r - p ∈ d.monoid)
    (g : d.completedBCHGroup ℒ) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r) :
    d.shiftedHomogeneousComponent ℳ p r
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
        ((d.shiftedFiltration ℳ p).of a)) = ⟨a, ha⟩ := by
  let b : shiftedSubmodule ℳ d.monoid r := ⟨a, by
    exact le_shiftedSubmodule ℳ d.monoid r d.monoid.zero_mem (by simpa using ha)⟩
  have hb : shiftedSupportInclusion ℳ d.monoid r p hrp b = a := by
    apply Subtype.ext
    exact coe_shiftedSupportInclusion ℳ d.monoid r p hrp b
  conv_lhs => rw [← hb]
  rw [← shiftedCompletedInclusion_of,
    ← shiftedCompletedInclusion_completedBCHAction, shiftedHomogeneousComponent_inclusion,
    shiftedHomogeneousComponent_completedBCHAction, shiftedHomogeneousComponent_of]
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same ℳ ha

/-- Every surviving output shift belongs to the positive monoid. This holds for
both crossing signs since the label can be arbitrary or inverted. -/
theorem sub_mem_monoid_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero
    (p : Γ) {r q : Γ} (hrp : r - p ∈ d.monoid)
    (g : d.completedBCHGroup ℒ) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r)
    (hq : d.shiftedHomogeneousComponent ℳ p q
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
        ((d.shiftedFiltration ℳ p).of a)) ≠ 0) :
    q - r ∈ d.monoid := by
  by_contra h
  exact hq (d.shiftedHomogeneousComponent_completedBCHAction_of_mem_eq_zero ℒ ℳ p hrp g a ha h)

/-- A nonidentity degree change strictly raises relative order. No spatial
projection or nonzero spatial-direction assumption is involved. -/
theorem degree_lt_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero
    (p : Γ) {r q : Γ} (hrp : r - p ∈ d.monoid) (hrq : r ≠ q)
    (g : d.completedBCHGroup ℒ) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r)
    (hq : d.shiftedHomogeneousComponent ℳ p q
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g
        ((d.shiftedFiltration ℳ p).of a)) ≠ 0) :
    d.degree (r - p) < d.degree (q - p) := by
  have hm := d.sub_mem_monoid_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero
    ℒ ℳ p hrp g a ha hq
  have hd := d.degree_pos hm (sub_ne_zero.mpr hrq.symm)
  have he : d.degree (q - p) = d.degree (q - r) + d.degree (r - p) := by
    rw [← map_add, sub_add_sub_cancel]
  omega

/-- Under every finite BCH label, a surviving component of a homogeneous input
still has positive-monoid shift. In particular, truncation cannot introduce
spurious degree changes. -/
theorem sub_mem_monoid_of_shiftedQuotientComponent_truncatedBCHAction_ne_zero
    (p : Γ) {r q : Γ} (hrp : r - p ∈ d.monoid)
    (k : ℕ) (g : d.truncatedGroup ℒ k) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r) (hk : d.degree (q - p) ≤ k)
    (hq : d.shiftedQuotientComponent ℳ p q k hk
      ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        g (Submodule.Quotient.mk a)) ≠ 0) :
    q - r ∈ d.monoid := by
  obtain ⟨g, rfl⟩ := CompletedGroup.projection_surjective (d.groupTower ℒ)
    (fun n => d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE (Nat.le_succ n)).op) k g
  apply d.sub_mem_monoid_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero
    ℒ ℳ p hrp g a ha
  simpa only [d.shiftedHomogeneousComponent_eq ℳ p q k hk,
    ModuleFiltration.projection_completedBCHAction, ModuleFiltration.projection_of] using hq

/-- A surviving nonidentity component of the finite action strictly raises
relative order. The cutoff is relative to the original incoming origin `p`. -/
theorem degree_lt_of_shiftedQuotientComponent_truncatedBCHAction_ne_zero
    (p : Γ) {r q : Γ} (hrp : r - p ∈ d.monoid) (hrq : r ≠ q)
    (k : ℕ) (g : d.truncatedGroup ℒ k) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r) (hk : d.degree (q - p) ≤ k)
    (hq : d.shiftedQuotientComponent ℳ p q k hk
      ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        g (Submodule.Quotient.mk a)) ≠ 0) :
    d.degree (r - p) < d.degree (q - p) := by
  obtain ⟨g, rfl⟩ := CompletedGroup.projection_surjective (d.groupTower ℒ)
    (fun n => d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE (Nat.le_succ n)).op) k g
  apply d.degree_lt_of_shiftedHomogeneousComponent_completedBCHAction_ne_zero
    ℒ ℳ p hrp hrq g a ha
  simpa only [d.shiftedHomogeneousComponent_eq ℳ p q k hk,
    ModuleFiltration.projection_completedBCHAction, ModuleFiltration.projection_of] using hq

/-- The retained unchanged-degree component is the original homogeneous input,
even for inverse labels and inputs of positive relative order. -/
theorem shiftedQuotientComponent_truncatedBCHAction_of_mem_same
    (p : Γ) {r : Γ} (hrp : r - p ∈ d.monoid)
    (k : ℕ) (g : d.truncatedGroup ℒ k) (a : shiftedSubmodule ℳ d.monoid p)
    (ha : (a : M) ∈ ℳ r) (hk : d.degree (r - p) ≤ k) :
    d.shiftedQuotientComponent ℳ p r k hk
      ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k
        g (Submodule.Quotient.mk a)) = ⟨a, ha⟩ := by
  obtain ⟨g, rfl⟩ := CompletedGroup.projection_surjective (d.groupTower ℒ)
    (fun n => d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE (Nat.le_succ n)).op) k g
  simpa only [d.shiftedHomogeneousComponent_eq ℳ p r k hk,
    ModuleFiltration.projection_completedBCHAction, ModuleFiltration.projection_of] using
    d.shiftedHomogeneousComponent_completedBCHAction_of_mem_same ℒ ℳ p hrp g a ha

end Mei.PositiveDegrees
