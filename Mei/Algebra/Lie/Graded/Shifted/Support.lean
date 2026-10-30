/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Component
public import Mei.Algebra.Lie.Filtered.Map
public import Mei.LinearAlgebra.GradedModule.Shifted.Overlap
public import Mei.LinearAlgebra.GradedModule.Shifted.Quotient
public import Mei.LinearAlgebra.GradedModule.History.Basic
public import Mei.Algebra.PositiveDegrees.Word

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

Finite exponential actions also preserve translated supports for arbitrary
coefficient filtrations, even without a homogeneous quotient. The finite support
argument uses `PositiveDegrees.lie_mem_shiftedSubmodule` and
`Module.End.exp_apply_mem_of_forall_mem`. For inherited quotient gradings this
gives positive degree increments for whole-component histories, including
comparisons between any two segments and at most `k` nonzero changes at order
`k`. Nonzero shifts with zero spatial direction are counted.

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

namespace Mei

section Monoid

variable {Γ R L M : Type*} [AddCommMonoid Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]

namespace ModuleFiltration

variable (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F]

/-- Rational scalars on a coefficient quotient are induced from its scalar ring. -/
local instance quotientRatModuleSupport (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom _ (algebraMap ℚ R)

/-- Finite Lie exponentials preserve the image of every translated positive
support. The filtration need not respect the coefficient grading. -/
theorem truncatedExpLieAction_mem_map_shiftedSubmodule
    (k : ℕ) (x : d.truncatedLie ℒ k) (p : Γ) {a : F.quotient k}
    (ha : a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ) :
    F.truncatedExpLieAction d ℒ k x a ∈
      (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
  rw [truncatedExpLieAction_apply]
  apply Module.End.exp_apply_mem_of_forall_mem _
    ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩ _ ?_ ha
  intro b hb
  obtain ⟨y, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  obtain ⟨b, hb, rfl⟩ := hb
  rw [LieIdeal.mkQ_apply, truncatedLieAction_mk, Submodule.mkQ_apply,
    quotientLieAction_mk]
  exact Submodule.mem_map_of_mem (d.lie_mem_shiftedSubmodule ℒ ℳ p y hb)

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- BCH labels preserve and reflect every translated positive support in a
finite coefficient quotient. Inverse labels satisfy the same support condition. -/
@[simp↓]
theorem truncatedBCHAction_mem_map_shiftedSubmodule_iff
    (k : ℕ) (g : d.truncatedGroup ℒ k) (p : Γ) (a : F.quotient k) :
    F.truncatedBCHAction d ℒ k g a ∈
      (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ ↔
    a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
  have h (g : d.truncatedGroup ℒ k) {a : F.quotient k}
      (ha : a ∈ (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ) :
      F.truncatedBCHAction d ℒ k g a ∈
        (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ := by
    rw [truncatedBCHAction_apply]
    exact F.truncatedExpLieAction_mem_map_shiftedSubmodule d ℒ ℳ k _ p ha
  exact ⟨fun ha => by
    simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h g⁻¹ ha,
    fun ha => h g ha⟩

end ModuleFiltration

end Monoid

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

namespace ModuleFiltration

variable (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F]

/-- Every surviving quotient component of a homogeneous input has an allowed
degree increment. This uses the inherited quotient decomposition, with no
finiteness or freeness hypothesis on the homogeneous pieces. -/
theorem sub_mem_monoid_of_decompose_truncatedBCHAction_ne_zero
    (k : ℕ) (g : d.truncatedGroup ℒ k)
    (𝓝 : Γ → Submodule R (F.quotient k)) [DirectSum.Decomposition 𝓝]
    (h𝓝 : ∀ n, 𝓝 n = (ℳ n).map (F.submodule (k + 1)).mkQ)
    {p q : Γ} {a : F.quotient k}
    (ha : a ∈ 𝓝 p)
    (hq : DirectSum.decompose 𝓝 (F.truncatedBCHAction d ℒ k g a) q ≠ 0) :
    q - p ∈ d.monoid := by
  have hp : ℳ p ≤ shiftedSubmodule ℳ d.monoid p := by
    simpa using le_shiftedSubmodule ℳ d.monoid p (d.monoid.zero_mem)
  have hs := (F.truncatedBCHAction_mem_map_shiftedSubmodule_iff d ℒ ℳ k g p a).mpr
    (Submodule.map_mono hp (by simpa only [h𝓝] using ha))
  have he : (shiftedSubmodule ℳ d.monoid p).map (F.submodule (k + 1)).mkQ =
      shiftedSubmodule 𝓝 d.monoid p := by
    simp only [shiftedSubmodule_def, Submodule.map_iSup, h𝓝]
  rw [he] at hs
  by_contra h
  exact hq (Subtype.val_injective
    ((mem_shiftedSubmodule_iff _ d.monoid p).mp hs q h))

end ModuleFiltration

end Mei

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DirectSum.Decomposition ℳ] (p : Γ)

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

/-- A surviving component of the actual finite shifted BCH action has an
allowed relative degree increment, for any label, including an inverse label. -/
theorem sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero
    (k : ℕ) (g : d.truncatedGroup ℒ k) {r s : Γ} {a : (F).quotient k}
    (ha : a ∈ (d.shiftedQuotientGrading ℳ p k).piece r)
    (hs : DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece
      ((F).truncatedBCHAction d ℒ k g a) s ≠ 0) :
    s - r ∈ d.monoid := by
  have := d.shiftedGrading_gradedBracket ℒ ℳ p
  exact (F).sub_mem_monoid_of_decompose_truncatedBCHAction_ne_zero
    (M := d.shiftedLieSubmodule ℒ ℳ p)
    d ℒ (shiftedGrading ℳ d.monoid p) k g ((d.shiftedQuotientGrading ℳ p k).piece)
      (d.shiftedQuotientGrading_piece ℳ p k) ha hs

/-- Every step of a surviving whole-component history of actual finite BCH
actions changes degree by an element of the positive monoid. Identity encounters
are retained; no spatial projection is used. -/
theorem homogeneousHistory_shiftedBCHAction_sub_mem_monoid
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0) (j : Fin n) :
    r j - Fin.snoc (α := fun _ => Γ) r r₀ j.succ ∈ d.monoid := by
  exact homogeneousHistory_rel_of_ne_zero (d.shiftedQuotientGrading ℳ p k).piece _
    (fun j _ _ _ ha hq =>
      d.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero ℒ ℳ p k (g j) ha hq)
    r r₀ a hne j

/-- Reading a surviving history backwards, any earlier degree differs from
any later degree by an allowed increment. The comparison includes the incoming
segment and supplies decreasing-degree itineraries without an extra hypothesis. -/
theorem homogeneousHistory_shiftedBCHAction_sub_mem_monoid_of_le
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Fin.snoc (α := fun _ => Γ) r r₀ i - Fin.snoc (α := fun _ => Γ) r r₀ j ∈
      d.monoid := by
  induction j using Fin.inductionOn with
  | zero =>
    have hi : i = 0 := le_antisymm hij (Fin.zero_le i)
    subst i
    simp
  | succ j ih =>
    by_cases he : i = j.succ
    · subst i
      simp
    · have hle : i ≤ j.castSucc := Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hij he)
      have hstep :=
        d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid ℒ ℳ p k g r r₀ a hne j
      simpa only [Fin.snoc_castSucc, sub_add_sub_cancel] using
        d.monoid.add_mem (ih hle) hstep

/-- A surviving history of finite shifted BCH actions has at most `k` nonzero
degree changes at order `k`. Unchanged-degree encounters are not counted, while
nonzero shifts with unchanged spatial velocity are counted. -/
theorem length_filter_bne_zero_homogeneousHistory_shiftedBCHAction_le
    (k : ℕ) {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
    (r : Fin n → Γ) (r₀ : Γ) (a : (d.shiftedQuotientGrading ℳ p k).piece r₀)
    (hne : homogeneousHistory (d.shiftedQuotientGrading ℳ p k).piece
      (fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap) r a ≠ 0) :
    ((List.ofFn fun j => r j - Fin.snoc (α := fun _ => Γ) r r₀ j.succ).filter
      (· != 0)).length ≤ k := by
  let T := fun j => ((F).truncatedBCHAction d ℒ k (g j)).toLinearMap
  let b := Fin.snoc (α := fun _ => Γ) r r₀
  have hcut (j : Fin (n + 1)) : b j ∈ d.cutoff k :=
    d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p
      (homogeneousHistoryStage_mem_snoc _ T r r₀ a j)
      (homogeneousHistoryStage_ne_zero _ T r hne j)
  apply d.length_filter_bne_zero_le
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid ℒ ℳ p k g r r₀ a hne j
  · have hsum : (List.ofFn fun j => r j - b j.succ).sum = b 0 - r₀ := by
      cases n with
      | zero => simp [b, Fin.snoc_zero]
      | succ m =>
        rw [Fin.sum_ofFn]
        have hIic : Finset.Iic (Fin.last m) = Finset.univ := Finset.Iic_top
        simpa only [hIic, neg_sub_neg, b,
          Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.snoc_apply_zero] using
          Fin.sum_Iic_sub (Fin.last m) (fun i => -b i)
    rw [hsum, map_sub]
    have hlast := d.degree_nonneg (d.mem_cutoff.mp (hcut (Fin.last n))).1
    have hfirst := (d.mem_cutoff.mp (hcut 0)).2
    simp only [b, Fin.snoc_last] at hlast
    omega

end Mei.PositiveDegrees
