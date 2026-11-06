/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Degree blocks of truncated BCH actions

For a label `g` at coefficient order `k`, `labelBlock` is the coefficient of the
difference between its truncated BCH action and the identity, between two
retained relative degrees `m` and `n`. It transports a homogeneous coefficient
of ambient degree `p + m` through `shiftedInclusion`, applies that difference,
and reads the ambient degree `p + n` component.

The positive-shift facts of the associated graded show that `labelBlock`
vanishes outside `Precedes`: the unchanged component is fixed, and every other
surviving component requires an allowed positive degree difference. The degree
bookkeeping follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

universe u

variable {Γ : Type} {R : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup M] [Module R M]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ]

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

/-- The difference between a truncated BCH action and the identity annihilates
an included homogeneous coefficient when its relative degree does not strictly
precede the output degree. -/
private theorem component_sub_one_inclusion_eq_zero (k : ℕ) (g : d.truncatedGroup ℒ k)
    {n m : d.cutoff k} (hnm : ¬ d.Precedes m.val n.val) (x : ℳ (p + m.val)) :
    d.shiftedQuotientComponent ℳ p (p + n.val) k (degree_add_val_sub_self_le d p k n)
      ((((A).truncatedBCHAction d ℒ k g : Module.End R ((A).quotient k)) - 1)
        (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
          ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x))) = 0 := by
  have hnm' : ¬ (m.val ≠ n.val ∧ n.val - m.val ∈ d.monoid) :=
    fun h => hnm (d.precedes_iff.mpr h)
  rcases not_and_or.mp hnm' with hmn | hmon
  · obtain rfl : m = n := Subtype.ext (not_not.mp hmn)
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, sub_eq_zero]
    trans (⟨x, x.property⟩ : ℳ (p + m.val))
    · rw [LinearEquiv.coe_coe,
        d.shiftedQuotientComponent_truncatedBCHAction_of_mem_same ℒ ℳ p
        (r := p + m.val) (add_val_sub_self_mem d p k m) k g
        (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x)
        (by simpa only [coe_shiftedInclusion] using x.property)
        (degree_add_val_sub_self_le d p k m)]
      exact Subtype.ext (by simp only [coe_shiftedInclusion])
    · rw [d.shiftedQuotientComponent_mk, coe_shiftedInclusion]
      exact Subtype.ext (DirectSum.decompose_of_mem_same ℳ x.property).symm
  · have hc : p + m.val ≠ p + n.val := by
      intro he
      apply hmon
      have h0 : n.val - m.val = 0 := by
        rw [← add_sub_add_left_eq_sub, he, sub_self]
      rw [h0]
      exact d.monoid.zero_mem
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub,
      d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne (q := p + n.val) (k := k)
        (h := degree_add_val_sub_self_le d p k n)
        (n := ⟨m.val, (d.mem_cutoff.mp m.property).1⟩) (hnq := hc) (x := x), sub_zero]
    by_contra hne
    apply hmon
    have hsub := d.sub_mem_monoid_of_shiftedQuotientComponent_truncatedBCHAction_ne_zero
      (ℒ := ℒ) (ℳ := ℳ) (p := p) (r := p + m.val) (q := p + n.val)
      (add_val_sub_self_mem d p k m) k g
      (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x)
      (by simpa only [coe_shiftedInclusion] using x.property)
      (degree_add_val_sub_self_le d p k n) hne
    rwa [add_sub_add_left_eq_sub] at hsub

/-- The coefficient of the difference between a truncated BCH action and the
identity, between two retained relative degrees. -/
def labelBlock (k : ℕ) (g : d.truncatedGroup ℒ k) (n m : d.cutoff k) :
    ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  (d.shiftedQuotientComponent ℳ p (p + n.val) k (degree_add_val_sub_self_le d p k n)).comp
    ((((A).truncatedBCHAction d ℒ k g : Module.End R ((A).quotient k)) - 1).comp
      (Submodule.mkQ ((A).submodule (k + 1)) |>.comp
        (shiftedInclusion ℳ d.monoid p ⟨m.val, (d.mem_cutoff.mp m.property).1⟩)))

/-- Evaluation of a label block on a homogeneous coefficient. -/
theorem labelBlock_apply (k : ℕ) (g : d.truncatedGroup ℒ k) (n m : d.cutoff k)
    (x : ℳ (p + m.val)) :
    labelBlock d ℳ p ℒ k g n m x =
      d.shiftedQuotientComponent ℳ p (p + n.val) k (degree_add_val_sub_self_le d p k n)
        ((((A).truncatedBCHAction d ℒ k g : Module.End R ((A).quotient k)) - 1)
          (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
            ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x))) := by
  simp only [labelBlock, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- Between distinct relative degrees, a label block is the component of the
truncated BCH action itself: the subtracted identity has no such component. -/
theorem labelBlock_apply_of_ne (k : ℕ) (g : d.truncatedGroup ℒ k)
    (n m : d.cutoff k) (hmn : m.val ≠ n.val) (x : ℳ (p + m.val)) :
    labelBlock d ℳ p ℒ k g n m x =
      d.shiftedQuotientComponent ℳ p (p + n.val) k (degree_add_val_sub_self_le d p k n)
        ((A).truncatedBCHAction d ℒ k g
          (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p
            ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ x))) := by
  simp [labelBlock_apply,
    d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne ℳ p
      (p + n.val) k _ ⟨m.val, (d.mem_cutoff.mp m.property).1⟩
      (fun he => hmn (add_left_cancel he))]

/-- A block outside the strict relative-degree relation vanishes. -/
theorem labelBlock_eq_zero_of_not_precedes (k : ℕ) (g : d.truncatedGroup ℒ k)
    {n m : d.cutoff k} (hnm : ¬ d.Precedes m.val n.val) :
    labelBlock d ℳ p ℒ k g n m = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [labelBlock_apply]
  exact component_sub_one_inclusion_eq_zero d ℳ p ℒ k g hnm x

/-- Between distinct relative degrees, the block acts on the component of an
arbitrary quotient coefficient by projecting its homogeneous input, applying
the BCH action, and reading the output component. The identity term vanishes. -/
theorem labelBlock_apply_component_of_ne (k : ℕ) (g : d.truncatedGroup ℒ k)
    (n m : d.cutoff k) (hmn : m.val ≠ n.val) (x : (A).quotient k) :
    labelBlock d ℳ p ℒ k g n m
        (d.shiftedQuotientComponent ℳ p (p + m.val) k
          (degree_add_val_sub_self_le d p k m) x) =
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (degree_add_val_sub_self_le d p k n)
        ((A).truncatedBCHAction d ℒ k g
          (DirectSum.decompose (d.shiftedQuotientGrading ℳ p k).piece x m.val)) := by
  rw [labelBlock_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    d.shiftedQuotientComponent_mk_shiftedInclusion_of_ne ℳ p
      (p + n.val) k _ _ (fun he => hmn (add_left_cancel he)), sub_zero,
    d.decompose_shiftedQuotientGrading ℳ p k
      ⟨m.val, (d.mem_cutoff.mp m.property).1⟩ (d.mem_cutoff.mp m.property).2]
  -- The subtype index has value `m.val`; the coerced endomorphism and the
  -- linear equivalence apply the same underlying BCH action.
  rfl

/-- A retained coefficient block is independent of enlarging the cutoff, provided
its label is truncated along the same quotient tower. -/
theorem labelBlock_truncation {k l : ℕ} (hkl : k ≤ l)
    (g : d.truncatedGroup ℒ l) (n m : d.cutoff k) :
    labelBlock d ℳ p ℒ k ((d.truncationMap ℒ hkl).bchGroupMap g) n m =
      labelBlock d ℳ p ℒ l g
        ⟨n.val, d.cutoff_mono hkl n.property⟩
        ⟨m.val, d.cutoff_mono hkl m.property⟩ := by
  apply LinearMap.ext
  intro x
  simp only [labelBlock_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearEquiv.coe_coe]
  rw [← (A).transition_mk hkl, ← (A).transition_truncatedBCHAction d ℒ hkl,
    d.shiftedQuotientComponent_transition]
  rw [d.shiftedQuotientComponent_transition]

end Mei.PositiveDegrees
