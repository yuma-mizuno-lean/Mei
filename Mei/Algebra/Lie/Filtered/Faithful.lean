/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Exp
public import Mei.Algebra.Lie.Graded.Completion
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Filtration detection and faithful completed Lie actions

A filtered Lie action is detected by the filtration if every Lie element surviving
through order `k` acts nontrivially on some filtration term modulo order `b + k + 2`.
The test order `b` may depend on the element. Consequently individual finite-order
representations need not be faithful.

The compatible finite representations give a Lie representation on the module
completion. Filtration detection makes this completed representation injective.
Over rational scalars it also distinguishes completed Lie elements by their finite
exponential operators, providing the faithfulness criterion for exponential actions.
For coefficient algebras, the existing exponential automorphisms of the original
Lie algebra are therefore injective as a function of the Lie element.

The representation uses `ModuleFiltration.lift` and the existing truncated Lie
actions. Exponential detection uses the finite logarithm identity
`IsNilpotent.log_exp` from Tau Ceti.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei

variable {N R L M : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- A Lie element surviving through order `k` has a nonzero action on some
filtration term, visible modulo order `b + k + 2`. -/
class IsFiltrationDetected (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    (F : ModuleFiltration R M) : Prop where
  /-- Some coefficient detects each Lie element outside the specified degree tail. -/
  exists_lie_not_mem : ∀ {k : ℕ} {x : L}, x ∉ d.degreeSubmodule ℒ k →
    ∃ (b : ℕ) (m : M), m ∈ F.submodule b ∧ ⁅x, m⁆ ∉ F.submodule (b + k + 2)

namespace ModuleFiltration

variable (F : ModuleFiltration R M) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [LieModule R L M] [DecidableEq N] [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] [IsFiltrationRaising d ℒ F]

local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- The action of the degree-completed Lie algebra on the coefficient completion. -/
def completedLieAction : d.completedLie ℒ →ₗ⁅R⁆ Module.End R F.completion where
  toFun x := F.lift (fun k => (F.truncatedLieAction d ℒ k (π k x)).comp (F.projection k))
    (by
      intro k l h
      ext m
      simp only [LinearMap.comp_apply, transition_truncatedLieAction,
        transition_projection, PositiveDegrees.truncationMap_def,
        LieIdeal.factor_completionProjection])
  map_add' x y := by
    apply LinearMap.ext
    intro m
    apply completion_ext
    intro k
    simp [map_add]
  map_smul' r x := by
    apply LinearMap.ext
    intro m
    apply completion_ext
    intro k
    simp
  map_lie' {x y} := by
    apply LinearMap.ext
    intro m
    apply completion_ext
    intro k
    simp [LieRing.of_associative_ring_bracket, Module.End.mul_apply]

/-- The completed action is computed by the finite representation at every order. -/
@[simp]
theorem projection_completedLieAction (k : ℕ) (x : d.completedLie ℒ) (m : F.completion) :
    F.projection k (F.completedLieAction d ℒ x m) =
      F.truncatedLieAction d ℒ k (π k x) (F.projection k m) := by
  simp [completedLieAction]

variable [IsFiltrationDetected d ℒ F]

/-- Vanishing of all finite representations forces a completed Lie element to vanish.
The detecting coefficient may require a finer quotient than the Lie order being tested. -/
theorem eq_zero_of_truncatedLieAction_eq_zero (x : d.completedLie ℒ)
    (hx : ∀ k, F.truncatedLieAction d ℒ k (π k x) = 0) : x = 0 := by
  apply completion_ext
  intro k
  rw [← LieIdeal.completionProjection_apply, map_zero]
  by_contra hk
  obtain ⟨y, hy⟩ := (d.degreeIdeal ℒ (k + 1)).surjective_mkQ (π (k + 1) x)
  have hlow : (d.degreeIdeal ℒ k).mkQ y = π k x := by
    simpa only [LieIdeal.mkQ_apply, LieIdeal.factor_apply] using
      congrArg ((d.degreeIdeal ℒ (k + 1)).factor (d.degreeIdeal ℒ k)
        (d.degreeIdeal_antitone ℒ (Nat.le_succ k))) hy
      |>.trans (LieIdeal.factor_completionProjection _ _ (Nat.le_succ k) x)
  have hy_not : y ∉ d.degreeSubmodule ℒ k := by
    intro h
    have hz : (d.degreeIdeal ℒ k).mkQ y = 0 :=
      (d.degreeIdeal ℒ k).mkQ_eq_zero.mpr (by
        rw [← d.degreeIdeal_toSubmodule ℒ k] at h
        exact h)
    exact hk (by simpa only [map_zero] using hlow.symm.trans hz)
  obtain ⟨b, m, hm, hdet⟩ := IsFiltrationDetected.exists_lie_not_mem (F := F) hy_not
  -- Keep one extra Lie degree: the ambiguity in the lift then acts in the
  -- very filtration term excluded by the detection test.
  obtain ⟨z, hz⟩ := (d.degreeIdeal ℒ (b + k + 1)).surjective_mkQ (π (b + k + 1) x)
  have hzy : (d.degreeIdeal ℒ (k + 1)).mkQ z = (d.degreeIdeal ℒ (k + 1)).mkQ y := by
    rw [hy]
    simpa only [LieIdeal.mkQ_apply, LieIdeal.factor_apply] using
      congrArg ((d.degreeIdeal ℒ (b + k + 1)).factor (d.degreeIdeal ℒ (k + 1))
        (d.degreeIdeal_antitone ℒ (by omega))) hz
      |>.trans (LieIdeal.factor_completionProjection _ _ (by omega) x)
  have hdiff : z - y ∈ d.degreeSubmodule ℒ (k + 1) := by
    rw [← d.degreeIdeal_toSubmodule ℒ]
    exact (d.degreeIdeal ℒ (k + 1)).mkQ_eq_zero.mp (by simp [map_sub, hzy])
  have heq : ⁅z - y, m⁆ ∈ F.submodule (b + k + 2) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      IsFiltrationRaising.lie_mem (d := d) (ℒ := ℒ) (F := F) hdiff hm
  have hzero : ⁅z, m⁆ ∈ F.submodule (b + k + 2) := by
    have ha := LinearMap.congr_fun (hx (b + k + 1)) (Submodule.Quotient.mk m)
    rw [← hz, LieIdeal.mkQ_apply, truncatedLieAction_mk, quotientLieAction_mk,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at ha
    exact ha
  exact hdet (by simpa [sub_lie] using (F.submodule (b + k + 2)).sub_mem hzero heq)

/-- Filtration detection makes the Lie action on the completion faithful. -/
theorem completedLieAction_injective : Function.Injective (F.completedLieAction d ℒ) := by
  apply (injective_iff_map_eq_zero (F.completedLieAction d ℒ)).mpr
  intro x hx
  apply F.eq_zero_of_truncatedLieAction_eq_zero d ℒ x
  intro k
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := (F.submodule (k + 1)).mkQ_surjective q
  have h := congrArg (F.projection k)
    (LinearMap.congr_fun hx (F.of m))
  simpa only [projection_completedLieAction, projection_of, Submodule.mkQ_apply,
    LinearMap.zero_apply, map_zero] using h

section Rational

variable [Algebra ℚ R]

/-- Rational scalars on quotient endomorphisms are induced from the coefficient ring. -/
local instance ratAlgebraQuotientEnd (k : ℕ) : Algebra ℚ (Module.End R (F.quotient k)) :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- Equality of all finite exponential operators implies equality of the completed Lie
elements. This tests the actual nilpotent representations, without requiring any one of
them to be injective. -/
theorem eq_of_exp_truncatedLieAction_eq (x y : d.completedLie ℒ)
    (h : ∀ k, IsNilpotent.exp (F.truncatedLieAction d ℒ k (π k x)) =
      IsNilpotent.exp (F.truncatedLieAction d ℒ k (π k y))) : x = y := by
  apply sub_eq_zero.mp
  apply F.eq_zero_of_truncatedLieAction_eq_zero d ℒ (x - y)
  intro k
  have hk := congrArg IsNilpotent.log (h k)
  rw [IsNilpotent.log_exp ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k _⟩,
    IsNilpotent.log_exp ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k _⟩] at hk
  simp only [map_sub, hk, sub_self]

end Rational
end ModuleFiltration

namespace AlgFiltration

variable {A : Type*} [Ring A] [Algebra R A] [Algebra ℚ A]
  [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]
  [IsFiltrationDetected d ℒ (F.toModuleFiltration R)]

/-- Filtration detection makes the exponential action of the original Lie algebra
on the completed coefficient algebra injective. No separatedness of the coefficient
filtration or faithfulness of individual quotient representations is required. -/
theorem expAction_injective : Function.Injective (F.expAction d ℒ) := by
  intro x y hxy
  have hcoeff (k : ℕ) : F.quotientLieAction d ℒ k x = F.quotientLieAction d ℒ k y := by
    have he : IsNilpotent.exp (F.quotientLieAction d ℒ k x) =
        IsNilpotent.exp (F.quotientLieAction d ℒ k y) := by
      apply LinearMap.ext
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have h := congrArg (fun e => F.projection k (e (F.toCompletion a))) hxy
      simpa only [projection_expAction, projection_toCompletion,
        quotientExpLieAction_apply] using h
    let : Algebra ℚ (Module.End R (A ⧸ F.ideal (k + 1))) :=
      Algebra.ofModule smul_mul_assoc mul_smul_comm
    have h := congrArg IsNilpotent.log he
    simpa only [IsNilpotent.log_exp ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k x⟩,
      IsNilpotent.log_exp ⟨k + 1, F.quotientLieAction_pow_eq_zero d ℒ k y⟩] using h
  apply sub_eq_zero.mp
  have htail : x - y ∈ ⨅ n, Mei.DirectSum.degreeTail ℒ d.degree n := by
    apply (Submodule.mem_iInf _).mpr
    intro k
    have hmem : x - y ∈ d.degreeSubmodule ℒ k := by
      by_contra hx
      obtain ⟨b, a, ha, hdet⟩ := IsFiltrationDetected.exists_lie_not_mem
        (F := F.toModuleFiltration R) hx
      have hz : F.quotientLieAction d ℒ (b + k + 1) (x - y) = 0 := by
        simp only [map_sub, hcoeff, sub_self]
      have h := LinearMap.congr_fun hz (Ideal.Quotient.mk _ a)
      rw [quotientLieAction_mk, LinearMap.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at h
      exact hdet h
    exact Mei.DirectSum.degreeTail_antitone ℒ d.degree (Nat.le_succ k)
      ((d.degreeSubmodule_eq_degreeTail ℒ k) ▸ hmem)
  simpa only [Mei.DirectSum.iInf_degreeTail_eq_bot, Submodule.mem_bot] using htail

end AlgFiltration
end Mei
