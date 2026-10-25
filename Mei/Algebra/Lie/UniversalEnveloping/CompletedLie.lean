/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Completion
public import Mei.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import Mei.RingTheory.FilteredAlgebra.Algebra

/-!
# The canonical map into a completed enveloping algebra

For a positively graded Lie algebra, the canonical enveloping map descends at
every degree cutoff and extends to a Lie homomorphism from the compatible-family
Lie completion into the degree completion of its enveloping algebra. The finite
maps commute with transitions, and projections characterize the completed map.
This construction works over an arbitrary commutative ring, without a PBW or
freeness hypothesis; it does not assert injectivity.

The finite maps use `LieIdeal.liftQ` and Mathlib's quotient algebra maps. The Lie
completion retains `Mei.ModuleFiltration.completion` as its underlying module.
-/

public section

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N R L : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))
local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- The canonical Lie map sends the ideal above cutoff `k` into enveloping order `k + 1`. -/
theorem ι_mem_degreeFiltration_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) : ι R x ∈ (F).ideal (k + 1) := by
  have h : d.degreeSubmodule ℒ k ≤
      (((F).ideal (k + 1)).restrictScalars R).comap (ι R).toLinearMap := by
    rw [d.degreeSubmodule_def ℒ]
    refine iSup_le fun n x hx => ?_
    exact ι_mem_degreeFiltration ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn)) hx
      (by have := n.property; omega)
  have hx' : x ∈ (d.degreeIdeal ℒ k).toSubmodule := hx
  rw [d.degreeIdeal_toSubmodule ℒ k] at hx'
  exact h hx'

/-- The canonical Lie map at a finite degree cutoff. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (F).ideal (k + 1) :=
  (d.degreeIdeal ℒ k).liftQ
    ((Ideal.Quotient.mkₐ R ((F).ideal (k + 1))).toLieHom.comp (ι R)) (by
      intro x hx
      rw [LieHom.mem_ker, LieHom.comp_apply, AlgHom.toLieHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact ι_mem_degreeFiltration_of_mem_degreeIdeal d ℒ hx)

/-- The finite map sends the class of a Lie element to the class of its enveloping image. -/
@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    truncatedLieToU d ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((F).ideal (k + 1)) (ι R x) := by
  simp [truncatedLieToU]

/-- The finite canonical maps commute with lowering the degree cutoff. -/
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (x : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor ((F).antitone (Nat.add_le_add_right h 1))
        (truncatedLieToU d ℒ l x) =
      truncatedLieToU d ℒ k (d.truncationMap ℒ h x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ x
  simp only [truncatedLieToU_mk, Ideal.Quotient.factor_mk,
    LieIdeal.mkQ_apply, PositiveDegrees.truncationMap_mk]

/-- Extend the canonical Lie map to degree completions, computed in each finite quotient. -/
noncomputable def completedLieToU : d.completedLie ℒ →ₗ⁅R⁆ (F).completion where
  toFun x := ⟨fun k => truncatedLieToU d ℒ k.unop (π k.unop x),
    ((F).mem_completion_iff _).mpr (by
      intro k l h
      rw [factor_truncatedLieToU d ℒ h]
      rw [PositiveDegrees.truncationMap_def, LieIdeal.factor_completionProjection])⟩
  map_add' x y := by
    apply (F).completion_ext
    intro k
    simp only [Mei.AlgFiltration.projection_apply]
    exact map_add ((truncatedLieToU d ℒ k).comp (π k)) x y
  map_smul' r x := by
    apply (F).completion_ext
    intro k
    have hs (z : (F).completion) :
        (F).projection k (r • z) = r • (F).projection k z := by
      simpa only [Mei.AlgFiltration.projectionₐ_apply] using
        map_smul ((F).projectionₐ (R := R) k) r z
    rw [RingHom.id_apply, hs]
    simp only [Mei.AlgFiltration.projection_apply]
    exact map_smul ((truncatedLieToU d ℒ k).comp (π k)) r x
  map_lie' := by
    intro x y
    apply (F).completion_ext
    intro k
    rw [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul]
    simp only [Mei.AlgFiltration.projection_apply]
    exact ((truncatedLieToU d ℒ k).comp (π k)).map_lie x y

/-- Projection of the completed Lie map is the canonical map of finite quotients. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (x : d.completedLie ℒ) :
    (F).projection k (completedLieToU d ℒ x) = truncatedLieToU d ℒ k (π k x) := by
  rw [Mei.AlgFiltration.projection_apply, completedLieToU]
  rfl

/-- The completed map extends the original canonical enveloping map. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    completedLieToU d ℒ
        (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (F).toCompletion (ι R x) := by
  apply (F).completion_ext
  intro k
  rw [projection_completedLieToU, LieIdeal.completionProjection_toCompletion,
    LieIdeal.mkQ_apply, truncatedLieToU_mk, Mei.AlgFiltration.projection_toCompletion]

/-- Finite-order compatibility uniquely characterizes the completed canonical map. -/
theorem completedLieToU_unique (f : d.completedLie ℒ →ₗ⁅R⁆ (F).completion)
    (hf : ∀ k x, (F).projection k (f x) = truncatedLieToU d ℒ k (π k x)) :
    f = completedLieToU d ℒ := by
  apply LieHom.ext
  intro x
  exact (F).completion_ext fun k => (hf k x).trans (projection_completedLieToU d ℒ k x).symm

end Mei.UniversalEnvelopingAlgebra
