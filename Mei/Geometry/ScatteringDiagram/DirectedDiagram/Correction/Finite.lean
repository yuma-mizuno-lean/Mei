/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Step
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Existence
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement

/-!
# Finite-order outgoing completions

A finitely active family of full affine hyperplanes admits a finite family of
outgoing corrections making it consistent through any prescribed order. The
initial indexed walls are retained literally, and every added wall has a pure
homogeneous logarithm of degree at most that order on its supported ray.
Each correction becomes active exactly at its homogeneous degree.
No finiteness assumption is imposed on the initial index set.

This result supplies finite stages for constructing an all-order outgoing
completion. It gives existence separately at each cutoff; compatibility between
the chosen stages requires additional data. For the underlying chamber and
correction constructions, see `DirectedDiagram.exists_chamber_trivialization`
and `DirectedDiagram.exists_consistent_outgoing_extension`.

The mathematical construction follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei.Convex

universe u v

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R L ι : Type*}
  [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ] [Module.Free ℤ Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- Full affine hyperplanes admit finitely many outgoing corrections consistent
through any prescribed cutoff. Every correction has a pure logarithm in an
actual degree of its supported ray and is active exactly from that degree
onward. The initial walls and their completed labels are retained exactly. -/
theorem exists_finite_outgoing_completion (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) (k : ℕ) :
    ∃ (κ : Type (max u v)) (_ : Fintype κ)
      (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      (∀ j, F.wall (.inl j) = D.wall j) ∧
      (∀ l ≤ k, F.LevelConsistent l) ∧
      ∀ a, (F.wall (.inr a)).Outgoing ∧
        ∃ n ∈ (F.wall (.inr a)).ray.rayDegrees, d.degree n ≤ k ∧
          (∃ z ∈ ℒ n, (F.wall (.inr a)).label = d.expToCompletion ℒ z) ∧
          ∀ l, Sum.inr a ∈ F.active l ↔ d.degree n ≤ l := by
  classical
  induction k with
  | zero =>
    let κ := PEmpty.{max u v + 1}
    let e : ι ⊕ κ ≃ ι := Equiv.sumEmpty ι κ
    let F : DirectedDiagram (d := d) h H (ι ⊕ κ) :=
      { wall := fun j => D.wall (e j)
        finite_active l := (D.finite_active l).preimage e.injective.injOn }
    refine ⟨κ, inferInstance, F, fun _ => rfl, ?_, fun a => a.elim⟩
    intro l hl
    have hl0 : l = 0 := by omega
    subst l
    apply (F.levelConsistent_def 0).mpr
    intro x y p q
    exact Subsingleton.elim _ _
  | succ k ih =>
    obtain ⟨κ, _, E, hE, hconsistent, hpure⟩ := ih
    have hk : E.LevelConsistent k := hconsistent k le_rfl
    -- Choose the geometric inputs afresh at the next cutoff of the current stage.
    obtain ⟨σ, hσ, cross, b, _, t, ht, τ, hτ, _⟩ :=
      E.exists_chamber_trivialization hk (fun _ => 1) (fun _ => zero_lt_one)
    have hfullE : ∀ j ∈ range (Sum.inl : ι → ι ⊕ κ), ∃ a : ℝ,
        (E.wall j).support = {v | h.realCharacter (E.wall j).normal v = a} := by
      rintro j ⟨j, rfl⟩
      simpa only [hE] using hfull j
    have hpureE : ∀ j ∉ range (Sum.inl : ι → ι ⊕ κ),
        ∃ n : Γ, d.degree n < k + 1 ∧
          ∃ a ∈ ℒ n, (E.wall j).label = d.expToCompletion ℒ a := by
      rintro (j | a) hj
      · exact (hj ⟨j, rfl⟩).elim
      · obtain ⟨_, n, _, hn, ⟨z, hz, he⟩, _⟩ := hpure a
        exact ⟨n, by omega, z, hz, he⟩
    obtain ⟨κ', _, G, hG, hnext, hprevious, hnew⟩ :=
      exists_consistent_outgoing_extension σ hσ cross hk b t ht τ hτ
        (range (Sum.inl : ι → ι ⊕ κ)) hfullE hpureE
    -- Reassociate indices without identifying any coincident wall occurrences.
    let e : ι ⊕ (κ ⊕ κ') ≃ (ι ⊕ κ) ⊕ κ' := (Equiv.sumAssoc ι κ κ').symm
    let F : DirectedDiagram (d := d) h H (ι ⊕ (κ ⊕ κ')) :=
      { wall := fun j => G.wall (e j)
        finite_active l := (G.finite_active l).preimage e.injective.injOn }
    have hFG : ∀ l, F.LevelEquivalent G l := fun l =>
      ((Refinement.ofEquiv e (fun _ => rfl)).levelEquivalent l).symm
    have hleft (j) : F.wall (.inl j) = D.wall j :=
      (hG (.inl j)).trans (hE j)
    have hold (a) : F.wall (.inr (.inl a)) = E.wall (.inr a) := hG (.inr a)
    have hright (a) : F.wall (.inr (.inr a)) = G.wall (.inr a) := rfl
    refine ⟨κ ⊕ κ', inferInstance, F, hleft, ?_, ?_⟩
    · intro l hl
      apply (hFG l).symm.consistent
      by_cases hlk : l ≤ k
      · exact (hprevious l hlk).symm.consistent (hconsistent l hlk)
      · have heq : l = k + 1 := by omega
        exact heq ▸ hnext
    · rintro (a | a)
      · rw [hold]
        obtain ⟨hout, n, hn, hnk, hz, hborn⟩ := hpure a
        refine ⟨hout, n, hn, by omega, hz, ?_⟩
        intro l
        simpa only [mem_active, hold] using hborn l
      · rw [hright]
        obtain ⟨hout, ⟨n, hn, hnk, z, hz, he⟩, hborn⟩ := hnew a
        refine ⟨hout, n, hn, by omega, ⟨z, hz, he⟩, ?_⟩
        intro l
        have hact : Sum.inr (.inr a) ∈ F.active l ↔ k + 1 ≤ l := by
          simpa only [mem_active, hright] using hborn l
        exact hact.trans (by omega)

end Mei.DirectedDiagram
