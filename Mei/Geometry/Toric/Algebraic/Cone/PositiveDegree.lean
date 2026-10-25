/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.LatticePoints
public import TauCeti.Geometry.Toric.Algebraic.Cone.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Positive integral functionals on rational cones

An integral character strictly positive on the nonzero lattice points of a
lattice-rational cone extends to a real functional strictly positive on every
nonzero point of that cone. Consequently the cone is salient. Positivity is
only required on lattice points; real positivity and salience are conclusions.

The extension is the existing `TauCeti.Toric.IsIntegralLattice.realCharacter`.
The proof uses finite lattice generation of the cone, without assuming finite
generation of its monoid of lattice points.
-/

public section

namespace TauCeti.Toric.IsLatticeRational

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Positivity of an integral character on nonzero lattice points of a rational
cone implies positivity of its real extension on every nonzero point of the cone. -/
theorem realCharacter_pos (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i)
    (δ : N →+ ℤ) (hδ : ∀ n ∈ σ.latticePoints i, n ≠ 0 → 0 < δ n)
    {x : V} (hx : x ∈ σ) (hx0 : x ≠ 0) : 0 < hi.realCharacter δ x := by
  obtain ⟨s, hs⟩ := isLatticeRational_iff.mp hσ
  have hgen : ∀ n ∈ s, i n ∈ σ := by
    intro n hn
    rw [hs]
    exact PointedCone.subset_hull ⟨n, hn, rfl⟩
  rw [hs] at hx
  have h : x = 0 ∨ 0 < hi.realCharacter δ x := by
    clear hx0
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, hn, rfl⟩ := hy
      by_cases hn0 : n = 0
      · simp [hn0]
      · right
        rw [hi.realCharacter_apply]
        exact_mod_cast hδ n (PointedCone.mem_latticePoints.mpr (hgen n hn)) hn0
    | zero => exact Or.inl rfl
    | add y z _ _ hy hz =>
      rcases hy with rfl | hy
      · simpa using hz
      rcases hz with rfl | hz
      · exact Or.inr (by simpa using hy)
      exact Or.inr (by simpa using add_pos hy hz)
    | smul a y _ hy =>
      rcases hy with rfl | hy
      · simp
      rcases a.property.eq_or_lt with ha | ha
      · have ha0 : a = 0 := Subtype.ext ha.symm
        simp [ha0]
      · right
        simpa only [map_smul, ← Nonneg.coe_smul, smul_eq_mul] using mul_pos ha hy
  exact h.resolve_left hx0

/-- A lattice-rational cone carrying an integral character strictly positive on
its nonzero lattice points is salient. No cutoff-finiteness assumption is needed. -/
theorem salient_of_degree_pos (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i)
    (δ : N →+ ℤ) (hδ : ∀ n ∈ σ.latticePoints i, n ≠ 0 → 0 < δ n) :
    (σ : ConvexCone ℝ V).Salient := by
  intro x hx hx0 hneg
  have hpos := hσ.realCharacter_pos hi δ hδ hx hx0
  have hnegpos := hσ.realCharacter_pos hi δ hδ hneg (neg_ne_zero.mpr hx0)
  simp only [map_neg] at hnegpos
  exact (not_lt_of_ge hpos.le) (neg_pos.mp hnegpos)

end TauCeti.Toric.IsLatticeRational
