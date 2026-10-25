/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.FinitelyGenerated
public import Mei.Geometry.Toric.Algebraic.Cone.Finiteness

/-!
# Positive degrees on lattice points of rational cones

A lattice-rational cone equipped with an integral functional strictly positive on
its nonzero lattice points defines `PositiveDegrees`. Gordan's lemma supplies
finite generation of the lattice-point monoid; positivity then supplies finite
degree cutoffs. No separate salience hypothesis is required.
-/

public section

namespace Mei.PositiveDegrees

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- The lattice points of a lattice-rational cone, graded by an integral
functional strictly positive away from zero. Finite cutoffs are consequences of
the hypotheses, rather than additional input. -/
def ofCone (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ) (δ : N →+ ℤ)
    (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) : PositiveDegrees N :=
  ofFG (σ.fg_comap_toAddSubmonoid hi hσ) δ hδ

/-- The allowed degrees are exactly the lattice points of the cone. -/
@[simp]
theorem ofCone_monoid (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (δ : N →+ ℤ) (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) :
    (ofCone hi hσ δ hδ).monoid = σ.toAddSubmonoid.comap i := by
  exact ofFG_monoid (σ.fg_comap_toAddSubmonoid hi hσ) δ hδ

/-- The cone construction retains the prescribed integral functional. -/
@[simp]
theorem ofCone_degree (hi : IsIntegralLattice i) (hσ : IsLatticeRational i σ)
    (δ : N →+ ℤ) (hδ : ∀ {n}, i n ∈ σ → n ≠ 0 → 0 < δ n) :
    (ofCone hi hσ δ hδ).degree = δ := by
  exact ofFG_degree (σ.fg_comap_toAddSubmonoid hi hσ) δ hδ

end Mei.PositiveDegrees
