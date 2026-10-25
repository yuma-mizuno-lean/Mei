/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
import TauCeti.Geometry.Convex.Cone.Alternative
import TauCeti.Algebra.Group.Submonoid.Finiteness

/-!
# Finite generation of lattice points in rational cones

The lattice points in a lattice-rational cone form a finitely generated additive
monoid, with no salience assumption. Integral characters separate a lattice point
outside the cone from the cone. Consequently membership is tested by the finitely
many generators of the dual semigroup, and Gordan's lemma applies to their
simultaneous integral inequalities.

The separation argument uses Tau Ceti's integral Tucker theorem
`exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos`. The finite-inequality
argument follows `IsLatticeRational.fg_dualSemigroup`, reusing that theorem and
`AddSubmonoid.FG.comap`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.2, Proposition 1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Proposition 1.2.17.
-/

public section

namespace Mei.Toric

open TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- An integral character separates a lattice point outside a lattice-rational cone:
it is nonnegative on the cone and strictly negative on the given lattice point. -/
theorem exists_mem_dualSemigroup_neg_of_not_mem (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) {n : N} (hn : i n ∉ σ) :
    ∃ m ∈ dualSemigroup hi σ, m n < 0 := by
  classical
  have := hi.free
  have := hi.finite
  obtain ⟨s, rfl⟩ := isLatticeRational_iff.mp hσ
  let v : Option s → N := Option.elim' (-n) fun a => a
  obtain ⟨c, m, hrel, hm, hpos⟩ :=
    TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos v
  have heq : ∑ a : s, c (some a) • (a : N) = c none • n := by
    apply Eq.symm
    simpa [v, Fintype.sum_option, neg_add_eq_zero] using hrel
  -- A positive coefficient of `-n` would put a positive multiple of `i n` in the cone.
  have hc : c none = 0 := by
    by_contra hne
    have hmem : (c none : ℝ) • i n ∈ PointedCone.hull ℝ (i '' (s : Set N)) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← heq, map_sum]
      exact Submodule.sum_mem _ fun a _ => by
        rw [map_nsmul]
        exact Submodule.smul_of_tower_mem _ _
          (PointedCone.subset_hull (Set.mem_image_of_mem i a.property))
    exact hn ((PointedCone.smul_mem_iff _
      (by exact_mod_cast Nat.pos_of_ne_zero hne)).mp hmem)
  refine ⟨m, (mem_dualSemigroup_hull_image hi _ m).mpr ?_, ?_⟩
  · intro a ha
    simpa [v] using hm (some ⟨a, ha⟩)
  · have := hpos none
    simpa [hc, v] using this

/-- Integral bipolarity at lattice points: membership in a lattice-rational cone
is equivalent to nonnegativity against every character of its dual semigroup. -/
theorem mem_iff_forall_dualSemigroup_nonneg (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) (n : N) :
    i n ∈ σ ↔ ∀ m ∈ dualSemigroup hi σ, 0 ≤ m n := by
  constructor
  · intro hn m hm
    have h := (mem_dualSemigroup hi m).mp hm hn
    simpa using h
  · intro hn
    by_contra hnot
    obtain ⟨m, hm, hneg⟩ := exists_mem_dualSemigroup_neg_of_not_mem hi hσ hnot
    exact (not_lt_of_ge (hn m hm)) hneg

/-- Finitely many integral characters nonnegative on a lattice-rational cone
test membership of all lattice points in that cone. -/
theorem exists_finset_dualSemigroup_mem_iff (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) :
    ∃ s : Finset (N →+ ℤ), (∀ m ∈ s, m ∈ dualSemigroup hi σ) ∧
      ∀ n, i n ∈ σ ↔ ∀ m ∈ s, 0 ≤ m n := by
  obtain ⟨s, hs⟩ := AddSubmonoid.isAddFG_iff.mp
    ((AddMonoid.fg_iff_addSubmonoid_fg _).mp (hσ.fg_dualSemigroup hi))
  refine ⟨s, fun m hm => hs ▸ AddSubmonoid.subset_closure hm, fun n => ?_⟩
  rw [mem_iff_forall_dualSemigroup_nonneg hi hσ]
  constructor
  · exact fun hn m hm => hn m (hs ▸ AddSubmonoid.subset_closure hm)
  · intro hn m hm
    rw [← hs] at hm
    induction hm using AddSubmonoid.closure_induction with
    | mem m hm => exact hn m hm
    | zero => simp
    | add a b ha hb iha ihb => simpa using add_nonneg iha ihb

end Mei.Toric

namespace PointedCone

open TauCeti.Toric

/-- **Gordan's lemma for lattice points.** The preimage of a lattice-rational
cone under an integral lattice map is a finitely generated additive submonoid.
The cone may contain lines. -/
theorem fg_comap_toAddSubmonoid {N V : Type*} [AddCommGroup N] [AddCommGroup V]
    [Module ℝ V] (σ : PointedCone ℝ V) {i : N →+ V} (hi : IsIntegralLattice i)
    (hσ : IsLatticeRational i σ) : (σ.toAddSubmonoid.comap i).FG := by
  classical
  have : AddMonoid.FG N := AddGroup.fg_iff_addMonoid_fg.mp
    (Module.Finite.iff_addGroup_fg.mp hi.finite)
  obtain ⟨s, _, hs⟩ := Mei.Toric.exists_finset_dualSemigroup_mem_iff hi hσ
  let ev : N →+ (s → ℤ) := AddMonoidHom.pi fun m => m.val
  let cast : (s → ℕ) →+ (s → ℤ) := (Nat.castAddMonoidHom ℤ).compLeft s
  have hfg : ((AddMonoidHom.mrange cast).comap ev).FG := by
    rw [AddMonoidHom.mrange_eq_map]
    exact ((AddMonoid.FG.fg_top (M := s → ℕ)).map cast).comap ev
  have heq : (AddMonoidHom.mrange cast).comap ev = σ.toAddSubmonoid.comap i := by
    ext n
    rw [AddSubmonoid.mem_comap, AddMonoidHom.mem_mrange, AddSubmonoid.mem_comap,
      Submodule.mem_toAddSubmonoid, hs]
    constructor
    · rintro ⟨a, ha⟩ m hm
      have h : (a ⟨m, hm⟩ : ℤ) = m n := congrFun ha ⟨m, hm⟩
      exact h ▸ Int.natCast_nonneg _
    · intro hn
      refine ⟨fun m => (m.val n).toNat, ?_⟩
      funext m
      exact Int.toNat_of_nonneg (hn m.val m.property)
  exact heq ▸ hfg

end PointedCone
