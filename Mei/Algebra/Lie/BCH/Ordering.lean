/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Filtration
public import Mei.Algebra.BigOperators.Group.List.Exchange

/-!
# Ordering finite products in completed BCH groups

Let `g : F → Ĝ` assign to each factor an element of the completed BCH group of a positively
graded Lie algebra lying in the degree filtration term of order `deg x`. At order `k`,
factors with `deg x > k` project to `1`, and two factors with `deg x + deg y > k` commute
by `commutator_degreeFiltration_le`. So when ordering a finite product at order `k`, only
the bad adjacent pairs with `deg x + deg y ≤ k` need an exchange
`x y = y M x`, and the inserted factors must have larger degree than both.
`PositiveDegrees.exists_isChain_projection_prod_eq_of_exchange` then gives an ordered product
with the same projection, by `List.exists_isChain_prod_map_eq_of_exchange`.

For products of dilogarithm elements `Ψ[n]^c`, with `deg` the degree of `n`, this gives the
termination of Nakanishi's Ordering Algorithm at each finite order once the exchanges of
anti-ordered pairs are supplied, for example by the pentagon relation (Nakanishi, *Cluster
algebras and scattering diagrams, Part III*, §5.2, arXiv:2111.00800v6). Anti-ordered pairs
whose total degree exceeds the order need no exchange.
-/

public section

open scoped commutatorElement

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- **Ordering at finite order.** Let each factor `x` lie in the degree filtration of order
`deg x`, and let `bad` be asymmetric. If every bad adjacent pair `x y` with
`deg x + deg y ≤ k` can be exchanged at order `k` as `x y = y M x`, where the factors of
`M` have degree larger than both `deg x` and `deg y`, then every finite product agrees at
order `k` with a product of factors of degree at most `k` with no bad adjacent pair. -/
theorem exists_isChain_projection_prod_eq_of_exchange {F : Type*} (l : List F)
    (g : F → d.completedBCHGroup ℒ) (deg : F → ℕ) (bad : F → F → Prop) (k : ℕ)
    (hg : ∀ x, g x ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (deg x))
    (hbad : ∀ x y, bad x y → ¬ bad y x)
    (hex : ∀ x y, bad x y → deg x + deg y ≤ k → ∃ M : List F,
      (∀ m ∈ M, deg x < deg m ∧ deg y < deg m) ∧
        CompletedGroup.projection k (g x * g y) =
          CompletedGroup.projection k (g y * (M.map g).prod * g x)) :
    ∃ l' : List F, l'.IsChain (fun x y => ¬ bad x y) ∧ (∀ x ∈ l', deg x ≤ k) ∧
      CompletedGroup.projection k (l'.map g).prod =
        CompletedGroup.projection k (l.map g).prod := by
  -- Elements of filtration order above `k` project to `1` at order `k`.
  have hone {a : ℕ} (ha : k < a) {u : d.completedBCHGroup ℒ}
      (hu : u ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) a) :
      CompletedGroup.projection k u = 1 := by
    have := CompletedGroup.degreeFiltration_antitone (d.groupTower ℒ)
      (Nat.succ_le_of_lt ha) hu
    rwa [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] at this
  obtain ⟨l', hc, hdeg, hprod⟩ := List.exists_isChain_prod_map_eq_of_exchange l
    (fun x => CompletedGroup.projection k (g x)) deg bad k hbad
    (fun x hx => hone hx (hg x)) fun x y hxy _ _ => by
      by_cases hk : deg x + deg y ≤ k
      · obtain ⟨M, hMdeg, hM⟩ := hex x y hxy hk
        refine ⟨M, hMdeg, ?_⟩
        simpa only [map_mul, map_list_prod, List.map_map, Function.comp_def] using hM
      · -- Factors of total degree above `k` commute at order `k`.
        refine ⟨[], by simp, ?_⟩
        have hcomm := hone (by omega) (d.commutator_degreeFiltration_le ℒ (deg x) (deg y)
          (Subgroup.commutator_mem_commutator (hg x) (hg y)))
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hcomm
        simpa using hcomm
  refine ⟨l', hc, hdeg, ?_⟩
  simpa only [map_list_prod, List.map_map, Function.comp_def] using hprod

end Mei.PositiveDegrees
