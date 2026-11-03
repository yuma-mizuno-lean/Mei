/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Exchange

/-!
# Ordering of products of normalized positive factors in the standard plane

At every finite order, a product of normalized positive factors `Ψ[m]^{sκ(m)}`, `s ∈ ℕ`, of
degrees in the first quadrant of the unimodular plane agrees with a product of unit factors
`Ψ[m']^{κ(m')}` all of whose adjacent pairs are ordered, `{m', m''} ≥ 0`
(`exists_isChain_projection_prod_pow_eq`). This is the positive ordering of rank-two products
for the standard plane and arbitrary positive weights, from the exchange of antiordered pairs
(`exists_exchange`) and the termination of the exchange algorithm
(`Mei.PositiveDegrees.exists_isChain_projection_prod_eq_of_exchange`). The positive integer
exponents of the factors of the ordered product are the multiplicities of the degrees in the
list.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2
  (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples

variable {w : Weight}

/-- **Ordering in the standard plane.** At every finite order `k`, a finite product of unitFactor
factors `Ψ[m]^{κ(m)}` of plane degrees agrees with a product of unit factors in which all
adjacent pairings `{m, m'}` are nonnegative. -/
theorem exists_isChain_projection_prod_unit_eq (k : ℕ) (l : List (PlaneDegree w)) :
    ∃ l' : List (PlaneDegree w), (l'.IsChain fun a b => 0 ≤ E.coefficientForm ℚ a.vec b.vec) ∧
      (∀ m ∈ l', m.deg ≤ k) ∧
      CompletedGroup.projection k (l'.map unitFactor).prod =
        CompletedGroup.projection k (l.map unitFactor).prod := by
  classical
  obtain ⟨l', hchain, hdeg, hprod, -⟩ :=
    Mei.PositiveDegrees.exists_isChain_projection_prod_eq_of_exchange (plane w)
      (SkewLieAlgebra.positiveGrading (E.coefficientForm ℚ) (E.isAlt_coefficientForm ℚ)
        (plane w)) l unitFactor PlaneDegree.deg PlaneDegree.Inverted (fun _ => False) k
      (fun m => unitFactor_mem_degreeFiltration m)
      (fun a b hab hba => by
        rw [PlaneDegree.inverted_iff] at hab hba
        nlinarith)
      (fun x y hxy hk => (exists_exchange k x y hxy hk).imp fun M hM =>
        ⟨fun m hm => ⟨(hM.1 m hm).1, (hM.1 m hm).2.1, fun h => h⟩, hM.2⟩)
  refine ⟨l', hchain.imp fun a b hab => not_lt.mp fun h => ?_, hdeg, hprod⟩
  exact hab ((PlaneDegree.inverted_def a b).mpr h)

/-- **Positive ordering in the standard plane.** At every finite order `k`, a finite product of
normalized positive factors `Ψ[m]^{s κ(m)}`, `s ∈ ℕ`, of plane degrees agrees with an ordered
product of unit factors `Ψ[m']^{κ(m')}`: all adjacent pairings `{m', m''}` are nonnegative and
each factor has weighted degree at most `k`. -/
theorem exists_isChain_projection_prod_pow_eq (k : ℕ) (l : List (PlaneDegree w × ℕ)) :
    ∃ l' : List (PlaneDegree w), (l'.IsChain fun a b => 0 ≤ E.coefficientForm ℚ a.vec b.vec) ∧
      (∀ m ∈ l', m.deg ≤ k) ∧
      CompletedGroup.projection k (l'.map unitFactor).prod =
        CompletedGroup.projection k
          (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
  have hflat : ∀ l : List (PlaneDegree w × ℕ),
      ((l.flatMap fun p => List.replicate p.2 p.1).map unitFactor).prod =
        (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate,
        List.prod_replicate, List.map_cons, List.prod_cons, unitFactor_def, ← dilogPow_natCast_mul]
  obtain ⟨l', hchain, hdeg, hprod⟩ := exists_isChain_projection_prod_unit_eq k
    (l.flatMap fun p => List.replicate p.2 p.1)
  exact ⟨l', hchain, hdeg, by rw [hprod, hflat]⟩

end Mei.StandardPlane
