/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Skew.Factorization.Completion
public import Mei.Algebra.Lie.Skew.Factorization.Sorted
public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Order
public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Ordering

/-!
# Positive ordering in the standard plane to all orders

The ordered factorizations of `Mei.StandardPlane.exists_isChain_projection_prod_pow_eq` are
finite-order statements, with an ordered list of unit factors chosen separately at every order
`k`. Here they are assembled into one factorization of the completed label. Order the plane
degrees by angle, counterclockwise from the first axis, and among collinear degrees by size
(`PlaneDegree.key`). Every finite product of normalized positive factors `Ψ[m]^{s κ(m)}`,
`s ∈ ℕ`, of plane degrees then has a unique ordered factorization
`∏ₘ Ψ[m]^{s'(m) κ(m)}` over all plane degrees in this order, where the exponents `s'(m)`
are natural numbers (`existsUnique_orderedProd_dilogPow`). The factorization has finitely many
nonidentity factors at every order, which is what makes the infinite ordered product well
defined.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2
  (arXiv:2111.00800v6).
-/

public section

open TauCeti.CompletedGroup (projection)

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples

variable {w : Weight}


local notation "β" => E.coefficientForm ℚ
local notation "hβ" => E.isAlt_coefficientForm ℚ

/-- A family of rational powers of dilogarithm labels of plane degrees has only finitely many
nonidentity factors at every order. -/
theorem hasFiniteSupport_dilogPow (c : PlaneDegree w → ℚ) :
    TauCeti.CompletedGroup.HasFiniteSupport fun m => dilogPow m (c m) := by
  simpa only [dilogPow_def] using SkewLieAlgebra.hasFiniteSupport_rayExp_smul_negDilogNeg β hβ
    PlaneDegree.vec PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective c

/-- **Positive ordering in the standard plane, to all orders.** A finite product of normalized
positive factors `Ψ[m]^{s κ(m)}`, `s ∈ ℕ`, of plane degrees equals, for exactly one family of
natural numbers `s'`, the ordered product `∏ₘ Ψ[m]^{s'(m) κ(m)}` over all plane degrees in the
angular order (`PlaneDegree.key`), smallest degree leftmost. Only finitely many factors are
nonidentity at every order (`hasFiniteSupport_dilogPow`), so the infinite product is defined. -/
theorem existsUnique_orderedProd_dilogPow (l : List (PlaneDegree w × ℕ)) :
    ∃! s : PlaneDegree w → ℕ,
      TauCeti.CompletedGroup.orderedProd (fun m => dilogPow m (s m * rayIndex m.vec))
          (hasFiniteSupport_dilogPow fun m => s m * rayIndex m.vec) =
        (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
  -- At every order, the ordered unit factors of the finite-order ordering form a sorted list.
  have hfact (k : ℕ) : ∃ l' : List (PlaneDegree w),
      l'.Pairwise (fun a b => 0 ≤ β a.vec b.vec) ∧
      projection k (l'.map fun m => SkewLieAlgebra.rayExp β hβ m.mem m.ne_zero
          (rayIndex m.vec • PowerSeries.negDilogNeg ℚ)).prod =
        projection k
          (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
    obtain ⟨l', hchain, -, hprod⟩ := exists_isChain_projection_prod_pow_eq k l
    refine ⟨l', LinearMap.IsAlt.pairwise_of_isChain_of_mem_closure_pair hβ PlaneDegree.vec
      (fun m _ => m.vec_mem_closure) (fun m _ => m.ne_zero) hchain, ?_⟩
    simpa only [show (unitFactor : PlaneDegree w → Label w) = fun m => dilogPow m (rayIndex m.vec)
      from funext unitFactor_def, dilogPow_def] using hprod
  simpa only [dilogPow_def, nsmul_eq_mul] using
    SkewLieAlgebra.existsUnique_orderedProd_rayExp_nsmul_smul_negDilogNeg β hβ PlaneDegree.vec
      PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective
      (fun _ _ => PlaneDegree.le_of_coefficientForm_pos) (fun m => rayIndex m.vec)
      (fun m => m.rayIndex_pos.ne') _ hfact

end Mei.StandardPlane
