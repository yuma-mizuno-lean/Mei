/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.Lie.Skew.Factorization.Completion
public import Mei.Algebra.Lie.Skew.Factorization.Sorted
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
are natural numbers (`existsUnique_orderedProd_dilogPow`). The factorization is compatible
under truncation: at every order only finitely many factors are nonidentity, and the exponents
are determined by the product through any cutoff above their degree.

## References

* Tomoki Nakanishi, *Cluster algebras and scattering diagrams, Part III*, §5.2
  (arXiv:2111.00800v6).
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples

variable {w : Weight}

namespace PlaneDegree

/-- The sort key of a plane degree: the angle coordinate `m₂ / (m₁ + m₂)`, which increases
with the slope of `m`, followed by the size `m₁ + m₂` to separate collinear degrees. -/
def key (m : PlaneDegree w) : ℚ ×ₗ ℤ := toLex ((m.snd : ℚ) / (m.fst + m.snd), m.fst + m.snd)

theorem fst_add_snd_pos (m : PlaneDegree w) : 0 < m.fst + m.snd := by
  have := m.fst_nonneg
  have := m.snd_nonneg
  rcases m.fst_ne_zero_or <;> omega

theorem key_injective : Function.Injective (key (w := w)) := by
  intro x y h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx : (0 : ℚ) < x.fst + x.snd := by exact_mod_cast x.fst_add_snd_pos
  have hy : (0 : ℚ) < y.fst + y.snd := by exact_mod_cast y.fst_add_snd_pos
  rw [div_eq_div_iff hx.ne' hy.ne'] at h1
  have h1' : x.snd * (y.fst + y.snd) = y.snd * (x.fst + x.snd) := by exact_mod_cast h1
  rw [← h2] at h1'
  have hsnd : x.snd = y.snd := mul_right_cancel₀ x.fst_add_snd_pos.ne' h1'
  have hfst : x.fst = y.fst := by omega
  exact PlaneDegree.ext (Subtype.ext (Prod.ext hfst hsnd))

/-- Plane degrees are sorted counterclockwise from the first axis, collinear ones by size. -/
instance : LinearOrder (PlaneDegree w) := LinearOrder.lift' key key_injective

-- The order is lifted along `key`, so the next lemma holds by unfolding the lifted order.
theorem lt_iff_key_lt {x y : PlaneDegree w} : x < y ↔ x.key < y.key := Iff.rfl

/-- A pair of plane degrees with positive pairing `{x, y}` is in order. -/
theorem lt_of_det_pos {x y : PlaneDegree w} (h : 0 < x.det y) : x < y := by
  have hx : (0 : ℚ) < x.fst + x.snd := by exact_mod_cast x.fst_add_snd_pos
  have hy : (0 : ℚ) < y.fst + y.snd := by exact_mod_cast y.fst_add_snd_pos
  have h' : x.snd * y.fst < x.fst * y.snd := by rw [det_eq] at h; linarith
  have h'' : (x.snd : ℚ) * y.fst < x.fst * y.snd := by exact_mod_cast h'
  rw [lt_iff_key_lt, key, key, Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  rw [div_lt_div_iff₀ hx hy]
  linarith

theorem le_of_coefficientForm_pos {x y : PlaneDegree w}
    (h : 0 < E.coefficientForm ℚ x.vec y.vec) : x ≤ y := by
  rw [coefficientForm_det] at h
  exact (lt_of_det_pos (by exact_mod_cast h)).le

theorem vec_injective : Function.Injective (vec (w := w)) := fun _ _ h => PlaneDegree.ext h

end PlaneDegree

local notation "β" => E.coefficientForm ℚ
local notation "hβ" => E.isAlt_coefficientForm ℚ

/-- A family of rational powers of dilogarithm labels of plane degrees has only finitely many
nonidentity factors at every order. -/
theorem hasFiniteSupport_dilogPow (c : PlaneDegree w → ℚ) :
    CompletedGroup.HasFiniteSupport fun m => dilogPow m (c m) := by
  simpa only [dilogPow_def] using SkewLieAlgebra.hasFiniteSupport_rayExp_smul_negDilogNeg β hβ
    PlaneDegree.vec PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective c

/-- At every order, a product of normalized positive factors is a finite product, in the angular
order, of unit factors with multiplicities. -/
private theorem exists_finsupp_projection_orderedDilogProduct_eq (l : List (PlaneDegree w × ℕ))
    (k : ℕ) :
    ∃ a : PlaneDegree w →₀ ℚ, (∀ m, ∃ s : ℕ, a m = s * rayIndex m.vec) ∧
      CompletedGroup.projection k (SkewLieAlgebra.orderedDilogProduct β hβ PlaneDegree.vec
          PlaneDegree.mem PlaneDegree.ne_zero a.support a) =
        CompletedGroup.projection k
          (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
  obtain ⟨l', hchain, -, hprod⟩ := exists_isChain_projection_prod_pow_eq k l
  have hpw : l'.Pairwise fun a b => 0 ≤ E.coefficientForm ℚ a.vec b.vec :=
    hchain.pairwise_of_forall_mem (p := fun _ => True) (fun _ _ => trivial)
      fun a b c _ _ _ hab hbc => LinearMap.IsAlt.nonneg_trans_of_mem_closure_pair
        (E.isAlt_coefficientForm ℚ) a.vec_mem_closure b.vec_mem_closure c.vec_mem_closure
        b.ne_zero hab hbc
  obtain ⟨a, ha, hl'⟩ := SkewLieAlgebra.exists_prod_rayExp_eq_orderedDilogProduct β hβ
    PlaneDegree.vec PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective
    (fun _ _ => PlaneDegree.le_of_coefficientForm_pos) (fun m => rayIndex m.vec) l' hpw
  refine ⟨a, fun m => ⟨l'.count m, by rw [ha, nsmul_eq_mul]⟩, ?_⟩
  have hunit : (unitFactor : PlaneDegree w → Label w) = fun m =>
      SkewLieAlgebra.rayExp β hβ m.mem m.ne_zero (rayIndex m.vec • PowerSeries.negDilogNeg ℚ) :=
    funext fun m => by rw [unitFactor_def, dilogPow_def]
  rw [← hl', ← hprod, hunit]

/-- **Positive ordering in the standard plane, to all orders.** A finite product of normalized
positive factors `Ψ[m]^{s κ(m)}`, `s ∈ ℕ`, of plane degrees equals, for exactly one family of
natural numbers `s'`, the ordered product `∏ₘ Ψ[m]^{s'(m) κ(m)}` over all plane degrees in the
angular order (`PlaneDegree.key`), smallest degree leftmost. Only finitely many factors are
nonidentity at every order, and the exponents of the factors of degree at most `k` are those of
any finite ordered factorization of the product at order `k`, such as the one given by
`exists_isChain_projection_prod_pow_eq`. -/
theorem existsUnique_orderedProd_dilogPow (l : List (PlaneDegree w × ℕ)) :
    ∃! s : PlaneDegree w → ℕ,
      CompletedGroup.orderedProd (fun m => dilogPow m (s m * rayIndex m.vec))
          (hasFiniteSupport_dilogPow fun m => s m * rayIndex m.vec) =
        (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod := by
  choose a ha hk using exists_finsupp_projection_orderedDilogProduct_eq l
  obtain ⟨c, hc, huniq⟩ := SkewLieAlgebra.existsUnique_orderedProd_rayExp_smul_negDilogNeg β hβ
    PlaneDegree.vec PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective
    (l.map fun p => dilogPow p.1 (p.2 * rayIndex p.1.vec)).prod fun k => ⟨a k, hk k⟩
  -- The assembled exponents agree with those of the factorization at order `deg m`.
  have hcs : ∀ m : PlaneDegree w, ∃ s : ℕ, c m = s * rayIndex m.vec := fun m => by
    obtain ⟨s, hs⟩ := ha m.deg m
    exact ⟨s, (SkewLieAlgebra.eq_of_orderedProd_rayExp_smul_negDilogNeg_eq β hβ
      PlaneDegree.vec PlaneDegree.mem PlaneDegree.ne_zero PlaneDegree.vec_injective c (a m.deg)
      hc (hk m.deg) m m.deg_eq_degree.ge).trans hs⟩
  choose s hs using hcs
  obtain rfl : c = fun m => s m * rayIndex m.vec := funext hs
  refine ⟨s, by simpa only [dilogPow_def] using hc, fun s' hs' => funext fun m => ?_⟩
  have h := congrFun (huniq (fun m => s' m * rayIndex m.vec)
    (by simpa only [dilogPow_def] using hs')) m
  exact_mod_cast mul_right_cancel₀ m.rayIndex_pos.ne' h

end Mei.StandardPlane
