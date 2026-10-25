/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Coproduct
public import Mei.RingTheory.Nilpotent.Log
public import Mei.RingTheory.FilteredAlgebra.Quotient

/-!
# Primitive finite BCH logarithms

In a positively graded enveloping algebra over a commutative rational algebra,
the logarithm of a product of two exponentials satisfies the primitive identity
at every finite degree cutoff. Its coproduct takes values in the quotient by
the total tensor filtration, via `quotientCoproduct`. This identity supplies the
primitive condition needed to reconstruct finite BCH Lie elements from their
enveloping algebra images.
-/

public section

open scoped TensorProduct

namespace Mei.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)
  [DecidableEq Γ] [GradedLieAlgebra ℒ]
  (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d (fun n hn => hpos n (le_of_lt hn))
local notation "T" => Ideal.tensorFiltration R
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d (fun n hn => hpos n (le_of_lt hn))))
  (Mei.AlgFiltration.ideal (degreeFiltration ℒ d (fun n hn => hpos n (le_of_lt hn))))

variable [Algebra ℚ R]

/-- The rational scalar action on the enveloping algebra induced from the base. -/
local instance ratAlgebraEnveloping : Algebra ℚ U := Algebra.compHom U (algebraMap ℚ R)
/-- The rational scalar action on the tensor product induced from the base. -/
local instance ratAlgebraTensor : Algebra ℚ (U ⊗[R] U) :=
  Algebra.compHom (U ⊗[R] U) (algebraMap ℚ R)

/-- The finite BCH logarithm is primitive in the total-degree tensor quotient. -/
theorem quotient_log_exp_product_primitive
    (k : ℕ) (x y : L) :
    let q := Ideal.Quotient.mk ((F).ideal (k + 1))
    let z := IsNilpotent.log (IsNilpotent.exp (q (ι R x)) * IsNilpotent.exp (q (ι R y)))
    quotientCoproduct ℒ d (fun n hn => hpos n (le_of_lt hn)) (k + 1) z =
      Mei.AlgFiltration.quotientIncludeLeft R (F) (F) (k + 1) z +
        Mei.AlgFiltration.quotientIncludeRight R (F) (F) (k + 1) z := by
  let q := Ideal.Quotient.mk ((F).ideal (k + 1))
  let δ := quotientCoproduct ℒ d (fun n hn => hpos n (le_of_lt hn)) (k + 1)
  let l := Mei.AlgFiltration.quotientIncludeLeft R (F) (F) (k + 1)
  let r := Mei.AlgFiltration.quotientIncludeRight R (F) (F) (k + 1)
  let π : U ⧸ (F).ideal (k + 1) →+* U ⧸ (F).ideal 1 :=
    Ideal.Quotient.factor ((F).antitone (Nat.le_add_left 1 k))
  -- The kernel of projection to degree one is nilpotent at this finite level.
  have hnil (a : U ⧸ (F).ideal (k + 1)) (ha : π a = 0) : IsNilpotent a :=
    (F).isNilpotent_of_factor_eq_zero k a ha
  have hπ (z : L) : π (q (ι R z)) = 0 := by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact ι_mem_degreeFiltration_one ℒ d hpos z
  have hx := hnil (q (ι R x)) (hπ x)
  have hy := hnil (q (ι R y)) (hπ y)
  have hprim (z : L) : δ (q (ι R z)) = l (q (ι R z)) + r (q (ι R z)) := by
    simp only [δ, l, r, q, quotientCoproduct_mk, Mei.AlgFiltration.quotientIncludeLeft_mk,
      Mei.AlgFiltration.quotientIncludeRight_mk,
      TauCeti.UniversalEnvelopingAlgebra.comul_ι, map_add]
  -- Primitive generators exponentiate to group-like elements in the tensor quotient.
  have he (a : U ⧸ (F).ideal (k + 1)) (ha : IsNilpotent a)
      (hp : δ a = l a + r a) :
      δ (IsNilpotent.exp a) = l (IsNilpotent.exp a) * r (IsNilpotent.exp a) := by
    rw [IsNilpotent.map_exp ha, hp,
      IsNilpotent.exp_add_of_commute (Mei.AlgFiltration.commute_quotientIncludes R (F) (F) _ a a)
        (ha.map l) (ha.map r), ← IsNilpotent.map_exp ha l, ← IsNilpotent.map_exp ha r]
  let g := IsNilpotent.exp (q (ι R x)) * IsNilpotent.exp (q (ι R y))
  have hg : δ g = l g * r g := by
    rw [map_mul, he _ hx (hprim x), he _ hy (hprim y), map_mul, map_mul]
    exact (Mei.AlgFiltration.commute_quotientIncludes R (F) (F) _ (IsNilpotent.exp (q (ι R y)))
      (IsNilpotent.exp (q (ι R x)))).symm.mul_mul_mul_comm _ _
  have hgu : IsNilpotent (g - 1) := by
    apply hnil
    rw [map_sub, map_one, map_mul, IsNilpotent.map_exp hx, IsNilpotent.map_exp hy,
      hπ x, hπ y, IsNilpotent.exp_zero, one_mul, sub_self]
  have hl : IsNilpotent (l g - 1) := by simpa only [map_sub, map_one] using hgu.map l
  have hr : IsNilpotent (r g - 1) := by simpa only [map_sub, map_one] using hgu.map r
  -- The logarithm of the commuting left/right product is the sum of logarithms.
  have hc : Commute (l g) (r g) := Mei.AlgFiltration.commute_quotientIncludes R (F) (F) _ g g
  have hz : δ (IsNilpotent.log g) = l (IsNilpotent.log g) + r (IsNilpotent.log g) := by
    rw [IsNilpotent.map_log hgu, hg]
    have hm := IsNilpotent.log_mul_of_commute hc hl hr
    convert hm using 1 <;> congr 1
    · exact IsNilpotent.map_log hgu l
    · exact IsNilpotent.map_log hgu r
  exact hz

end Mei.UniversalEnvelopingAlgebra
