/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Grading
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Naturality

/-!
# Upper coordinate transport in the focus-focus chambers

The shear `(a,b,h) ↦ (a,b-a,h)` induces automorphisms of both chamber order
quotients. They transport the full exponent pieces, and hence their homogeneous
projections, along this shear. Through the chamber dictionary these give the
upper coordinate changes `x ↦ wx`, `y ↦ w⁻¹y` in the nodal presentations over
truncated polynomial scalars. Coefficient change and cutoff reduction commute
with this transport, even when they kill homogeneous coefficients.

We use Mathlib's `AddMonoidAlgebra.domCongr` and `Ideal.quotientEquivAlg`,
Tau Ceti's `DirectSum.map_decompose_shift`, and the chamber dictionary
`truncatedExponentChamberEquiv`. The coordinate conventions follow
Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open AddMonoidAlgebra
open scoped _root_.LaurentPolynomial Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ) (i : Fin 2)

private theorem map_upperMonoid_orderIdeal :
    (Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)}).map
        (domCongr K K upperMonoid : AddMonoidAlgebra K exponentMonoid →+*
          AddMonoidAlgebra K exponentMonoid) =
      Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)} := by
  have hmem (f : AddMonoidAlgebra K exponentMonoid) :
      domCongr K K upperMonoid f ∈
          Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)} ↔
        f ∈ Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)} := by
    have ho (q : exponentMonoid) : chamberOrder i (upperMonoid q) = chamberOrder i q := by
      fin_cases i <;> simp
    simp only [mem_span_single_pow_iff, domCongr_support, Finset.forall_mem_map,
      Equiv.toEmbedding_apply, AddEquiv.coe_toEquiv, ho]
  refine (Ideal.map_comap_of_equiv (domCongr K K upperMonoid).toRingEquiv).trans
    (Ideal.ext fun f => ?_)
  rw [Ideal.mem_comap, ← hmem, AlgEquiv.toRingEquiv_symm, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.apply_symm_apply]

/-- Upper exponent transport on either absolute chamber order quotient. -/
def upperExponentOrder : ExponentOrderQuotient K k i ≃ₐ[K] ExponentOrderQuotient K k i :=
  Ideal.quotientEquivAlg _ _ (domCongr K K upperMonoid)
    (map_upperMonoid_orderIdeal K k i).symm

/-- The upper change acts on every representative by the exponent shear. -/
@[simp]
theorem upperExponentOrder_mk (f : AddMonoidAlgebra K exponentMonoid) :
    upperExponentOrder K k i (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (domCongr K K upperMonoid f) :=
  Ideal.quotientEquivAlg_mk _ _ _ f

/-- Inverse transport uses the inverse exponent shear. -/
@[simp]
theorem upperExponentOrder_symm_mk (f : AddMonoidAlgebra K exponentMonoid) :
    (upperExponentOrder K k i).symm (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (domCongr K K upperMonoid.symm f) := by
  apply (upperExponentOrder K k i).injective
  rw [AlgEquiv.apply_symm_apply, upperExponentOrder_mk, ← domCongr_symm,
    AlgEquiv.apply_symm_apply]

/-- Every homogeneous chamber element is transported to the sheared exponent. -/
private theorem upperExponentOrder_mem_grade (q : ℤ × ℤ × ℤ)
    (x : ExponentOrderQuotient K k i) (hx : x ∈ exponentOrderGrade K k i q) :
    upperExponentOrder K k i x ∈ exponentOrderGrade K k i (upperExponent q) := by
  by_cases hq : q ∈ exponentMonoid
  · obtain ⟨r, rfl⟩ := (mem_exponentOrderGrade_iff K k i ⟨q, hq⟩ x).mp hx
    rw [upperExponentOrder_mk, domCongr_single]
    simpa only [coe_upperMonoid, Subtype.coe_mk] using
      (mem_exponentOrderGrade_iff K k i (upperMonoid ⟨q, hq⟩) _).mpr ⟨r, rfl⟩
  · rw [exponentOrderGrade_eq_bot_of_notMem K k i q hq] at hx
    simp only [Submodule.mem_bot] at hx
    simp [hx]

/-- Upper transport commutes with homogeneous projection after shearing its index. -/
theorem upperExponentOrder_decompose (q : ℤ × ℤ × ℤ)
    (x : ExponentOrderQuotient K k i) :
    upperExponentOrder K k i
        (DirectSum.decompose (exponentOrderGrade K k i) x q : ExponentOrderQuotient K k i) =
      (DirectSum.decompose (exponentOrderGrade K k i)
        (upperExponentOrder K k i x) (upperExponent q) : ExponentOrderQuotient K k i) :=
  DirectSum.map_decompose_shift _ _ (upperExponentOrder K k i).toAlgHom.toAddMonoidHom
    upperExponent upperExponent.injective (upperExponentOrder_mem_grade K k i) q x

/-- The upper coordinate change identifies entire exponent pieces, including zero pieces. -/
@[simp]
theorem upperExponentOrder_mem_grade_iff (q : ℤ × ℤ × ℤ)
    (x : ExponentOrderQuotient K k i) :
    upperExponentOrder K k i x ∈ exponentOrderGrade K k i (q.1, q.2.1 - q.1, q.2.2) ↔
      x ∈ exponentOrderGrade K k i q := by
  rw [← upperExponent_apply]
  refine ⟨fun hx => ?_, upperExponentOrder_mem_grade K k i q x⟩
  have he := upperExponentOrder_decompose K k i q x
  rw [DirectSum.decompose_of_mem_same _ hx] at he
  have hx' := (upperExponentOrder K k i).injective he
  exact hx' ▸ (DirectSum.decompose (exponentOrderGrade K k i) x q).property

/-- Upper coordinate change on the nodal chamber over truncated smoothing scalars. -/
def upperTruncatedExponentChamber :
    TruncatedExponentChamber K k i ≃ₐ[K] TruncatedExponentChamber K k i :=
  (truncatedExponentChamberEquiv K k i).symm.trans
    ((upperExponentOrder K k i).trans (truncatedExponentChamberEquiv K k i))

/-- The chamber dictionary intertwines the absolute and nodal upper changes. -/
@[simp]
theorem upperTruncatedExponentChamber_equiv (x : ExponentOrderQuotient K k i) :
    upperTruncatedExponentChamber K k i (truncatedExponentChamberEquiv K k i x) =
      truncatedExponentChamberEquiv K k i (upperExponentOrder K k i x) := by
  simp [upperTruncatedExponentChamber]

/-- The inverse chamber dictionary also intertwines upper transport. -/
@[simp]
theorem truncatedExponentChamberEquiv_symm_upper (x : TruncatedExponentChamber K k i) :
    (truncatedExponentChamberEquiv K k i).symm (upperTruncatedExponentChamber K k i x) =
      upperExponentOrder K k i ((truncatedExponentChamberEquiv K k i).symm x) := by
  obtain ⟨x, rfl⟩ := (truncatedExponentChamberEquiv K k i).surjective x
  simp only [upperTruncatedExponentChamber_equiv, AlgEquiv.symm_apply_apply]

/-- Inverse upper change through the same dictionary. -/
@[simp]
theorem upperTruncatedExponentChamber_symm_equiv (x : ExponentOrderQuotient K k i) :
    (upperTruncatedExponentChamber K k i).symm (truncatedExponentChamberEquiv K k i x) =
      truncatedExponentChamberEquiv K k i ((upperExponentOrder K k i).symm x) := by
  apply (upperTruncatedExponentChamber K k i).injective
  simp

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)

/-- A homogeneous monomial in the nodal chamber retains its coefficient and its
coordinate powers; only its tangential exponent changes by `-a`. -/
theorem upperTruncatedExponentChamber_single (q : exponentMonoid) (r : K) :
    upperTruncatedExponentChamber K k i
        (truncatedExponentChamberEquiv K k i (Ideal.Quotient.mk _ (single q r))) =
      Ideal.Quotient.mk _
        (algebraMap S[ℤ] _ (single (q.val.2.1 - q.val.1) (AdjoinRoot.of _ r)) *
          TauCeti.NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 0 ^ rightOrder q *
          TauCeti.NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 1 ^ leftOrder q) := by
  rw [upperTruncatedExponentChamber_equiv, upperExponentOrder_mk, domCongr_single,
    truncatedExponentChamberEquiv_single]
  simp

/-- On the two node coordinates the upper change is `x ↦ wx`, `y ↦ w⁻¹y`. -/
@[simp]
theorem upperTruncatedExponentChamber_coord (j : Fin 2) :
    upperTruncatedExponentChamber K k i
        (Ideal.Quotient.mk _ (TauCeti.NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j)) =
      algebraMap S[ℤ] (TruncatedExponentChamber K k i)
          (_root_.LaurentPolynomial.T (![1, -1] j)) *
        Ideal.Quotient.mk _ (TauCeti.NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j) := by
  have hc := (truncatedExponentChamberEquiv K k i).apply_symm_apply
    (Ideal.Quotient.mk _ (TauCeti.NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j))
  rw [truncatedExponentChamberEquiv_symm_coord] at hc
  calc
    _ = upperTruncatedExponentChamber K k i
        (truncatedExponentChamberEquiv K k i
          (Ideal.Quotient.mk _ (single (![xDegree, yDegree] j) 1))) := congrArg _ hc.symm
    _ = _ := by
      rw [upperTruncatedExponentChamber_single]
      fin_cases j <;> simp

/-- The smoothing parameter is fixed by the upper change. -/
@[simp]
theorem upperTruncatedExponentChamber_parameter :
    upperTruncatedExponentChamber K k i (algebraMap S (TruncatedExponentChamber K k i) τ) =
      algebraMap S (TruncatedExponentChamber K k i) τ := by
  apply (truncatedExponentChamberEquiv K k i).symm.injective
  simp only [truncatedExponentChamberEquiv_symm_upper,
    truncatedExponentChamberEquiv_symm_parameter, upperExponentOrder_mk,
    domCongr_single, upperMonoid_smoothingDegree]

/-- Tangential Laurent monomials are fixed by the upper change. -/
@[simp]
theorem upperTruncatedExponentChamber_tangent (b : ℤ) :
    upperTruncatedExponentChamber K k i
        (algebraMap S[ℤ] (TruncatedExponentChamber K k i) (_root_.LaurentPolynomial.T b)) =
      algebraMap S[ℤ] (TruncatedExponentChamber K k i) (_root_.LaurentPolynomial.T b) := by
  apply (truncatedExponentChamberEquiv K k i).symm.injective
  simp only [truncatedExponentChamberEquiv_symm_upper,
    truncatedExponentChamberEquiv_symm_tangent, upperExponentOrder_mk,
    domCongr_single, upperMonoid_tangentDegree]

/-- Full exponent homogeneity in the nodal chamber is transported by the upper shear. -/
@[simp]
theorem upperTruncatedExponentChamber_mem_grade_iff (q : ℤ × ℤ × ℤ)
    (x : TruncatedExponentChamber K k i) :
    upperTruncatedExponentChamber K k i x ∈
        truncatedExponentChamberGrade K k i (q.1, q.2.1 - q.1, q.2.2) ↔
      x ∈ truncatedExponentChamberGrade K k i q := by
  obtain ⟨x, rfl⟩ := (truncatedExponentChamberEquiv K k i).surjective x
  simp only [upperTruncatedExponentChamber_equiv,
    mem_truncatedExponentChamberGrade_iff, AlgEquiv.symm_apply_apply,
    upperExponentOrder_mem_grade_iff]

/-- Nodal homogeneous projections commute with upper transport at the sheared degree. -/
theorem upperTruncatedExponentChamber_decompose (q : ℤ × ℤ × ℤ)
    (x : TruncatedExponentChamber K k i) :
    upperTruncatedExponentChamber K k i
        (DirectSum.decompose (truncatedExponentChamberGrade K k i) x q :
          TruncatedExponentChamber K k i) =
      (DirectSum.decompose (truncatedExponentChamberGrade K k i)
        (upperTruncatedExponentChamber K k i x) (upperExponent q) :
          TruncatedExponentChamber K k i) :=
  DirectSum.map_decompose_shift _ _
    (upperTruncatedExponentChamber K k i).toAlgHom.toAddMonoidHom
    upperExponent upperExponent.injective
    (fun q x hx => by
      rw [upperExponent_apply]
      exact (upperTruncatedExponentChamber_mem_grade_iff K k i q x).mpr hx) q x

variable {K' : Type*} [CommRing K'] {l : ℕ} (φ : K →+* K') (hl : l ≤ k)

/-- Upper exponent transport commutes with coefficient changes and cutoff reductions. -/
theorem exponentOrderMap_upperExponentOrder (x : ExponentOrderQuotient K k i) :
    exponentOrderMap φ hl i (upperExponentOrder K k i x) =
      upperExponentOrder K' l i (exponentOrderMap φ hl i x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [upperExponentOrder_mk, exponentOrderMap_mk]
  congr 1
  exact RingHom.congr_fun
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom φ upperMonoid.toAddMonoidHom) f

/-- The nodal upper change is compatible with the same coefficient and cutoff maps. -/
theorem truncatedExponentChamberMap_upper (x : TruncatedExponentChamber K k i) :
    truncatedExponentChamberMap φ hl i (upperTruncatedExponentChamber K k i x) =
      upperTruncatedExponentChamber K' l i (truncatedExponentChamberMap φ hl i x) := by
  obtain ⟨x, rfl⟩ := (truncatedExponentChamberEquiv K k i).surjective x
  simp only [upperTruncatedExponentChamber_equiv, truncatedExponentChamberMap_equiv,
    exponentOrderMap_upperExponentOrder]

end Mei.FocusFocus
