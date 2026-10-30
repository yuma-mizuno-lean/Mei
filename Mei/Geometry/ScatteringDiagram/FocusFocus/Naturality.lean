/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.OrderQuotient
public import Mei.RingTheory.Node.Map

/-!
# Naturality of the focus-focus chamber dictionary

Coefficient homomorphisms and reductions of the chamber order act on both the
absolute exponent quotients and the nodal chambers over truncated polynomial
scalars. The comparison `truncatedExponentChamberEquiv` intertwines these maps.
Thus the chamber dictionary compares quotient towers, rather than only their
individual rings.

We use Mathlib's `AdjoinRoot.map`, `Ideal.quotientMap` and coefficient maps of
monoid algebras, and `Mei.NodeAlgebra.mapOfEq`. The coordinates
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra
open scoped LaurentPolynomial Mei.NodeAlgebra

variable {K K' K'' : Type*} [CommRing K] [CommRing K'] [CommRing K'']
  {k l m : ℕ} (φ : K →+* K') (hl : l ≤ k) (i : Fin 2)

/-- Change coefficients and lower the order in the absolute exponent quotient. -/
def exponentOrderMap : ExponentOrderQuotient K k i →+* ExponentOrderQuotient K' l i :=
  Ideal.quotientMap _ (mapRingHom exponentMonoid φ) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      mapRingHom_single, map_one, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ (by omega))

/-- The absolute quotient map acts coefficientwise on every representative. -/
@[simp]
theorem exponentOrderMap_mk (a : AddMonoidAlgebra K exponentMonoid) :
    exponentOrderMap φ hl i (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (mapRingHom exponentMonoid φ a) := (rfl)

/-- Changing neither coefficients nor cutoff gives the identity map. -/
@[simp]
theorem exponentOrderMap_id :
    exponentOrderMap (RingHom.id K) (k := k) le_rfl i = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp

/-- Coefficient change and order reduction compose in the expected order. -/
theorem exponentOrderMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (exponentOrderMap ψ hm i).comp (exponentOrderMap φ hl i) =
      exponentOrderMap (ψ.comp φ) (hm.trans hl) i := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp [mapRingHom_comp]

/-- Surjective coefficient maps induce surjective chamber order maps. In
particular, the cutoff transition maps are surjective. -/
theorem exponentOrderMap_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (exponentOrderMap φ hl i) :=
  Ideal.quotientMap_surjective (map_surjective φ.toAddMonoidHom hφ)

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "S'" => AdjoinRoot (Polynomial.X ^ (l + 1) : Polynomial K')
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ'" => AdjoinRoot.root (Polynomial.X ^ (l + 1) : Polynomial K')

private def nodeReduction : NodeAlgebra S[ℤ] (_root_.LaurentPolynomial.C τ) →+*
    NodeAlgebra S'[ℤ] (_root_.LaurentPolynomial.C τ') := by
  let f := mapRingHom ℤ (AdjoinRoot.map φ (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1))))
  letI : Algebra S[ℤ] S'[ℤ] := f.toAlgebra
  letI : Algebra S[ℤ] (NodeAlgebra S'[ℤ] (_root_.LaurentPolynomial.C τ')) :=
    Algebra.compHom _ f
  letI : IsScalarTower S[ℤ] S'[ℤ]
      (NodeAlgebra S'[ℤ] (_root_.LaurentPolynomial.C τ')) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Mei.NodeAlgebra.mapOfEq (_root_.LaurentPolynomial.C τ) (by
    simp only [RingHom.algebraMap_toAlgebra, f, ← _root_.LaurentPolynomial.single_eq_C,
      mapRingHom_single, AdjoinRoot.map_root])).toRingHom

private theorem nodeReduction_coord (j : Fin 2) :
    nodeReduction φ hl (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j) =
      NodeAlgebra.coord (_root_.LaurentPolynomial.C τ') j := by
  let f := mapRingHom ℤ (AdjoinRoot.map φ (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1))))
  let : Algebra S[ℤ] S'[ℤ] := f.toAlgebra
  let : Algebra S[ℤ] (NodeAlgebra S'[ℤ] (_root_.LaurentPolynomial.C τ')) :=
    Algebra.compHom _ f
  let : IsScalarTower S[ℤ] S'[ℤ]
      (NodeAlgebra S'[ℤ] (_root_.LaurentPolynomial.C τ')) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Mei.NodeAlgebra.mapOfEq_coord _ _ j

private theorem nodeReduction_algebraMap (a : S[ℤ]) :
    nodeReduction φ hl (algebraMap S[ℤ] _ a) =
      algebraMap S'[ℤ] _ (mapRingHom ℤ (AdjoinRoot.map φ
        (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1)))) a) := by
  simp [nodeReduction, Algebra.compHom_algebraMap_eq]

private theorem nodeReduction_mk (p : MvPolynomial (Fin 2) S[ℤ]) :
    nodeReduction φ hl (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ) p) =
      NodeAlgebra.mk (_root_.LaurentPolynomial.C τ')
        (MvPolynomial.map (mapRingHom ℤ (AdjoinRoot.map φ
          (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1))))) p) := by
  have h : (nodeReduction φ hl).comp
      (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)).toRingHom =
      (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ')).toRingHom.comp
        (MvPolynomial.map (mapRingHom ℤ (AdjoinRoot.map φ
          (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1)))))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.map_C]
      rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, nodeReduction_algebraMap,
        MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
    · intro j
      simpa using nodeReduction_coord φ hl j
  exact RingHom.congr_fun h p

/-- Change coefficients and reduce the order in the nodal chamber. The truncated
scalar parameter is reduced by `AdjoinRoot.map`, and both node coordinates are fixed. -/
def truncatedExponentChamberMap :
    TruncatedExponentChamber K k i →+* TruncatedExponentChamber K' l i :=
  Ideal.quotientMap _ (nodeReduction φ hl) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      nodeReduction_coord, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ (by omega))

/-- On polynomial representatives the nodal chamber map changes only coefficients. -/
@[simp]
theorem truncatedExponentChamberMap_mk (p : MvPolynomial (Fin 2) S[ℤ]) :
    truncatedExponentChamberMap φ hl i
        (Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ) p)) =
      Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ')
        (MvPolynomial.map (mapRingHom ℤ (AdjoinRoot.map φ
          (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
        (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
          (Nat.add_le_add_right hl 1))))) p)) := by
  rw [truncatedExponentChamberMap, Ideal.quotientMap_mk, nodeReduction_mk]

/-- Both nodal coordinates retain their quotient classes. -/
@[simp]
theorem truncatedExponentChamberMap_coord (j : Fin 2) :
    truncatedExponentChamberMap φ hl i
        (Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j)) =
      Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ') j) := by
  rw [truncatedExponentChamberMap, Ideal.quotientMap_mk, nodeReduction_coord]

/-- The coefficient Laurent algebra is reduced by the usual truncated scalar map. -/
@[simp]
theorem truncatedExponentChamberMap_algebraMap (a : S[ℤ]) :
    truncatedExponentChamberMap φ hl i (algebraMap S[ℤ] _ a) =
      algebraMap S'[ℤ] _ (mapRingHom ℤ (AdjoinRoot.map φ (Polynomial.X ^ (k + 1))
        (Polynomial.X ^ (l + 1)) (by simpa using
          (pow_dvd_pow (Polynomial.X : Polynomial K') (Nat.add_le_add_right hl 1)))) a) := by
  rw [← Ideal.Quotient.mk_algebraMap, truncatedExponentChamberMap,
    Ideal.quotientMap_mk, nodeReduction_algebraMap, Ideal.Quotient.mk_algebraMap]

/-- Coefficient change and cutoff reduction commute with the chamber dictionary. -/
theorem truncatedExponentChamberMap_equiv (a : ExponentOrderQuotient K k i) :
    truncatedExponentChamberMap φ hl i (truncatedExponentChamberEquiv K k i a) =
      truncatedExponentChamberEquiv K' l i (exponentOrderMap φ hl i a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedExponentChamberEquiv_mk, truncatedExponentChamberMap_mk,
    exponentOrderMap_mk, truncatedExponentChamberEquiv_mk,
    exponentPolynomialEquiv_mapRingHom]
  simp only [MvPolynomial.map_map, ← mapRingHom_comp]
  have h : (AdjoinRoot.map φ (Polynomial.X ^ (k + 1)) (Polynomial.X ^ (l + 1))
      (by simpa using (pow_dvd_pow (Polynomial.X : Polynomial K')
        (Nat.add_le_add_right hl 1)))).comp (AdjoinRoot.of _) =
      (AdjoinRoot.of _).comp φ := by
    ext r
    simp
  rw [h]

/-- The inverse chamber dictionary commutes with the same reductions. -/
theorem truncatedExponentChamberEquiv_symm_map (a : TruncatedExponentChamber K k i) :
    (truncatedExponentChamberEquiv K' l i).symm (truncatedExponentChamberMap φ hl i a) =
      exponentOrderMap φ hl i ((truncatedExponentChamberEquiv K k i).symm a) := by
  apply (truncatedExponentChamberEquiv K' l i).injective
  simp only [AlgEquiv.apply_symm_apply, ← truncatedExponentChamberMap_equiv]

/-- Identity coefficient change at a fixed order fixes the nodal chamber. -/
@[simp]
theorem truncatedExponentChamberMap_id :
    truncatedExponentChamberMap (RingHom.id K) (k := k) le_rfl i = RingHom.id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := (truncatedExponentChamberEquiv K k i).surjective z
  simp [truncatedExponentChamberMap_equiv]

/-- Nodal chamber reductions respect composition of coefficients and cutoffs. -/
theorem truncatedExponentChamberMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (truncatedExponentChamberMap ψ hm i).comp (truncatedExponentChamberMap φ hl i) =
      truncatedExponentChamberMap (ψ.comp φ) (hm.trans hl) i := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := (truncatedExponentChamberEquiv K k i).surjective z
  simp only [RingHom.comp_apply, truncatedExponentChamberMap_equiv]
  exact congrArg (truncatedExponentChamberEquiv K'' m i)
    (RingHom.congr_fun (exponentOrderMap_comp φ hl i ψ hm) a)

/-- A surjective coefficient map gives a surjective nodal chamber reduction. -/
theorem truncatedExponentChamberMap_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (truncatedExponentChamberMap φ hl i) := by
  intro z
  obtain ⟨a, ha⟩ := exponentOrderMap_surjective φ hl i hφ
    ((truncatedExponentChamberEquiv K' l i).symm z)
  refine ⟨truncatedExponentChamberEquiv K k i a, ?_⟩
  rw [truncatedExponentChamberMap_equiv, ha, AlgEquiv.apply_symm_apply]

end Mei.FocusFocus
