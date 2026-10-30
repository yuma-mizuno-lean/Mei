/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.OrderQuotient
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Algebra
public import Mei.RingTheory.AdjoinRoot.Laurent

/-!
# Naturality of the focus-focus chamber dictionary

Coefficient homomorphisms and reductions of the chamber order act on both the
absolute exponent quotients and the nodal chambers over truncated polynomial
scalars. The comparison `truncatedExponentChamberEquiv` intertwines these maps.
Thus the chamber dictionary compares quotient towers, rather than only their
individual rings. The same reductions on the fiber-product slab act by the
two chamber reductions and respect identity, composition and the nodal comparison.

We use Mathlib's `AdjoinRoot.map`, `Ideal.quotientMap` and coefficient maps of
monoid algebras, and `Mei.NodeAlgebra.mapOfEq` with the chamber maps
`Mei.NodeAlgebra.rightChamberMap` and `Mei.NodeAlgebra.leftChamberMap`, and
`Mei.NodeAlgebra.slabAlgebraMap` on the fiber product. The coordinates
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra Mei.NodeAlgebra _root_.LaurentPolynomial
open _root_.Mei.LaurentPolynomial
open scoped _root_.LaurentPolynomial Mei.NodeAlgebra

variable {K K' K'' : Type*} [CommRing K] [CommRing K'] [CommRing K'']
  {k l m : ℕ} (φ : K →+* K') (hl : l ≤ k) (i : Fin 2)

/-- Change coefficients and lower the order in the absolute exponent quotient. -/
def exponentOrderMap : ExponentOrderQuotient K k i →+* ExponentOrderQuotient K' l i :=
  Ideal.quotientMap _ (mapRingHom exponentMonoid φ) (by
    simpa [Ideal.span_le, Ideal.mem_span_singleton] using
      pow_dvd_pow (single (![xDegree, yDegree] i) (1 : K')) (by omega : l + 1 ≤ k + 1))

/-- The absolute quotient map acts coefficientwise on every representative. -/
@[simp]
theorem exponentOrderMap_mk (a : AddMonoidAlgebra K exponentMonoid) :
    exponentOrderMap φ hl i (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (mapRingHom exponentMonoid φ a) :=
  Ideal.quotientMap_mk

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

/-- Change coefficients and reduce the order in the nodal chamber. The truncated
scalar parameter is reduced by `AdjoinRoot.map`, and both node coordinates are fixed.
This is `Mei.NodeAlgebra.rightChamberMap` for `i = 0` and
`Mei.NodeAlgebra.leftChamberMap` for `i = 1`. -/
def truncatedExponentChamberMap :
    TruncatedExponentChamber K k i →+* TruncatedExponentChamber K' l i :=
  letI : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
  match i with
  | 0 => (Mei.NodeAlgebra.rightChamberMap _ (truncatedScalarMap_C_root φ hl) hl).toRingHom
  | 1 => (Mei.NodeAlgebra.leftChamberMap _ (truncatedScalarMap_C_root φ hl) hl).toRingHom

/-- The left nodal chamber reduction is the canonical quotient reduction. -/
theorem truncatedExponentChamberMap_one :
    truncatedExponentChamberMap φ hl 1 =
      (letI : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
       (Mei.NodeAlgebra.leftChamberMap (_root_.LaurentPolynomial.C τ)
         (truncatedScalarMap_C_root φ hl) hl).toRingHom) := (rfl)

/-- The right nodal chamber reduction is the canonical quotient reduction. -/
theorem truncatedExponentChamberMap_zero :
    truncatedExponentChamberMap φ hl 0 =
      (letI : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
       (Mei.NodeAlgebra.rightChamberMap (_root_.LaurentPolynomial.C τ)
         (truncatedScalarMap_C_root φ hl) hl).toRingHom) := (rfl)

/-- Both nodal coordinates retain their quotient classes. -/
@[simp]
theorem truncatedExponentChamberMap_coord (j : Fin 2) :
    truncatedExponentChamberMap φ hl i
        (Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j)) =
      Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ') j) := by
  let : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
  match i with
  | 0 =>
    exact (Mei.NodeAlgebra.rightChamberMap_mk _ (truncatedScalarMap_C_root φ hl) hl _).trans
      (congrArg _ (Mei.NodeAlgebra.mapOfEq_coord _ _ j))
  | 1 =>
    exact (Mei.NodeAlgebra.leftChamberMap_mk _ (truncatedScalarMap_C_root φ hl) hl _).trans
      (congrArg _ (Mei.NodeAlgebra.mapOfEq_coord _ _ j))

/-- The coefficient Laurent algebra is reduced by `Mei.LaurentPolynomial.truncatedScalarMap`. -/
@[simp]
theorem truncatedExponentChamberMap_algebraMap (a : S[ℤ]) :
    truncatedExponentChamberMap φ hl i (algebraMap S[ℤ] _ a) =
      algebraMap S'[ℤ] _ (truncatedScalarMap φ hl a) := by
  let : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
  match i with
  | 0 =>
    exact ((Mei.NodeAlgebra.rightChamberMap _ (truncatedScalarMap_C_root φ hl) hl).commutes a).trans
      (IsScalarTower.algebraMap_apply S[ℤ] S'[ℤ] _ a)
  | 1 =>
    exact ((Mei.NodeAlgebra.leftChamberMap _ (truncatedScalarMap_C_root φ hl) hl).commutes a).trans
      (IsScalarTower.algebraMap_apply S[ℤ] S'[ℤ] _ a)

/-- On polynomial representatives the nodal chamber map changes only coefficients. -/
@[simp]
theorem truncatedExponentChamberMap_mk (p : MvPolynomial (Fin 2) S[ℤ]) :
    truncatedExponentChamberMap φ hl i
        (Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ) p)) =
      Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ')
        (MvPolynomial.map (truncatedScalarMap φ hl) p)) := by
  have h : (truncatedExponentChamberMap φ hl i).comp ((Ideal.Quotient.mk _).comp
      (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)).toRingHom) =
      ((Ideal.Quotient.mk _).comp (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ')).toRingHom).comp
        (MvPolynomial.map (truncatedScalarMap φ hl)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp
  exact RingHom.congr_fun h p

/-- Coefficient change and cutoff reduction commute with the chamber dictionary. -/
@[simp]
theorem truncatedExponentChamberMap_equiv (a : ExponentOrderQuotient K k i) :
    truncatedExponentChamberMap φ hl i (truncatedExponentChamberEquiv K k i a) =
      truncatedExponentChamberEquiv K' l i (exponentOrderMap φ hl i a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [truncatedExponentChamberEquiv_mk, truncatedExponentChamberMap_mk,
    exponentOrderMap_mk, truncatedExponentChamberEquiv_mk,
    exponentPolynomialEquiv_mapRingHom]
  have h : (truncatedScalarMap φ hl).comp (mapRingHom ℤ (AdjoinRoot.of _)) =
      (mapRingHom ℤ (AdjoinRoot.of _)).comp (mapRingHom ℤ φ) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, ← _root_.LaurentPolynomial.single_eq_C, mapRingHom_single]
        using truncatedScalarMap_C_of φ hl r
    · intro n
      simpa only [RingHom.comp_apply, mapRingHom_single, map_one, _root_.LaurentPolynomial.T]
        using truncatedScalarMap_T φ hl n
  simp only [MvPolynomial.map_map, h]

/-- The inverse chamber dictionary commutes with the same reductions. -/
@[simp]
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

/-- Coefficient change and cutoff reduction on the focus-focus fiber product,
using the same scalar reduction as on its two chamber factors. -/
def truncatedSlabMap :
    slabAlgebra (C τ) (1 + T 1) k →+* slabAlgebra (C τ') (1 + T 1) l :=
  letI : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
  (slabAlgebraMap (C τ) (1 + T 1) (truncatedScalarMap_C_root φ hl)
    (by simp [RingHom.algebraMap_toAlgebra]) hl).toRingHom

/-- The slab reduction acts on the first factor by the left chamber reduction. -/
@[simp]
theorem truncatedSlabMap_fst (z : slabAlgebra (C τ) (1 + T 1) k) :
    (truncatedSlabMap φ hl z).val.1 = truncatedExponentChamberMap φ hl 1 z.val.1 := by
  simp only [truncatedSlabMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_slabAlgebraMap,
    truncatedExponentChamberMap_one]

/-- The slab reduction acts on the second factor by the right chamber reduction. -/
@[simp]
theorem truncatedSlabMap_snd (z : slabAlgebra (C τ) (1 + T 1) k) :
    (truncatedSlabMap φ hl z).val.2 = truncatedExponentChamberMap φ hl 0 z.val.2 := by
  simp only [truncatedSlabMap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, coe_slabAlgebraMap,
    truncatedExponentChamberMap_zero]

/-- The slab reduction fixes the fiber product when coefficients and cutoff agree. -/
@[simp]
theorem truncatedSlabMap_id :
    truncatedSlabMap (RingHom.id K) (k := k) le_rfl = RingHom.id _ := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext <;> simp

/-- Successive coefficient changes and cutoff reductions compose on the slab. -/
theorem truncatedSlabMap_comp (ψ : K' →+* K'') (hm : m ≤ l) :
    (truncatedSlabMap ψ hm).comp (truncatedSlabMap φ hl) =
      truncatedSlabMap (ψ.comp φ) (hm.trans hl) := by
  ext z : 1
  apply Subtype.ext
  apply Prod.ext <;>
    simp only [RingHom.comp_apply, truncatedSlabMap_fst, truncatedSlabMap_snd]
  · exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 1 ψ hm) z.val.1
  · exact RingHom.congr_fun (truncatedExponentChamberMap_comp φ hl 0 ψ hm) z.val.2

/-- Reduction commutes with the comparison from the nodal algebra to the slab. -/
theorem truncatedSlabMap_toSlabAlgebra (z : NodeAlgebra S[ℤ] (C τ * (1 + T 1))) :
    truncatedSlabMap φ hl (toSlabAlgebra (C τ) (1 + T 1) k z) =
      toSlabAlgebra (C τ') (1 + T 1) l
        (letI : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
         mapOfEq (C τ * (1 + T 1)) (by simp [RingHom.algebraMap_toAlgebra]) z) := by
  let : Algebra S[ℤ] S'[ℤ] := RingHom.toAlgebra (truncatedScalarMap φ hl)
  exact slabAlgebraMap_toSlabAlgebra (C τ) (1 + T 1)
    (truncatedScalarMap_C_root φ hl) (by simp [RingHom.algebraMap_toAlgebra]) hl z

/-- The inverse slab dictionary commutes with coefficient changes and cutoff
reductions, on every matching pair. -/
@[simp↓]
theorem algebraEquiv_symm_truncatedSlabMap
    (z : slabAlgebra (C τ) (1 + T 1) k) :
    (algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))).symm
        (truncatedSlabMap φ hl z) =
      (letI : Algebra S[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
       mapOfEq (C τ * (1 + T 1))
         (by simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
           truncatedScalarMap_C_root, truncatedScalarMap_T])
         ((algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))).symm z)) := by
  apply (algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))).symm_apply_eq.mpr
  let e := algebraEquiv τ k (AdjoinRoot.root_X_pow_pow (k + 1))
  let e' := algebraEquiv τ' l (AdjoinRoot.root_X_pow_pow (l + 1))
  let : Algebra S[ℤ] S'[ℤ] := (truncatedScalarMap φ hl).toAlgebra
  let htf : algebraMap S[ℤ] S'[ℤ] (C τ * (1 + T 1)) =
      C τ' * (1 + T 1) := by
    simp only [map_mul, map_add, map_one, RingHom.algebraMap_toAlgebra,
      truncatedScalarMap_C_root, truncatedScalarMap_T]
  have he : truncatedSlabMap φ hl (e (e.symm z)) =
      e' (mapOfEq (C τ * (1 + T 1)) htf (e.symm z)) := by
    simpa only [e, e', algebraEquiv_apply] using
      truncatedSlabMap_toSlabAlgebra φ hl (e.symm z)
  simpa only [AlgEquiv.apply_symm_apply] using he

end Mei.FocusFocus
