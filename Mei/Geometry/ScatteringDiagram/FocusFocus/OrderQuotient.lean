/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.MonoidAlgebra

/-!
# Order quotients and the truncated smoothing parameter

The quotient of the focus-focus exponent algebra by a chamber order is the
nodal chamber over `K[t]/(t^(k+1))`. No smoothing relation is imposed on the
original exponent algebra: its smoothing monomial becomes the product `xy`.
Its nilpotence follows from the chamber cutoff. This compares the absolute
monoid presentation with the relative nodal presentation over truncated scalars.

The construction uses `exponentPolynomialEquiv`, `AdjoinRoot.lift` and the
universal properties of the nodal algebra and ideal quotients. The coordinates
follow Gross–Siebert, *An Invitation to Toric Degenerations*, §2.2–2.3
(arXiv:0808.2749v2).
-/

public noncomputable section

namespace Mei.FocusFocus

open TauCeti AddMonoidAlgebra
open scoped LaurentPolynomial Mei.NodeAlgebra

variable (K : Type*) [CommRing K] (k : ℕ) (i : Fin 2)

/-- The original exponent algebra truncated by the left (`i=1`) or right
(`i=0`) chamber order. -/
abbrev ExponentOrderQuotient :=
  AddMonoidAlgebra K exponentMonoid ⧸
    Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)}

/-- The same chamber expressed over truncated polynomial scalars. -/
abbrev TruncatedExponentChamber :=
  NodeAlgebra (AddMonoidAlgebra (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) ℤ)
      (_root_.LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K))) ⧸
    Ideal.span {(NodeAlgebra.coord
      (_root_.LaurentPolynomial.C (AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)) :
        AddMonoidAlgebra (AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)) ℤ) i) ^ (k + 1)}

local notation "S" => AdjoinRoot (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "τ" => AdjoinRoot.root (Polynomial.X ^ (k + 1) : Polynomial K)
local notation "π" => Ideal.Quotient.mk
  (Ideal.span {(single (![xDegree, yDegree] i) (1 : K)) ^ (k + 1)})

private def toChamber : AddMonoidAlgebra K exponentMonoid →+*
    TruncatedExponentChamber K k i :=
  (Ideal.Quotient.mk _).comp
    ((NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)).toRingHom.comp
      ((MvPolynomial.map (mapRingHom ℤ (AdjoinRoot.of _))).comp
        (exponentPolynomialEquiv K).toAlgHom.toRingHom))

private theorem toChamber_single (q : exponentMonoid) (r : K) :
    toChamber K k i (single q r) =
      Ideal.Quotient.mk _
        (algebraMap S[ℤ] _ (single q.val.2.1 (AdjoinRoot.of _ r)) *
          NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 0 ^ rightOrder q *
          NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 1 ^ leftOrder q) := by
  simp only [toChamber, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom,
    exponentPolynomialEquiv_single,
    MvPolynomial.map_monomial, mapRingHom_single]
  rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]
  simp

private theorem toChamber_single_coord (j : Fin 2) :
    toChamber K k i (single (![xDegree, yDegree] j) 1) =
      Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j) := by
  fin_cases j <;> simp [toChamber]

private def forward : ExponentOrderQuotient K k i →+* TruncatedExponentChamber K k i :=
  Ideal.Quotient.lift _ (toChamber K k i) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, toChamber_single_coord, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), mul_zero])

private def scalarBack : S →+* ExponentOrderQuotient K k i :=
  AdjoinRoot.lift (algebraMap K _) (π (single smoothingDegree 1)) (by
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_span_singleton.mpr
    have he : single smoothingDegree (1 : K) =
        single (![xDegree, yDegree] i) 1 * single (![yDegree, xDegree] i) 1 := by
      fin_cases i <;> simp [single_mul_single, xDegree_add_yDegree, add_comm]
    rw [he, mul_pow]
    exact dvd_mul_right _ _)

private def laurentBack : S[ℤ] →+* ExponentOrderQuotient K k i :=
  liftNCRingHom (scalarBack K k i)
    (((π).toMonoidHom.comp (of K exponentMonoid)).comp
      (AddMonoidHom.toMultiplicative tangentDegree)) (fun _ _ => Commute.all _ _)

private theorem laurentBack_single (b : ℤ) (r : S) :
    laurentBack K k i (single b r) =
      scalarBack K k i r * π (single (tangentDegree b) 1) := by
  simp only [laurentBack, liftNCRingHom_single, MonoidHom.comp_apply,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd, of_apply]
  rfl

private def nodeBack :
    NodeAlgebra S[ℤ] (_root_.LaurentPolynomial.C τ) →+*
      ExponentOrderQuotient K k i := by
  letI : Algebra S[ℤ] (ExponentOrderQuotient K k i) :=
    (laurentBack K k i).toAlgebra
  exact (NodeAlgebra.lift _
    (π (single xDegree 1)) (π (single yDegree 1)) (by
      rw [RingHom.algebraMap_toAlgebra, ← _root_.LaurentPolynomial.single_eq_C, laurentBack_single]
      simp only [scalarBack, AdjoinRoot.lift_root, tangentDegree.map_zero, ← one_def,
        map_one, mul_one]
      rw [← map_mul, single_mul_single, one_mul, xDegree_add_yDegree])).toRingHom

private theorem nodeBack_coord (j : Fin 2) :
    nodeBack K k i (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j) =
      π (single (![xDegree, yDegree] j) 1) := by
  fin_cases j <;> simp [nodeBack, NodeAlgebra.lift_coord]

private theorem nodeBack_algebraMap (p : S[ℤ]) :
    nodeBack K k i (algebraMap _ _ p) = laurentBack K k i p := by
  simp only [nodeBack, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
    RingHom.algebraMap_toAlgebra]

private def backward : TruncatedExponentChamber K k i →+* ExponentOrderQuotient K k i :=
  Ideal.Quotient.lift _ (nodeBack K k i) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, nodeBack_coord, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), mul_zero])

private theorem backward_toChamber_single (q : exponentMonoid) (r : K) :
    backward K k i (toChamber K k i (single q r)) = π (single q r) := by
  rw [toChamber_single, backward, Ideal.Quotient.lift_mk]
  simp only [map_mul, map_pow, nodeBack_algebraMap, laurentBack_single, scalarBack,
    AdjoinRoot.lift_of, nodeBack_coord, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hs : algebraMap K (ExponentOrderQuotient K k i) r =
      π (single 0 r) := by
    -- The quotient scalar map is the composite of the monoid-algebra scalar map.
    rfl
  rw [hs]
  simp only [← map_pow, ← map_mul]
  congr 1
  simp only [single_pow, one_pow, single_mul_single, mul_one]
  congr 1
  apply exponentEquiv.injective
  simp only [map_add, map_nsmul, exponentEquiv_apply, coe_tangentDegree,
    coe_xDegree, coe_yDegree, leftOrder_apply, rightOrder_apply]
  ext <;> simp

private theorem forward_scalarBack (r : S) :
    forward K k i (scalarBack K k i r) = algebraMap S (TruncatedExponentChamber K k i) r := by
  have he : (forward K k i).comp (scalarBack K k i) =
      algebraMap S (TruncatedExponentChamber K k i) := by
    apply AdjoinRoot.ringHom_ext
    · ext r
      simp only [RingHom.comp_apply, scalarBack, AdjoinRoot.lift_of]
      have hs : algebraMap K (ExponentOrderQuotient K k i) r =
          π (single 0 r) := by
        -- The quotient scalar map is the composite coefficient map.
        rfl
      rw [hs]
      have hC : mapRingHom ℤ (AdjoinRoot.of _) (_root_.LaurentPolynomial.C r) =
          algebraMap S S[ℤ] (AdjoinRoot.of (Polynomial.X ^ (k + 1)) r) := by
        simp only [← _root_.LaurentPolynomial.single_eq_C, mapRingHom_single,
          coe_algebraMap, Function.comp_apply]
        rfl
      have h := congrArg (algebraMap S[ℤ] (TruncatedExponentChamber K k i)) hC
      rw [← IsScalarTower.algebraMap_apply S S[ℤ]] at h
      simpa [forward, toChamber] using h
    · simp only [RingHom.comp_apply, scalarBack, AdjoinRoot.lift_root,
        forward, Ideal.Quotient.lift_mk]
      have hS : algebraMap S[ℤ] (TruncatedExponentChamber K k i)
          (_root_.LaurentPolynomial.C τ) = algebraMap S (TruncatedExponentChamber K k i) τ := by
        rw [IsScalarTower.algebraMap_apply S S[ℤ]]
        rfl
      simpa [toChamber] using hS
  exact RingHom.congr_fun he r

private theorem forward_laurentBack (p : S[ℤ]) :
    forward K k i (laurentBack K k i p) =
      Ideal.Quotient.mk _ (algebraMap _ _ p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single b r =>
    rw [laurentBack_single, map_mul, forward_scalarBack]
    simp only [forward, Ideal.Quotient.lift_mk, toChamber_single,
      coe_tangentDegree, rightOrder_apply, leftOrder_apply, Int.toNat_zero, pow_zero,
      mul_one, map_one]
    rw [IsScalarTower.algebraMap_apply S S[ℤ]]
    simp only [← Ideal.Quotient.mk_algebraMap, ← map_mul]
    congr 1
    simp [← map_mul]

private theorem forward_nodeBack (z :
    NodeAlgebra S[ℤ] (_root_.LaurentPolynomial.C τ)) :
    forward K k i (nodeBack K k i z) = Ideal.Quotient.mk _ z := by
  have he : ((forward K k i).comp (nodeBack K k i)).comp
      (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)).toRingHom =
      (Ideal.Quotient.mk _).comp
        (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
      rw [nodeBack_algebraMap, forward_laurentBack]
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        NodeAlgebra.mk_X, nodeBack_coord, forward, Ideal.Quotient.lift_mk,
        toChamber_single_coord]
  obtain ⟨p, rfl⟩ := NodeAlgebra.mk_surjective (_root_.LaurentPolynomial.C τ) z
  exact RingHom.congr_fun he p

private def orderRingEquiv :
    ExponentOrderQuotient K k i ≃+* TruncatedExponentChamber K k i :=
  RingEquiv.ofRingHom (forward K k i) (backward K k i)
    (by
      apply RingHom.ext
      intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact forward_nodeBack K k i z)
    (by
      apply RingHom.ext
      intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      induction z using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
      | single q r => exact backward_toChamber_single K k i q r)

/-- The absolute monoid order quotient is the nodal chamber over
`K[t]/(t^(k+1))`, in either chamber and over every commutative coefficient ring. -/
def truncatedExponentChamberEquiv :
    ExponentOrderQuotient K k i ≃ₐ[K] TruncatedExponentChamber K k i :=
  AlgEquiv.ofRingEquiv (f := orderRingEquiv K k i) (by
    intro r
    have hs : algebraMap K (ExponentOrderQuotient K k i) r =
        π (single 0 r) := by
      -- The quotient scalar map is the composite coefficient map.
      rfl
    rw [hs]
    have hC : mapRingHom ℤ (AdjoinRoot.of _) (_root_.LaurentPolynomial.C r) =
        algebraMap K S[ℤ] r := by
      simp only [← _root_.LaurentPolynomial.single_eq_C, mapRingHom_single,
        coe_algebraMap, Function.comp_apply, AdjoinRoot.algebraMap_eq]
    have h := congrArg (algebraMap S[ℤ] (TruncatedExponentChamber K k i)) hC
    rw [← IsScalarTower.algebraMap_apply K S[ℤ]] at h
    simpa [orderRingEquiv, forward, toChamber] using h)

/-- On arbitrary representatives, the comparison is the polynomial dictionary,
coefficient reduction, and the nodal and chamber quotient maps. -/
@[simp]
theorem truncatedExponentChamberEquiv_mk (a : AddMonoidAlgebra K exponentMonoid) :
    truncatedExponentChamberEquiv K k i (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (NodeAlgebra.mk (_root_.LaurentPolynomial.C τ)
        (MvPolynomial.map (mapRingHom ℤ (AdjoinRoot.of _))
          (exponentPolynomialEquiv K a))) := (rfl)

/-- A monomial retains its Laurent exponent and both coordinate multiplicities. -/
theorem truncatedExponentChamberEquiv_single (q : exponentMonoid) (r : K) :
    truncatedExponentChamberEquiv K k i (Ideal.Quotient.mk _ (single q r)) =
      Ideal.Quotient.mk _
        (algebraMap S[ℤ] _ (single q.val.2.1 (AdjoinRoot.of _ r)) *
          NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 0 ^ rightOrder q *
          NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) 1 ^ leftOrder q) :=
  toChamber_single K k i q r

/-- The inverse sends each nodal coordinate to its original monomial class. -/
@[simp]
theorem truncatedExponentChamberEquiv_symm_coord (j : Fin 2) :
    (truncatedExponentChamberEquiv K k i).symm
        (Ideal.Quotient.mk _ (NodeAlgebra.coord (_root_.LaurentPolynomial.C τ) j)) =
      Ideal.Quotient.mk _ (single (![xDegree, yDegree] j) 1) := by
  apply (truncatedExponentChamberEquiv K k i).symm_apply_eq.mpr
  exact (toChamber_single_coord K k i j).symm

/-- A truncated scalar polynomial is evaluated at the original smoothing
monomial by the inverse comparison. -/
@[simp]
theorem truncatedExponentChamberEquiv_symm_scalar_mk (p : Polynomial K) :
    (truncatedExponentChamberEquiv K k i).symm
        (algebraMap S (TruncatedExponentChamber K k i) (AdjoinRoot.mk _ p)) =
      p.eval₂ (algebraMap K (ExponentOrderQuotient K k i))
        (π (single smoothingDegree 1)) := by
  apply (truncatedExponentChamberEquiv K k i).symm_apply_eq.mpr
  simpa only [scalarBack, AdjoinRoot.lift_mk, truncatedExponentChamberEquiv,
    AlgEquiv.ofRingEquiv_apply, orderRingEquiv, RingEquiv.ofRingHom_apply] using
    (forward_scalarBack K k i (AdjoinRoot.mk _ p)).symm

/-- The inverse identifies the truncated scalar parameter with the smoothing
monomial, rather than with an independent generator. -/
@[simp]
theorem truncatedExponentChamberEquiv_symm_parameter :
    (truncatedExponentChamberEquiv K k i).symm
        (algebraMap S (TruncatedExponentChamber K k i) τ) =
      Ideal.Quotient.mk _ (single smoothingDegree 1) := by
  apply (truncatedExponentChamberEquiv K k i).symm_apply_eq.mpr
  rw [truncatedExponentChamberEquiv_mk]
  simp only [exponentPolynomialEquiv_smoothingDegree, map_mul, MvPolynomial.map_X,
    NodeAlgebra.mk_X, NodeAlgebra.coord_zero_mul_coord_one, Ideal.Quotient.mk_algebraMap]
  rw [IsScalarTower.algebraMap_apply S S[ℤ]]
  rfl

/-- The inverse fixes all tangential Laurent monomials. -/
@[simp]
theorem truncatedExponentChamberEquiv_symm_tangent (b : ℤ) :
    (truncatedExponentChamberEquiv K k i).symm
        (algebraMap S[ℤ] (TruncatedExponentChamber K k i) (_root_.LaurentPolynomial.T b)) =
      Ideal.Quotient.mk _ (single (tangentDegree b) 1) := by
  apply (truncatedExponentChamberEquiv K k i).symm_apply_eq.mpr
  rw [truncatedExponentChamberEquiv_single]
  simp only [coe_tangentDegree, rightOrder_apply, leftOrder_apply, sub_self,
    Int.toNat_zero, pow_zero, mul_one, map_one, Ideal.Quotient.mk_algebraMap]
  rfl

end Mei.FocusFocus
