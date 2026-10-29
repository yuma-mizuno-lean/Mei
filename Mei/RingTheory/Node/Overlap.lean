/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Gluing

/-!
# Unit twists of truncated nodal overlaps

The overlap `R[x,y]/(xy-t, x^(k+1), y^(k+1))` admits the coordinate change
`x ↦ ux`, `y ↦ u⁻¹y` for every scalar unit `u`. More generally, an overlap map
into a commutative algebra can be twisted by a unit in that algebra. This permits
comparison of slab gluing maps in a common localized overlap, even when their wall
functions are not units before localization.

We use `TauCeti.NodeAlgebra.lift` and `Ideal.Quotient.liftₐ`. The overlap model
and its unit changes of coordinates follow Gross–Siebert, *An Invitation to Toric
Degenerations*, §2.3, arXiv:0808.2749v2.
-/

public noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra

variable {R A : Type*} [CommRing R] [CommSemiring A] [Algebra R A]
  (t : R) (k : ℕ)

/-- Both overlap coordinates vanish to order `k + 1`. -/
@[simp]
theorem overlap_mk_coord_pow_succ (i : Fin 2) :
    (Ideal.Quotient.mk _ (coord t i) : Overlap t k) ^ (k + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  fin_cases i <;> exact Ideal.subset_span (by simp)

private def twistOverlapLift (φ : Overlap t k →ₐ[R] A) (u : Aˣ) :
    NodeAlgebra R t →ₐ[R] A :=
  lift t (u * φ (Ideal.Quotient.mk _ (coord t 0)))
    (↑u⁻¹ * φ (Ideal.Quotient.mk _ (coord t 1))) (by
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, ← map_mul,
        coord_zero_mul_coord_one, Ideal.Quotient.mk_algebraMap, AlgHom.commutes])

private theorem twistOverlapLift_eq_zero (φ : Overlap t k →ₐ[R] A) (u : Aˣ) :
    ∀ z ∈ Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)},
      twistOverlapLift t k φ u z = 0 := by
  have hker : Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} ≤
      RingHom.ker (twistOverlapLift t k φ u) := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · apply (RingHom.mem_ker (f := (twistOverlapLift t k φ u).toRingHom)).mpr
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow,
        twistOverlapLift, lift_coord_zero, mul_pow]
      rw [← map_pow, overlap_mk_coord_pow_succ, map_zero, mul_zero]
    · obtain rfl := Set.mem_singleton_iff.mp hz
      apply (RingHom.mem_ker (f := (twistOverlapLift t k φ u).toRingHom)).mpr
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_pow,
        twistOverlapLift, lift_coord_one, mul_pow]
      rw [← map_pow, overlap_mk_coord_pow_succ, map_zero, mul_zero]
  exact fun z hz => hker hz

/-- Twist a map from the truncated nodal overlap by `x ↦ ux`, `y ↦ u⁻¹y`.
The unit may exist only in the target algebra. -/
def twistOverlap (φ : Overlap t k →ₐ[R] A) (u : Aˣ) : Overlap t k →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (twistOverlapLift t k φ u) (twistOverlapLift_eq_zero t k φ u)

private theorem twistOverlap_mk (φ : Overlap t k →ₐ[R] A) (u : Aˣ)
    (z : NodeAlgebra R t) :
    twistOverlap t k φ u (Ideal.Quotient.mk _ z) = twistOverlapLift t k φ u z :=
  AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp _ _ (twistOverlapLift_eq_zero t k φ u)) z

/-- The first overlap coordinate is multiplied by the twisting unit. -/
@[simp]
theorem twistOverlap_mk_coord_zero (φ : Overlap t k →ₐ[R] A) (u : Aˣ) :
    twistOverlap t k φ u (Ideal.Quotient.mk _ (coord t 0)) =
      u * φ (Ideal.Quotient.mk _ (coord t 0)) := by
  rw [twistOverlap_mk, twistOverlapLift, lift_coord_zero]

/-- The second overlap coordinate is multiplied by the inverse twisting unit. -/
@[simp]
theorem twistOverlap_mk_coord_one (φ : Overlap t k →ₐ[R] A) (u : Aˣ) :
    twistOverlap t k φ u (Ideal.Quotient.mk _ (coord t 1)) =
      ↑u⁻¹ * φ (Ideal.Quotient.mk _ (coord t 1)) := by
  rw [twistOverlap_mk, twistOverlapLift, lift_coord_one]

/-- Twisting by one leaves the overlap map unchanged. -/
@[simp]
theorem twistOverlap_one (φ : Overlap t k →ₐ[R] A) : twistOverlap t k φ 1 = φ := by
  apply Ideal.Quotient.algHom_ext
  ext <;> simp

/-- Composing with a scalar coordinate twist multiplies the target twisting unit
by the image of the scalar unit. -/
theorem twistOverlap_comp (φ : Overlap t k →ₐ[R] A) (u : Aˣ) (v : Rˣ) :
    (twistOverlap t k φ u).comp
        (twistOverlap t k (AlgHom.id R _) (Units.map (algebraMap R (Overlap t k)).toMonoidHom v)) =
      twistOverlap t k φ (u * Units.map (algebraMap R A).toMonoidHom v) := by
  apply Ideal.Quotient.algHom_ext
  ext <;> simp [mul_assoc, mul_left_comm, mul_comm]

/-- A scalar unit gives an automorphism of the truncated overlap, with inverse
the twist by its inverse. -/
def scaleOverlap (u : Rˣ) : Overlap t k ≃ₐ[R] Overlap t k :=
  AlgEquiv.ofAlgHom
    (twistOverlap t k (AlgHom.id R _) (Units.map (algebraMap R (Overlap t k)).toMonoidHom u))
    (twistOverlap t k (AlgHom.id R _) (Units.map (algebraMap R (Overlap t k)).toMonoidHom u⁻¹))
    (by rw [twistOverlap_comp]; simp)
    (by rw [twistOverlap_comp]; simp)

/-- The scalar overlap automorphism has the underlying unit twist. -/
@[simp]
theorem scaleOverlap_toAlgHom (u : Rˣ) :
    (scaleOverlap t k u).toAlgHom =
      twistOverlap t k (AlgHom.id R _)
        (Units.map (algebraMap R (Overlap t k)).toMonoidHom u) := (rfl)

/-- Scaling the first coordinate multiplies it by `u`. -/
@[simp]
theorem scaleOverlap_mk_coord_zero (u : Rˣ) :
    scaleOverlap t k u (Ideal.Quotient.mk _ (coord t 0)) =
      algebraMap R (Overlap t k) u * Ideal.Quotient.mk _ (coord t 0) := by
  exact twistOverlap_mk_coord_zero t k _ _

/-- Scaling the second coordinate multiplies it by `u⁻¹`. -/
@[simp]
theorem scaleOverlap_mk_coord_one (u : Rˣ) :
    scaleOverlap t k u (Ideal.Quotient.mk _ (coord t 1)) =
      algebraMap R (Overlap t k) (↑u⁻¹ : R) * Ideal.Quotient.mk _ (coord t 1) := by
  have h := twistOverlap_mk_coord_one t k (AlgHom.id R _)
    (Units.map (algebraMap R (Overlap t k)).toMonoidHom u)
  rw [← map_inv, Units.coe_map] at h
  exact h

/-- The identity scalar gives the identity overlap automorphism. -/
@[simp]
theorem scaleOverlap_one : scaleOverlap t k (1 : Rˣ) = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  simp

/-- Multiplication of scalar units gives composition of overlap automorphisms. -/
@[simp]
theorem scaleOverlap_mul (u v : Rˣ) :
    scaleOverlap t k (u * v) = (scaleOverlap t k v).trans (scaleOverlap t k u) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply Ideal.Quotient.algHom_ext
  ext <;> simp [mul_assoc, mul_left_comm, mul_comm]

/-- Inverting the scalar unit inverts its overlap automorphism. -/
@[simp]
theorem scaleOverlap_inv (u : Rˣ) :
    scaleOverlap t k u⁻¹ = (scaleOverlap t k u).symm := by
  simp [scaleOverlap, AlgEquiv.ofAlgHom_symm]

end Mei.NodeAlgebra
