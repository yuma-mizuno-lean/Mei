/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Gluing

/-!
# Maps from truncated nodal overlaps

The overlap `R[x,y]/(xy-t, x^(k+1), y^(k+1))` represents pairs of elements
whose product is `t` and whose `(k+1)`st powers vanish. Its evaluation map
and coordinate extensionality let one compare gluing maps without choosing
polynomial representatives. Rescaling the two coordinates by mutually inverse
units gives maps to any algebra over the overlap.

We use `TauCeti.NodeAlgebra.lift` and `Ideal.Quotient.liftₐ` for the two
successive quotients.
-/

public noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra

variable {R A : Type*} [CommRing R] [CommSemiring A] [Algebra R A]
  (t : R) (k : ℕ)

/-- Evaluate a truncated nodal overlap at nilpotent coordinates with product `t`. -/
def overlapLift (x y : A) (hxy : x * y = algebraMap R A t)
    (hx : x ^ (k + 1) = 0) (hy : y ^ (k + 1) = 0) : Overlap t k →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (lift t x y hxy) fun z hz => by
    have hle : Ideal.span {coord t 0 ^ (k + 1), coord t 1 ^ (k + 1)} ≤
        RingHom.ker (lift t x y hxy) := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor <;> simp [RingHom.mem_ker, hx, hy]
    exact RingHom.mem_ker.mp (hle hz)

/-- Evaluation on a nodal representative uses the nodal evaluation map. -/
@[simp]
theorem overlapLift_mk (x y : A) (hxy : x * y = algebraMap R A t)
    (hx : x ^ (k + 1) = 0) (hy : y ^ (k + 1) = 0) (z : NodeAlgebra R t) :
    overlapLift t k x y hxy hx hy (Ideal.Quotient.mk _ z) = lift t x y hxy z := (rfl)

/-- Maps from an overlap are determined by its two coordinates. -/
@[ext]
theorem overlap_hom_ext {φ ψ : Overlap t k →ₐ[R] A}
    (hx : φ (Ideal.Quotient.mk _ (coord t 0)) = ψ (Ideal.Quotient.mk _ (coord t 0)))
    (hy : φ (Ideal.Quotient.mk _ (coord t 1)) = ψ (Ideal.Quotient.mk _ (coord t 1))) :
    φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  exact TauCeti.NodeAlgebra.hom_ext t hx hy

variable [Algebra (Overlap t k) A] [IsScalarTower R (Overlap t k) A]

/-- Rescale the first overlap coordinate by `u` and the second by `u⁻¹`,
then evaluate in an algebra over the overlap. -/
def overlapRescale (u : Aˣ) : Overlap t k →ₐ[R] A :=
  overlapLift t k
    ((u : A) * algebraMap (Overlap t k) A (Ideal.Quotient.mk _ (coord t 0)))
    ((↑u⁻¹ : A) * algebraMap (Overlap t k) A (Ideal.Quotient.mk _ (coord t 1)))
    (by rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, ← map_mul,
          coord_zero_mul_coord_one, Ideal.Quotient.mk_algebraMap,
          ← IsScalarTower.algebraMap_apply])
    (by rw [mul_pow, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (by simp)), map_zero, mul_zero])
    (by rw [mul_pow, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (by simp)), map_zero, mul_zero])

/-- Rescaling multiplies the first coordinate by the unit. -/
@[simp]
theorem overlapRescale_coord_zero (u : Aˣ) :
    overlapRescale t k u (Ideal.Quotient.mk _ (coord t 0)) =
      (u : A) * algebraMap (Overlap t k) A (Ideal.Quotient.mk _ (coord t 0)) := by
  simp [overlapRescale]

/-- Rescaling multiplies the second coordinate by the inverse unit. -/
@[simp]
theorem overlapRescale_coord_one (u : Aˣ) :
    overlapRescale t k u (Ideal.Quotient.mk _ (coord t 1)) =
      (↑u⁻¹ : A) * algebraMap (Overlap t k) A (Ideal.Quotient.mk _ (coord t 1)) := by
  simp [overlapRescale]

/-- Unit rescaling recovers the structural map from the overlap. -/
@[simp]
theorem overlapRescale_one :
    overlapRescale t k (1 : Aˣ) = IsScalarTower.toAlgHom R (Overlap t k) A := by
  apply overlap_hom_ext <;> simp

/-- A coefficient-unit rescaling followed by a target-unit rescaling multiplies
those units. The first unit is fixed because it comes from the coefficient ring. -/
theorem overlapRescale_comp (u : Rˣ) (v : Aˣ) :
    (overlapRescale t k v).comp
        (overlapRescale t k (Units.map (algebraMap R (Overlap t k)) u)) =
      overlapRescale t k (Units.map (algebraMap R A) u * v) := by
  apply overlap_hom_ext <;>
    simp [Units.coe_map, map_mul, ← map_inv, mul_assoc, mul_left_comm]

/-- Rescaling by a coefficient unit is an automorphism of the truncated overlap. -/
def overlapRescaleEquiv (u : Rˣ) : Overlap t k ≃ₐ[R] Overlap t k :=
  AlgEquiv.ofAlgHom
    (overlapRescale t k (Units.map (algebraMap R (Overlap t k)) u))
    (overlapRescale t k (Units.map (algebraMap R (Overlap t k)) u⁻¹))
    (by rw [overlapRescale_comp, ← map_mul, inv_mul_cancel, map_one, overlapRescale_one]; rfl)
    (by rw [overlapRescale_comp, ← map_mul, mul_inv_cancel, map_one, overlapRescale_one]; rfl)

/-- The overlap automorphism has the values of coordinate rescaling. -/
@[simp]
theorem overlapRescaleEquiv_apply (u : Rˣ) (z : Overlap t k) :
    overlapRescaleEquiv t k u z =
      overlapRescale t k (Units.map (algebraMap R (Overlap t k)) u) z := (rfl)

/-- The inverse rescaling is given by the inverse coefficient unit. -/
@[simp]
theorem overlapRescaleEquiv_symm (u : Rˣ) :
    (overlapRescaleEquiv t k u).symm = overlapRescaleEquiv t k u⁻¹ := by
  ext z
  rfl

/-- The algebra map underlying the rescaling automorphism. -/
@[simp]
theorem overlapRescaleEquiv_toAlgHom (u : Rˣ) :
    (overlapRescaleEquiv t k u).toAlgHom =
      overlapRescale t k (Units.map (algebraMap R (Overlap t k)) u) := (rfl)

/-- The quotient from the left chamber to the overlap. -/
def leftToOverlap : LeftChamber t k →ₐ[R] Overlap t k :=
  Ideal.Quotient.factorₐ R (Ideal.span_mono (by simp))

/-- The chamber-to-overlap quotient keeps nodal representatives. -/
@[simp]
theorem leftToOverlap_mk (z : NodeAlgebra R t) :
    leftToOverlap t k (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z := (rfl)

end Mei.NodeAlgebra
