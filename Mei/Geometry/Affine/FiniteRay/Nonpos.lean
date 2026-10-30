/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# Normalizing bends at the endpoint

A finite hinge presentation with nonpositive bend times determines a finite affine
ray on the negative half-line. The increment at time zero is absorbed into the
final direction, leaving only strictly negative bends. This normalization handles
segments that collapse onto the endpoint in a limiting family. It preserves the
incoming affine line, while choosing the affine continuation past the endpoint
using the new final direction.

The construction uses `FiniteAffineRay` and Mathlib's `Finsupp.erase` and
`Finsupp.add_sum_erase'`.
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V]

/-- Normalize a finite hinge presentation with nonpositive bend times by absorbing
the increment at time zero into the final direction. -/
def ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) : FiniteAffineRay V P := by
  classical
  exact
    { endpoint := Q
      direction := v + b 0
      bends := b.erase 0
      bend_neg := fun t ht =>
        lt_of_le_of_ne (hb t (Finset.mem_erase.mp ht).2) (Finset.mem_erase.mp ht).1 }

/-- Normalization retains the endpoint. -/
@[simp]
theorem endpoint_ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) : (ofNonposBends Q v b hb).endpoint = Q := (rfl)

/-- The time-zero increment becomes part of the final direction. -/
@[simp]
theorem direction_ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) :
    (ofNonposBends Q v b hb).direction = v + b 0 := (rfl)

/-- Only the time-zero bend is removed. Coincident increments are already added
in the finitely supported bend data. -/
@[simp]
theorem bends_ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) :
    (ofNonposBends Q v b hb).bends = b.erase 0 := (rfl)

variable [Module ℝ V] [AddTorsor V P]

/-- On the negative half-line normalization realizes the original hinge formula,
including the possible time-zero hinge. -/
theorem ofNonposBends_apply (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) {t : ℝ} (ht : t ≤ 0) :
    ofNonposBends Q v b hb t =
      (b.sum (fun s w => max (s - t) 0 • w) - t • v) +ᵥ Q := by
  classical
  rw [eval_def, bends_ofNonposBends, direction_ofNonposBends,
    ← Finsupp.add_sum_erase' b 0 (fun s w => max (s - t) 0 • w) (fun _ => smul_zero _)]
  congr 1
  rw [zero_sub, max_eq_left (neg_nonneg.mpr ht), smul_add, neg_smul]
  abel

omit [Module ℝ V] [AddTorsor V P] in
/-- Normalization preserves the total incoming direction. -/
@[simp]
theorem incomingDirection_ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) :
    (ofNonposBends Q v b hb).incomingDirection = v + b.sum (fun _ w => w) := by
  rw [incomingDirection_def, direction_ofNonposBends, bends_ofNonposBends,
    ← Finsupp.add_sum_erase' b 0 (fun _ w => w) (fun _ => rfl), add_assoc]

/-- Removing a bend at time zero leaves the incoming affine reference unchanged. -/
@[simp]
theorem incomingReference_ofNonposBends (Q : P) (v : V) (b : ℝ →₀ V)
    (hb : ∀ t ∈ b.support, t ≤ 0) :
    (ofNonposBends Q v b hb).incomingReference = b.sum (fun s w => s • w) +ᵥ Q := by
  rw [incomingReference_def, endpoint_ofNonposBends, bends_ofNonposBends,
    ← Finsupp.add_sum_erase' b 0 (fun s w => s • w) (fun _ => smul_zero _),
    zero_smul, zero_add]

omit [Module ℝ V] [AddTorsor V P] in
/-- A presentation already having strictly negative bend times is unchanged. -/
@[simp]
theorem ofNonposBends_eq (β : FiniteAffineRay V P) :
    ofNonposBends β.endpoint β.direction β.bends (fun t ht => (β.bend_neg t ht).le) = β := by
  classical
  have hz : 0 ∉ β.bends.support := fun h => (lt_irrefl 0) (β.bend_neg 0 h)
  ext <;> simp [Finsupp.notMem_support_iff.mp hz]

end Mei.FiniteAffineRay
