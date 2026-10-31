/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# Extending a finite affine ray through a new encounter

Continue a ray for time `s` in its final direction, then for time `t` in a
new direction. All old bends move backwards by `s + t`; the new encounter
occurs at time `-t`. The entire incoming path is preserved by translation of
the time coordinate, including when the new direction equals the old one.

This is the geometric attachment operation for the last-encounter recursion
for broken lines in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5). It uses the hinge realization
and direction increments of `FiniteAffineRay`.
-/

public noncomputable section

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Continue in the old direction for time `s`, then in direction `w` for time
`t`. Directions are negatives of forward velocities. -/
def extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V) (hs : 0 ≤ s) (ht : 0 < t) :
    FiniteAffineRay V P where
  endpoint := (-s • β.direction - t • w) +ᵥ β.endpoint
  direction := w
  bends := β.bends.mapDomain (fun b => b - (s + t)) +
    Finsupp.single (-t) (β.direction - w)
  bend_neg := by
    classical
    intro b hb
    rcases Finset.mem_union.mp (Finsupp.support_add hb) with hb | hb
    · rw [Finsupp.mapDomain_support_of_injective (fun _ _ h => sub_left_injective h)] at hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      linarith [β.bend_neg a ha]
    · have := Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
      linarith

/-- The endpoint is obtained by the two prescribed forward displacements. -/
@[simp]
theorem endpoint_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) :
    (β.extend s t w hs ht).endpoint = (-s • β.direction - t • w) +ᵥ β.endpoint := (rfl)

/-- The extension ends in its new direction. -/
@[simp]
theorem direction_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) : (β.extend s t w hs ht).direction = w := (rfl)

/-- Old bend times are translated, and the new increment is the difference
between the old and new directions. -/
@[simp]
theorem bends_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) :
    (β.extend s t w hs ht).bends =
      β.bends.mapDomain (fun b => b - (s + t)) +
        Finsupp.single (-t) (β.direction - w) := (rfl)

/-- Before the new encounter, the entire path is the original ray with its
time coordinate translated. This includes the straight continuation to the encounter. -/
theorem extend_apply_of_le (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) {u : ℝ} (hu : u ≤ -t) :
    β.extend s t w hs ht u = β (u + (s + t)) := by
  classical
  rw [eval_def, bends_extend, direction_extend, endpoint_extend,
    Finsupp.sum_add_index' (fun _ => smul_zero _)
      (fun _ _ _ => smul_add _ _ _),
    Finsupp.sum_mapDomain_index (fun _ => smul_zero _)
      (fun _ _ _ => smul_add _ _ _),
    Finsupp.sum_single_index (h := fun b v => max (b - u) 0 • v) (smul_zero _),
    max_eq_left (by linarith : 0 ≤ -t - u), eval_def, vadd_vadd]
  have he : β.bends.sum (fun b v => max (b - (s + t) - u) 0 • v) =
      β.bends.sum (fun b v => max (b - (u + (s + t))) 0 • v) := by
    congr 1
    funext b v
    congr 2
    ring
  rw [he]
  congr 1
  module

/-- After the new encounter there are no further bends. -/
theorem extend_apply_of_ge (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) {u : ℝ} (hu : -t ≤ u) :
    β.extend s t w hs ht u = (-u • w) +ᵥ (β.extend s t w hs ht).endpoint := by
  classical
  rw [eval_def, bends_extend, direction_extend,
    Finsupp.sum_add_index' (fun _ => smul_zero _)
      (fun _ _ _ => smul_add _ _ _),
    Finsupp.sum_mapDomain_index (fun _ => smul_zero _)
      (fun _ _ _ => smul_add _ _ _),
    Finsupp.sum_single_index (h := fun b v => max (b - u) 0 • v) (smul_zero _),
    max_eq_right (by linarith : -t - u ≤ 0), zero_smul, add_zero]
  have he : β.bends.sum (fun b v => max (b - (s + t) - u) 0 • v) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    dsimp only
    rw [max_eq_right (by linarith [β.bend_neg b hb]), zero_smul]
  rw [he, zero_sub, neg_smul]

/-- The original path is retained at every original nonpositive time. -/
@[simp]
theorem extend_apply_sub (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) {u : ℝ} (hu : u ≤ 0) :
    β.extend s t w hs ht (u - (s + t)) = β u := by
  rw [extend_apply_of_le _ _ _ _ hs ht (by linarith), sub_add_cancel]

/-- The direction before the new encounter is the original interval direction. -/
theorem directionAt_extend_of_le (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) {u : ℝ} (hu : u ≤ -t) :
    (β.extend s t w hs ht).directionAt u = β.directionAt (u + (s + t)) := by
  classical
  rw [directionAt_def, bends_extend, direction_extend,
    Finsupp.sum_add_index' (fun _ => by split <;> rfl)
      (fun _ _ _ => by split <;> simp),
    Finsupp.sum_mapDomain_index (fun _ => by split <;> rfl)
      (fun _ _ _ => by split <;> simp),
    Finsupp.sum_single_index (by split <;> rfl), ite_eq_left hu, directionAt_def]
  have he : β.bends.sum (fun b v => if u ≤ b - (s + t) then v else 0) =
      β.bends.sum (fun b v => if u + (s + t) ≤ b then v else 0) := by
    congr 1
    funext b v
    simp only [le_sub_iff_add_le]
  rw [he]
  abel

/-- After the new encounter the interval direction is the new direction. -/
theorem directionAt_extend_of_gt (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) {u : ℝ} (hu : -t < u) :
    (β.extend s t w hs ht).directionAt u = w := by
  classical
  rw [directionAt_def, bends_extend, direction_extend,
    Finsupp.sum_add_index' (fun _ => by split <;> rfl)
      (fun _ _ _ => by split <;> simp),
    Finsupp.sum_mapDomain_index (fun _ => by split <;> rfl)
      (fun _ _ _ => by split <;> simp),
    Finsupp.sum_single_index (by split <;> rfl), ite_eq_right hu.not_ge]
  have he : β.bends.sum (fun b v => if u ≤ b - (s + t) then v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    dsimp only
    rw [ite_eq_right (by linarith [β.bend_neg b hb])]
  simp [he]

/-- Extending the endpoint leaves the incoming direction unchanged. -/
@[simp]
theorem incomingDirection_extend (β : FiniteAffineRay V P) (s t : ℝ) (w : V)
    (hs : 0 ≤ s) (ht : 0 < t) :
    (β.extend s t w hs ht).incomingDirection = β.incomingDirection := by
  classical
  simp only [incomingDirection_def, direction_extend, bends_extend]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (by rfl)]
  abel

end Mei.FiniteAffineRay
