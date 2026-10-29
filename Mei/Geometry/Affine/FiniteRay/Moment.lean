/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Conservation of the moment of a finite ray

Let `ω` be an alternating bilinear form on a real vector space `V`, and let `β` be a finite
affine ray in `V`, regarded as an affine space over itself. Along a segment with direction
`m` the position moves by multiples of `m`, so the moment `ω(β t, m)` is constant. If every
direction increment of `β` is proportional to its bend position in the sense
`ω(β b, Δ_b) = 0`, as for bends on walls through the origin with increments tangent to the
wall, then the moment is also unchanged across each bend. Hence
`ω(β t, β.directionAt t) = ω(β.endpoint, β.direction)` at every time
(`FiniteAffineRay.form_eval_directionAt`). Between consecutive bend times `s < t` the positions
then satisfy `ω(β s, β t) = (s - t) ω(β.endpoint, β.direction)`
(`FiniteAffineRay.form_eval_eval`): for `ω(β.endpoint, β.direction) ≠ 0` successive bend
positions rotate strictly in one sense.

For `V = ℝ²` and the determinant this is the conservation of the position–velocity
determinant of broken lines in rank-two scattering diagrams, used by Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, Lemma 5.13
(arXiv:2503.03719v1), to order the bends of a broken line.
-/

public section

namespace Mei.FiniteAffineRay

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

/-- If every bend of a finite ray has its increment `ω`-orthogonal to its position, then the
moment `ω(β t, β.directionAt t)` is the same at every time, and equals the moment of the
final segment at the endpoint. -/
theorem form_eval_directionAt (hω : ω.IsAlt) (β : FiniteAffineRay V V)
    (hβ : ∀ b ∈ β.bends.support, ω (β b) (β.bends b) = 0) (t : ℝ) :
    ω (β t) (β.directionAt t) = ω β.endpoint β.direction := by
  classical
  obtain ⟨E, m, f, hf⟩ := β
  induction f using Finsupp.induction_on_min₂ generalizing t with
  | zero =>
    simp [eval_def, directionAt_def, hω.self_eq_zero]
  | add_single b δ f hmin hδ ih =>
    have hbf : f b = 0 := Finsupp.notMem_support_iff.mp fun h => (hmin b h).false
    have hb : b < 0 := hf b (by simp [hbf, hδ])
    have hf' : ∀ c ∈ f.support, c < 0 := fun c hc =>
      hf c (by simpa [Finsupp.single_eq_of_ne (hmin c hc).ne'] using hc)
    set β' : FiniteAffineRay V V := ⟨E, m, f, hf'⟩
    have hβeq : (⟨E, m, f + Finsupp.single b δ, hf⟩ : FiniteAffineRay V V) =
        β'.insert b δ hb := by
      ext <;> simp [β']
    have hβc : ∀ c ∈ f.support, β' c = β'.insert b δ hb c := fun c hc => by
      rw [insert_apply, max_eq_right (sub_nonpos.mpr (hmin c hc).le), zero_smul, zero_vadd]
    have hβ' : ∀ c ∈ β'.bends.support, ω (β' c) (β'.bends c) = 0 := fun c hc => by
      have hcb : c ≠ b := (hmin c hc).ne'
      have hc' : c ∈ (f + Finsupp.single b δ).support := by
        simpa [Finsupp.single_eq_of_ne hcb] using hc
      simpa [hβeq, ← hβc c hc, Finsupp.single_eq_of_ne hcb] using hβ c hc'
    have ih' : ∀ t, ω (β' t) (β'.directionAt t) = ω β'.endpoint β'.direction :=
      fun t => ih t hf' hβ'
    have hβb : β'.insert b δ hb b = β' b := by simp
    have hδb : ω (β' b) δ = 0 := by
      simpa [hβeq, hβb, hbf] using hβ b (by simp [hbf, hδ])
    rw [hβeq, insert_apply, directionAt_insert, endpoint_insert, direction_insert]
    rcases le_or_gt t b with htb | hbt
    · -- before the new bend, move back along the incoming segment of `β'` to the bend
      have hle : ∀ c ∈ f.support, b ≤ c := fun c hc => (hmin c hc).le
      have hseg : β' b -ᵥ β' t = (t - b) • β'.directionAt b :=
        β'.eval_vsub_eval htb fun c hc => Or.inr (hle c hc)
      have hdir : β'.directionAt t = β'.directionAt b := by
        rw [β'.directionAt_of_le_bends t fun c hc => htb.trans (hle c hc),
          β'.directionAt_of_le_bends b hle]
      have hpos : β' t = β' b - (t - b) • β'.directionAt b := by
        rw [← hseg, vsub_eq_sub, sub_sub_cancel]
      rw [ite_eq_left htb, max_eq_left (sub_nonneg.mpr htb), hdir, vadd_eq_add, hpos]
      have hb' := ih' b
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, hω.self_eq_zero, smul_eq_mul] at hb' ⊢
      linear_combination hb' + hδb + (b - t) * (hω.neg δ (β'.directionAt b)).symm
    · rw [ite_eq_right hbt.not_ge, max_eq_right (sub_nonpos.mpr hbt.le), zero_smul, zero_vadd,
        add_zero]
      exact ih' t

/-- Under the hypotheses of `form_eval_directionAt`, if no bend lies strictly between the times
`s < t` or at `t`, then `ω(β s, β t) = (s - t) ω(β.endpoint, β.direction)`. -/
theorem form_eval_eval (hω : ω.IsAlt) (β : FiniteAffineRay V V)
    (hβ : ∀ b ∈ β.bends.support, ω (β b) (β.bends b) = 0) {s t : ℝ} (hst : s < t)
    (hb : ∀ b ∈ β.bends.support, b ≤ s ∨ t ≤ b) :
    ω (β s) (β t) = (s - t) * ω β.endpoint β.direction := by
  classical
  -- across `[s, t)` the direction changes only by the increment at `s`
  have hdir : β.directionAt s = β.directionAt t + β.bends s := by
    have hterm : ∀ b ∈ β.bends.support, (if s ≤ b then β.bends b else 0) =
        (if t ≤ b then β.bends b else 0) + if b = s then β.bends b else 0 := by
      intro b hb'
      rcases hb b hb' with h | h
      · rcases h.lt_or_eq with h | rfl
        · simp [h.not_ge, (h.trans hst).not_ge, h.ne]
        · simp [hst.not_ge]
      · simp [hst.le.trans h, h, (hst.trans_le h).ne']
    rw [directionAt_def, directionAt_def, add_assoc, Finsupp.sum, Finsupp.sum,
      Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
    split_ifs with hs
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hs]
  have hβs : ω (β s) (β.bends s) = 0 := by
    by_cases hs : s ∈ β.bends.support
    · exact hβ s hs
    · rw [Finsupp.notMem_support_iff.mp hs, map_zero]
  have hcons := form_eval_directionAt hω β hβ s
  rw [hdir, map_add, hβs, add_zero] at hcons
  have hpos : β t = (s - t) • β.directionAt t + β s := by
    rw [← β.eval_vsub_eval hst.le hb, vsub_eq_sub, sub_add_cancel]
  rw [hpos, map_add, map_smul, hcons, hω.self_eq_zero, add_zero, smul_eq_mul]

end Mei.FiniteAffineRay
