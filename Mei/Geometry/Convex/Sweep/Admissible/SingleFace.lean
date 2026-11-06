/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mei.Geometry.Affine.FiniteRay.Hyperplane

/-!
# Admissible rays through a single face

Conservation of a normal coordinate across the recorded encounters makes that
coordinate affine along the entire ray. If all encounters lie on one level
hyperplane, there is at most one encounter. This counts recorded encounters,
including those with unchanged spatial direction, rather than only bends.

For a full hyperplane in the obstacle family, a transverse ray has exactly one
encounter precisely when the intersection parameter is negative. On the incoming
side it has no encounters and is the straight ray. On the opposite side the
encounter parameter and position are the explicit backward intersection formulas.
Sources and singular obstacles remain part of the original admissible realization.

The projection argument reuses `FiniteAffineRay.apply_eval_eq_sub_mul` and
`AdmissibleRayRealization.bends_parameter`. The single-face description is the
geometric input to propagation through a coefficient span, as in
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open Set

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {v : Fin (n + 1) → V} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- Preserving a normal coordinate across each encounter kills the normal
component of every actual bend, including when some encounters are not bends. -/
theorem normal_bends_eq_zero (r : AdmissibleRayRealization f c v P W S C Q)
    (ν : V →L[ℝ] ℝ) (hv : ∀ j : Fin n, ν (v j.castSucc) = ν (v j.succ))
    {t : ℝ} (ht : t ∈ r.ray.bends.support) : ν (r.ray.bends t) = 0 := by
  obtain ⟨j, rfl⟩ := r.bends_recorded t ht
  rw [r.bends_parameter, map_sub, hv j, sub_self]

/-- The conserved normal coordinate is affine in time on the whole ray,
including the full incoming half-line. -/
theorem normal_ray_eq_sub_mul (r : AdmissibleRayRealization f c v P W S C Q)
    (ν : V →L[ℝ] ℝ) (hv : ∀ j : Fin n, ν (v j.castSucc) = ν (v j.succ)) (t : ℝ) :
    ν (r.ray t) = ν Q - t * ν (v 0) := by
  simpa only [LinearMap.coe_toAffineMap, LinearMap.toAffineMap_linear,
    ContinuousLinearMap.coe_coe,
    r.endpoint_eq, r.ray_direction] using
    r.ray.apply_eval_eq_sub_mul ν.toLinearMap.toAffineMap
      (fun t ht => r.normal_bends_eq_zero ν hv ht) t

section SingleFace

variable {ν : V →L[ℝ] ℝ} {b : ℝ}
  (r : AdmissibleRayRealization (fun _ => ν) (fun _ => b) v P W S C Q)
  (hv : ∀ j : Fin n, ν (v j.castSucc) = ν (v j.succ))

include r hv

/-- Every recorded encounter with one face has the same explicit intersection
parameter. Transversality follows from the recorded encounter itself. -/
theorem parameter_eq_div_singleFace (j : Fin n) :
    r.parameter j.succ = (ν Q - b) / ν (v 0) := by
  have hn : ∀ i : Fin (n + 1), ν (v i) = ν (v 0) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hv i).symm.trans ih
  have htrans : ν (v 0) ≠ 0 := hn j.castSucc ▸ r.transverse j
  have he := r.height_eq j
  rw [r.normal_ray_eq_sub_mul ν hv] at he
  apply (eq_div_iff htrans).mpr
  linarith

/-- A common face and conserved normal velocity permit at most one recorded
encounter. No nonzero-velocity assumption is needed for empty itineraries. -/
theorem encounter_count_le_one_singleFace : n ≤ 1 := by
  by_contra hn
  have h₀ := r.parameter_eq_div_singleFace hv (⟨0, by omega⟩ : Fin n)
  have h₁ := r.parameter_eq_div_singleFace hv (⟨1, by omega⟩ : Fin n)
  have hne := r.strictAnti_parameter.injective (h₀.trans h₁.symm)
  have := congrArg Fin.val hne
  simp at this

/-- Any recorded face crossing lies strictly before the endpoint. -/
theorem div_neg_of_encounter_singleFace (j : Fin n) : (ν Q - b) / ν (v 0) < 0 := by
  rw [← r.parameter_eq_div_singleFace hv j, ← r.parameter_zero]
  exact r.strictAnti_parameter (Fin.succ_pos j)

/-- The crossing point is the intersection of the terminal backward ray and
the face, even if its recorded encounter leaves the spatial direction unchanged. -/
theorem ray_parameter_eq_singleFace (j : Fin n) :
    r.ray (r.parameter j.succ) = Q - ((ν Q - b) / ν (v 0)) • v 0 := by
  have hn := r.encounter_count_le_one_singleFace hv
  have hj : j.val = 0 := by omega
  have ht : r.parameter j.succ < 0 := by
    simpa only [r.parameter_zero] using r.strictAnti_parameter (Fin.succ_pos j)
  rw [r.ray_eq_endpoint_sub_smul j.succ ?_ ⟨le_rfl, ht.le⟩,
    r.parameter_eq_div_singleFace hv j]
  intro i hi
  have hi0 : i = 0 := by
    apply Fin.ext
    simp only [Fin.val_zero]
    simp only [Fin.lt_def, Fin.val_succ] at hi
    omega
  rw [hi0]

/-- A transverse ray encountering one face is on the opposite side exactly
when its itinerary has one encounter. A full copy of the face in the obstacle
family forces the encounter to be recorded. -/
theorem encounter_count_eq_one_iff_singleFace (htrans : ν (v 0) ≠ 0)
    (a : J) (hW : {x | ν x = b} ⊆ W a) :
    n = 1 ↔ (ν Q - b) / ν (v 0) < 0 := by
  constructor
  · intro hn
    exact r.div_neg_of_encounter_singleFace hv ⟨0, by omega⟩
  · intro ht
    have hn := r.encounter_count_le_one_singleFace hv
    by_contra hne
    have hn0 : n = 0 := by omega
    have hwall : r.ray ((ν Q - b) / ν (v 0)) ∈ W a := by
      apply hW
      rw [Set.mem_ofPred_eq, r.normal_ray_eq_sub_mul ν hv,
        div_mul_cancel₀ _ htrans]
      ring
    exact r.avoids_walls a _ ht (fun j => by have := j.isLt; omega) hwall

/-- A transverse allowed endpoint is on the incoming side precisely when no
face encounter is recorded. -/
theorem encounter_count_eq_zero_iff_singleFace (htrans : ν (v 0) ≠ 0)
    (a : J) (hW : {x | ν x = b} ⊆ W a) :
    n = 0 ↔ 0 < (ν Q - b) / ν (v 0) := by
  have hoff : ν Q ≠ b := fun he => r.off_walls a (hW he)
  have ht : (ν Q - b) / ν (v 0) ≠ 0 := div_ne_zero (sub_ne_zero.mpr hoff) htrans
  have hn := r.encounter_count_le_one_singleFace hv
  have he := r.encounter_count_eq_one_iff_singleFace hv htrans a hW
  constructor
  · intro h
    have hnot : ¬ (ν Q - b) / ν (v 0) < 0 := fun ht => by
      have := he.mpr ht
      omega
    exact lt_of_le_of_ne (le_of_not_gt hnot) ht.symm
  · intro h
    have hne : n ≠ 1 := fun hn => (not_lt_of_ge h.le) (he.mp hn)
    omega

end SingleFace

/-- For a single full face, an opposite-side endpoint admits its unique
one-crossing realization exactly when the computed crossing misses the singular
set. The source is the full incoming half-space. No closedness, codimension or
genericity assumption on the singular subset is needed. -/
theorem nonempty_singleFace_iff {ν : V →L[ℝ] ℝ} {b : ℝ} {u w Q : V}
    {Z : Set V} (hnormal : ν w = ν u) (htrans : ν w ≠ 0)
    (hZ : Z ⊆ {x | ν x = b}) :
    Nonempty (AdmissibleRayRealization (fun _ : Fin 1 => ν) (fun _ => b) ![w, u]
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u} Q) ↔
      (ν Q - b) / ν w < 0 ∧ Q - ((ν Q - b) / ν w) • w ∉ Z := by
  have hv : ∀ j : Fin 1, ν (![w, u] j.castSucc) = ν (![w, u] j.succ) := by
    intro j
    fin_cases j
    exact hnormal
  constructor
  · rintro ⟨r⟩
    have ht := r.div_neg_of_encounter_singleFace hv 0
    have hx := r.avoids_singular ()
      (r.parameter (Fin.succ (0 : Fin 1)))
      (by simpa only [r.parameter_zero] using
        (r.strictAnti_parameter (Fin.succ_pos (0 : Fin 1))).le)
    rw [r.ray_parameter_eq_singleFace hv 0] at hx
    exact ⟨ht, hx⟩
  · rintro ⟨ht, hx⟩
    -- Insert the difference of the incoming and outgoing directions at the
    -- computed crossing. The conserved normal then handles all avoidance tests.
    let τ := (ν Q - b) / ν w
    let β := (FiniteAffineRay.straight Q w).insert τ (u - w) ht
    have hbends {t : ℝ} (ht' : t ∈ β.bends.support) : t = τ := by
      have hmem : t ∈ (Finsupp.single τ (u - w)).support := by
        simpa only [β, FiniteAffineRay.bends_insert, FiniteAffineRay.bends_straight,
          zero_add] using ht'
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hmem)
    have hβ (t : ℝ) : ν (β t) = ν Q - t * ν w := by
      have hb : ∀ t ∈ β.bends.support,
          ν.toLinearMap.toAffineMap.linear (β.bends t) = 0 := by
        intro t ht'
        simp [β, hbends ht', map_sub, hnormal]
      simpa only [LinearMap.coe_toAffineMap, LinearMap.toAffineMap_linear,
        ContinuousLinearMap.coe_coe, β, FiniteAffineRay.endpoint_insert,
        FiniteAffineRay.endpoint_straight, FiniteAffineRay.direction_insert,
        FiniteAffineRay.direction_straight] using
        β.apply_eval_eq_sub_mul ν.toLinearMap.toAffineMap hb t
    have hhit (t : ℝ) : ν (β t) = b ↔ t = τ := by
      rw [hβ, eq_div_iff htrans]
      constructor <;> intro h <;> linarith
    have hcross : β τ = Q - τ • w := by
      simp only [β, FiniteAffineRay.insert_apply, sub_self, max_self, zero_smul,
        FiniteAffineRay.straight_apply, vadd_eq_add, zero_add, neg_smul, neg_add_eq_sub]
    refine ⟨{
      ray := β
      parameter := ![0, τ]
      parameter_zero := rfl
      strictAnti_parameter := ?_
      transverse := ?_
      endpoint_eq := by simp [β]
      directionAt_eq := ?_
      bends_recorded := ?_
      height_eq := ?_
      incidence := ?_
      avoids_walls := ?_
      incoming := ?_
      avoids_singular := ?_
      off_walls := ?_ }⟩
    · apply Fin.strictAnti_iff_succ_lt.mpr
      intro j
      fin_cases j
      exact ht
    · intro j
      fin_cases j
      exact htrans
    · intro j
      fin_cases j <;> simp [β]
    · intro t ht'
      exact ⟨0, hbends ht'⟩
    · intro j
      fin_cases j
      exact (hhit τ).mpr rfl
    · intro j
      fin_cases j
      exact (hhit τ).mpr rfl
    · intro a t _ hnot hwall
      exact hnot 0 ((hhit t).mp hwall)
    · filter_upwards [Filter.eventually_lt_atBot τ] with t ht'
      have he : (ν (β t) - b) / ν u = τ - t := by
        rw [hβ, ← hnormal]
        dsimp only [τ]
        field_simp
        ring
      exact he ▸ sub_pos.mpr ht'
    · intro a t _ hmem
      have he := (hhit t).mp (hZ hmem)
      subst t
      exact hx (hcross ▸ hmem)
    · intro a hwall
      have hwall' : ν Q = b := hwall
      have he : τ = 0 := by simp [τ, hwall']
      exact ht.ne he

/-- On the incoming side the empty itinerary has its straight realization;
it is admitted exactly at endpoints in the full incoming half-space. Singular
subsets of the face impose no additional condition on these rays. -/
theorem nonempty_singleFace_empty_iff {ν : V →L[ℝ] ℝ} {b : ℝ} {u Q : V}
    {Z : Set V} (htrans : ν u ≠ 0) (hZ : Z ⊆ {x | ν x = b}) :
    Nonempty (AdmissibleRayRealization (fun _ : Fin 0 => ν) (fun _ => b) (fun _ => u)
      (fun _ => {x | ν x = b}) (fun _ : Unit => {x | ν x = b})
      (fun _ : Unit => Z) {x | 0 < (ν x - b) / ν u} Q) ↔
      0 < (ν Q - b) / ν u := by
  constructor
  · rintro ⟨r⟩
    exact (r.encounter_count_eq_zero_iff_singleFace (fun j => j.elim0)
      htrans () Set.Subset.rfl).mp rfl
  · intro ht
    have he (t : ℝ) :
        (ν (FiniteAffineRay.straight Q u t) - b) / ν u = (ν Q - b) / ν u - t := by
      simp only [FiniteAffineRay.straight_apply, vadd_eq_add, map_add, map_smul,
        smul_eq_mul]
      field_simp
      ring
    have hoff (t : ℝ) (ht' : t ≤ 0) : ν (FiniteAffineRay.straight Q u t) ≠ b := by
      intro hwall
      have hz : (ν (FiniteAffineRay.straight Q u t) - b) / ν u = 0 := by rw [hwall]; simp
      rw [he] at hz
      linarith
    refine ⟨{
      ray := FiniteAffineRay.straight Q u
      parameter := fun _ => 0
      parameter_zero := rfl
      strictAnti_parameter := ?_
      transverse := fun j => j.elim0
      endpoint_eq := FiniteAffineRay.endpoint_straight Q u
      directionAt_eq := fun _ => FiniteAffineRay.directionAt_straight Q u 0
      bends_recorded := by simp
      height_eq := fun j => j.elim0
      incidence := fun j => j.elim0
      avoids_walls := fun _ t ht' _ => hoff t ht'.le
      incoming := ?_
      avoids_singular := fun _ t ht' hm => hoff t ht' (hZ hm)
      off_walls := ?_ }⟩
    · intro i j hij
      have := Fin.eq_zero i
      have := Fin.eq_zero j
      omega
    · filter_upwards [Filter.eventually_lt_atBot ((ν Q - b) / ν u)] with t ht'
      rw [he]
      exact sub_pos.mpr ht'
    · intro a hm
      exact (ne_of_gt ht) (by rw [hm]; simp)

end Mei.Convex.AdmissibleRayRealization
