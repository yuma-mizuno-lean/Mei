/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible.Extend
public import Mei.Geometry.Convex.Sweep.Admissible.FinalEncounter
public import Mei.Geometry.Convex.Sweep.Admissible.Truncate
public import Mei.Geometry.Affine.Segment

/-!
# Endpoint domains across a regular final encounter

Let the backward line `Q + u • v 0` from an endpoint `Q` first meet the walls at a
regular transverse point `Q + t • v 0` of the final encounter's support, whose
incident walls lie in the encounter hyperplane. Then for every sufficiently short
incoming displacement `η`, the endpoint `Q` is admitted by the complete backward data
exactly when the incoming germ `Q + t • v 0 + η • v 1` is admitted by the data with the
final encounter removed.

One direction cuts an admissible realization inside the segment before its final
encounter; the other attaches the final encounter to an admissible realization at the
germ. The source, wall and singular avoidance conditions are retained in both.
This is the geometric step of the last-change recursion of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V J K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {f : Fin (n + 1) → V →L[ℝ] ℝ} {c : Fin (n + 1) → ℝ}
  {v : Fin (n + 2) → V} {P : Fin (n + 1) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V}

/-- Across a regular final encounter at `Q + t • v 0`, the endpoint `Q` and every
sufficiently close incoming germ `Q + t • v 0 + η • v 1` are admitted together, by
the complete backward data and by the data without its final encounter. -/
theorem eventually_mem_admissibleBackwardDomain_iff_succ [Finite J] [Finite K] (Q : V)
    {t : ℝ} (ht : 0 < t)
    (htrans : f 0 (v 0) ≠ 0) (hnormal : f 0 (v 0) = f 0 (v 1))
    (hheight : f 0 (Q + t • v 0) = c 0) (hinc : Q + t • v 0 ∈ P 0)
    (hP : P 0 ⊆ ⋃ a, W a) (hclosedW : ∀ a, IsClosed (W a))
    (hplane : ∀ a, Q + t • v 0 ∈ W a → ∀ y ∈ W a, f 0 y = c 0)
    (hclosedS : ∀ a, IsClosed (S a)) (hregular : ∀ a, Q + t • v 0 ∉ S a)
    (hW : ∀ a u, 0 ≤ u → u < t → Q + u • v 0 ∉ W a)
    (hS : ∀ a u, 0 ≤ u → u < t → Q + u • v 0 ∉ S a) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      Q ∈ admissibleBackwardDomain f c v P W S C ↔
        Q + t • v 0 + η • v 1 ∈ admissibleBackwardDomain (fun j => f j.succ)
          (fun j => c j.succ) (fun j => v j.succ) (fun j => P j.succ) W S C := by
  let Z := Q + t • v 0
  have hnear := eventually_incomingSegment_notMem Z (v 1) (f 0).toLinearMap (c 0)
    (by simpa only [ContinuousLinearMap.coe_coe, ← hnormal] using htrans) hheight hclosedW
    hplane hclosedS hregular
  -- Cutting: an admitted endpoint has its final encounter at `Z`, and a short cut
  -- before it stays after every earlier encounter.
  have hcut : ∀ᶠ η : ℝ in 𝓝[>] 0, Q ∈ admissibleBackwardDomain f c v P W S C →
      Z + η • v 1 ∈ admissibleBackwardDomain (fun j => f j.succ)
        (fun j => c j.succ) (fun j => v j.succ) (fun j => P j.succ) W S C := by
    by_cases hQ : Q ∈ admissibleBackwardDomain f c v P W S C
    · let r := admissibleRayRealization f c v P W S C Q hQ
      obtain ⟨-, τ, hτ, hpar, -, hmem, hav⟩ := r.exists_finalEncounter
      have hτt : τ = t := by
        rcases lt_trichotomy τ t with hlt | rfl | hgt
        · obtain ⟨a, ha⟩ := mem_iUnion.mp (hP hmem)
          exact (hW a τ hτ.le hlt ha).elim
        · rfl
        · obtain ⟨a, ha⟩ := mem_iUnion.mp (hP hinc)
          exact (hav a t ht.le hgt ha).elim
      subst hτt
      have hpar1 : r.parameter 1 = -τ := hpar
      have hgap : ∀ᶠ η : ℝ in 𝓝 0, ∀ j : Fin n, r.parameter j.succ.succ < -τ - η := by
        refine eventually_all.mpr fun j => ?_
        have hlt : r.parameter j.succ.succ < r.parameter 1 :=
          r.strictAnti_parameter (Fin.succ_lt_succ_iff.mpr (Fin.succ_pos j))
        filter_upwards [eventually_lt_nhds (sub_pos.mpr (hpar1 ▸ hlt))] with η hη
        linarith
      filter_upwards [hgap.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with η hη hpos _
      have hpos : 0 < η := hpos
      have hupper : -τ - η < r.parameter 1 := by rw [hpar1]; linarith
      have hray : r.ray (-τ - η) = Z + η • v 1 := by
        have hafter : ∀ j : Fin (n + 2), 1 < j → r.parameter j ≤ -τ - η := by
          intro j hj
          obtain ⟨k, rfl⟩ : ∃ k : Fin n, j = k.succ.succ := by
            refine ⟨⟨j.val - 2, ?_⟩, Fin.ext ?_⟩
            · have := j.isLt
              have : 1 < j.val := hj
              omega
            · simp only [Fin.val_succ]
              have : 1 < j.val := hj
              omega
          exact (hη k).le
        have h := r.ray_eq_add_smul_of_before_parameter 1 hupper.le hafter
        have hZ : r.ray (r.parameter 1) = Z := by
          have hv : ∀ i ≤ (0 : Fin (n + 1)).castSucc, v i = v 0 := fun i hi => by
            rw [Fin.le_zero_iff.mp hi]
          have hτ' : (c 0 - f 0 Q) / f 0 (v 0) = τ := by
            rw [div_eq_iff htrans]
            rw [map_add, map_smul, smul_eq_mul] at hheight
            linarith
          have hp := r.ray_parameter_succ_eq_of_directions_eq 0 hv
          rw [hτ'] at hp
          exact hp
        rw [h, hZ, hpar1]
        congr 2
        ring
      rw [← hray]
      exact (r.truncateSucc (-τ - η) hupper hη).mem_admissibleBackwardDomain
    · exact Eventually.of_forall fun _ h => (hQ h).elim
  -- Attaching: a short admissible incoming segment to `Z` and the outgoing segment to
  -- `Q` extend every admitted germ.
  have hattach : ∀ᶠ η : ℝ in 𝓝[>] 0,
      Z + η • v 1 ∈ admissibleBackwardDomain (fun j => f j.succ)
        (fun j => c j.succ) (fun j => v j.succ) (fun j => P j.succ) W S C →
      Q ∈ admissibleBackwardDomain f c v P W S C := by
    filter_upwards [hnear, self_mem_nhdsWithin] with η hnear hpos hY
    have hpos : 0 < η := hpos
    let r := admissibleRayRealization _ _ _ _ W S C _ hY
    have hcont (u : ℝ) (hu : 0 ≤ u) : r.ray u = Z + η • v 1 - u • v 1 := by
      rw [r.ray_of_nonneg hu]
      simp only [vadd_eq_add, neg_smul, Fin.succ_zero_eq_one]
      abel
    have hend : (r.ray.extend η t (v 0) hpos.le ht).endpoint = Q := by
      rw [FiniteAffineRay.endpoint_extend, r.ray_direction, r.endpoint_eq]
      simp only [Z, vadd_eq_add, neg_smul, Fin.succ_zero_eq_one]
      abel
    have hZ : r.ray η = Z := by rw [hcont η hpos.le]; abel
    have g := r.extend η t (v 0) hpos.le ht (f 0) (c 0) (P 0) htrans (by rw [hZ]; exact hheight)
      (by rw [hZ]; exact hinc)
      (fun a u hu hu' => by rw [hcont u hu.le]; exact hnear.1 a u hu hu')
      (fun a u hu hu₀ => by
        rw [hend]
        have h := hW a (-u) (by linarith) (by linarith)
        rw [vadd_eq_add, add_comm]
        exact h)
      (fun a u hu hu' => by rw [hcont u hu.le]; exact hnear.2 a u hu hu')
      (fun a u hu hu₀ => by
        rw [hend]
        have h := hS a (-u) (by linarith) (by linarith)
        rw [vadd_eq_add, add_comm]
        exact h)
    have hmem := g.mem_admissibleBackwardDomain
    have hf : (Fin.cons (f 0) fun j => f j.succ : Fin (n + 1) → V →L[ℝ] ℝ) = f :=
      Fin.cons_self_tail f
    have hc : (Fin.cons (c 0) fun j => c j.succ : Fin (n + 1) → ℝ) = c := Fin.cons_self_tail c
    have hv : (Fin.cons (v 0) fun j => v j.succ : Fin (n + 2) → V) = v := Fin.cons_self_tail v
    have hP' : (Fin.cons (P 0) fun j => P j.succ : Fin (n + 1) → Set V) = P :=
      Fin.cons_self_tail P
    rw [hend, hf, hc, hv, hP'] at hmem
    exact hmem
  filter_upwards [hcut, hattach] with η h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The cons form of `eventually_mem_admissibleBackwardDomain_iff_succ`: prepending a
regular final encounter `(m, b, H)` with outgoing direction `w` to backward data,
the endpoint `Q` is admitted exactly when every sufficiently close incoming germ
`Q + t • w + η • v 0` is admitted by the original data. -/
theorem eventually_mem_admissibleBackwardDomain_cons_iff [Finite J] [Finite K]
    {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ} {v : Fin (n + 1) → V} {P : Fin n → Set V}
    (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V) (w Q : V) {t : ℝ} (ht : 0 < t)
    (htrans : m w ≠ 0) (hnormal : m w = m (v 0))
    (hheight : m (Q + t • w) = b) (hinc : Q + t • w ∈ H)
    (hP : H ⊆ ⋃ a, W a) (hclosedW : ∀ a, IsClosed (W a))
    (hplane : ∀ a, Q + t • w ∈ W a → ∀ y ∈ W a, m y = b)
    (hclosedS : ∀ a, IsClosed (S a)) (hregular : ∀ a, Q + t • w ∉ S a)
    (hW : ∀ a u, 0 ≤ u → u < t → Q + u • w ∉ W a)
    (hS : ∀ a u, 0 ≤ u → u < t → Q + u • w ∉ S a) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      Q ∈ admissibleBackwardDomain (Fin.cons m f) (Fin.cons b c) (Fin.cons w v)
          (Fin.cons H P) W S C ↔
        Q + t • w + η • v 0 ∈ admissibleBackwardDomain f c v P W S C := by
  have h := eventually_mem_admissibleBackwardDomain_iff_succ (f := Fin.cons m f)
    (c := Fin.cons b c) (v := Fin.cons w v) (P := Fin.cons H P) (W := W) (S := S) (C := C)
    Q ht (by simpa only [Fin.cons_zero] using htrans)
    (by simpa only [Fin.cons_zero, Fin.cons_one] using hnormal)
    (by simpa only [Fin.cons_zero] using hheight) (by simpa only [Fin.cons_zero] using hinc)
    (by simpa only [Fin.cons_zero] using hP) hclosedW
    (by simpa only [Fin.cons_zero] using hplane) hclosedS
    (by simpa only [Fin.cons_zero] using hregular) (by simpa only [Fin.cons_zero] using hW)
    (by simpa only [Fin.cons_zero] using hS)
  simpa only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ] using h

end Mei.Convex
