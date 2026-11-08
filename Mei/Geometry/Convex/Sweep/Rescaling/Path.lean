/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rescaling
public import Mei.Geometry.Convex.Polyhedron.Tangent.SingularSupport

/-!
# Tangent comparisons along bounded pieces of reconstructed rays

On bounded endpoint and time sets, a backward reconstructed path has bounded
image. Thus a single positive scale compares all its contacts with a finite
polyhedral family to contacts with the incident tangent cones. The comparison
includes unrecorded walls and the actual singular support, including relative
boundaries and intersections of different supporting directions.

The path can have collapsed encounters and need not be admissible. These results
compare local pieces of closed path charts; they impose no condition on the
unbounded incoming tail or on exterior pieces. They complement the selected
incidence comparison in `Mei.Convex.eventually_forall_mem_backwardDomain_add_smul_iff`.
The local broken-line interpretation follows Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (v : Fin (n + 1) → V)
  (z : V) (W : ι → Set V) (hW : ∀ j, TauCeti.IsConvexPolyhedron (W j))
  {K : Set V} {I : Set ℝ} (hK : Bornology.IsBounded K) (hI : Bornology.IsBounded I)

include hW hK hI

/-- A single sufficiently small positive scale compares every wall contact on
all reconstructed path pieces in the bounded parameter set. Nonincident walls
have no contacts. The times, endpoints and wall indices are all uniform. -/
theorem eventually_forall_backwardPath_mem_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K, ∀ t ∈ I, ∀ j,
      backwardPath f (fun j => f j z) v (z + r • Q) (r * t) ∈ W j ↔
        z ∈ W j ∧ backwardPath f 0 v Q t ∈ posTangentConeAt (W j) z := by
  have hb := isBounded_image_backwardPath f 0 v hK hI
  have hu := eventually_singleton_add_smul_subset (𝕜 := ℝ) hb
    (eventually_forall_mem_iff_sub_mem_posTangentConeAt W hW z)
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrpos
  intro Q hQ t ht j
  rw [backwardPath_add_smul f z Q v hrpos.le t]
  have hc := hr (Set.add_mem_add (Set.mem_singleton z)
    (Set.smul_mem_smul_set (mem_image_of_mem (fun p : V × ℝ => backwardPath f 0 v p.1 p.2)
      (mk_mem_prod hQ ht)))) j
  simp only [add_sub_cancel_left] at hc
  refine hc.trans ⟨?_, ?_⟩
  · rintro ⟨hz, hv⟩
    refine ⟨hz, ?_⟩
    simpa only [smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul] using
      Mei.smul_mem_posTangentConeAt hv (inv_pos.mpr hrpos).le
  · rintro ⟨hz, hv⟩
    exact ⟨hz, Mei.smul_mem_posTangentConeAt hv hrpos.le⟩

/-- The same uniform local comparison detects singular contacts, rather than
only contacts with the selected supports. It retains terminal times and times
at collapsed encounters. -/
theorem eventually_forall_backwardPath_mem_singularSupport_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K, ∀ t ∈ I,
      backwardPath f (fun j => f j z) v (z + r • Q) (r * t) ∈ singularSupport W ↔
        backwardPath f 0 v Q t ∈ singularSupport
          (fun j : {j | z ∈ W j} => posTangentConeAt (W j) z) := by
  have hb := isBounded_image_backwardPath f 0 v hK hI
  have hu := eventually_singleton_add_smul_subset (𝕜 := ℝ) hb
    (eventually_mem_singularSupport_iff_sub_mem_posTangentConeAt W hW z)
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hrpos
  intro Q hQ t ht
  rw [backwardPath_add_smul f z Q v hrpos.le t]
  have hc := hr (Set.add_mem_add (Set.mem_singleton z)
    (Set.smul_mem_smul_set (mem_image_of_mem (fun p : V × ℝ => backwardPath f 0 v p.1 p.2)
      (mk_mem_prod hQ ht))))
  simp only [mem_ofPred_eq, add_sub_cancel_left] at hc
  exact hc.trans (smul_mem_singularSupport_posTangentConeAt_iff
    (fun j : {j | z ∈ W j} => W j) z hrpos _)

local notation "τ" c:max => backwardParameter f c (fun j : Fin n => v (Fin.castSucc j))
local notation "TW" => fun j : {j | z ∈ W j} => posTangentConeAt (W j) z

/-- At a single small scale, uniformly on the bounded endpoint and time sets, the
local no-extra-encounter and regularity constraints of a rescaled backward path
agree with those of the incident tangent supports. Only recorded encounter times
are excepted from wall avoidance; no time is excepted from singular avoidance. -/
theorem eventually_forall_backwardPath_avoids_add_smul_iff :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ Q ∈ K,
      ((∀ s ∈ I, (∀ j : Fin n, r * s ≠ (τ (fun j => f j z)) j.succ (z + r • Q)) →
          ∀ b, backwardPath f (fun j => f j z) v (z + r • Q) (r * s) ∉ W b) ∧
        ∀ s ∈ I, backwardPath f (fun j => f j z) v (z + r • Q) (r * s) ∉ singularSupport W) ↔
      ((∀ s ∈ I, (∀ j : Fin n, s ≠ (τ 0) j.succ Q) → ∀ b, backwardPath f 0 v Q s ∉ TW b) ∧
        ∀ s ∈ I, backwardPath f 0 v Q s ∉ singularSupport TW) := by
  have hm := eventually_forall_backwardPath_mem_add_smul_iff f v z W hW hK hI
  have hs := eventually_forall_backwardPath_mem_singularSupport_add_smul_iff f v z W hW hK hI
  filter_upwards [hm, hs, self_mem_nhdsWithin] with r hr hsing hrpos
  intro Q hQ
  have htimes (s : ℝ) :
      (∀ j : Fin n, r * s ≠ (τ (fun j => f j z)) j.succ (z + r • Q)) ↔
        ∀ j : Fin n, s ≠ (τ 0) j.succ Q := by
    simp only [backwardParameter_add_smul, ne_eq, mul_right_inj' hrpos.ne']
  constructor
  · rintro ⟨hwall, hreg⟩
    refine ⟨?_, fun s hs => fun hh => hreg s hs ((hsing Q hQ s hs).mpr hh)⟩
    intro s hs htime b hb
    exact hwall s hs ((htimes s).mpr htime) b.val ((hr Q hQ s hs b.val).mpr ⟨b.property, hb⟩)
  · rintro ⟨hwall, hreg⟩
    refine ⟨?_, fun s hs => fun hh => hreg s hs ((hsing Q hQ s hs).mp hh)⟩
    intro s hs htime b hb
    obtain ⟨hzb, hb⟩ := (hr Q hQ s hs b).mp hb
    exact hwall s hs ((htimes s).mp htime) ⟨b, hzb⟩ hb

end Mei.Convex
