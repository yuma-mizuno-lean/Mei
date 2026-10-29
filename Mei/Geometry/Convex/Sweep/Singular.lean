/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Encounter

/-!
# Singular-set avoidance for backward rays

The singular-avoidance domain of a selected itinerary tests every open finite
segment, the open incoming half-line, all recorded encounters and the endpoint.
It is exactly the domain on which the realized negative half-line misses the
specified sets. In contrast to wall encounters, singular encounters are forbidden
even at recorded times.

For finitely many closed rational-normal singular cells and lattice directions,
with rational selected hyperplane normals and rational semilinear selected supports,
this domain is rational semilinear. Since rational semilinearity is closed under
finite intersections, `IsRationalSemilinear.exists_disjoint_intrinsicInteriors`
decomposes its intersection with any other rational semilinear domain.
No codimension assumption is needed for this domain calculation.

We reuse `backwardRay_avoids_iff`, the finite-segment and incoming-ray avoidance
domains and their rationality theorems. Backward endpoint parameterization follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ)
  (v : Fin (n + 1) → V) (P : Fin n → Set V) (S : J → Set V)

/-- Selected incidences with singular-set avoidance on all segments, at every
recorded encounter and at the endpoint. The incoming source is unrestricted. -/
def backwardSingularAvoidanceDomain : Set V :=
  (backwardAvoidanceDomain f c (fun j => v j.castSucc) P S ∩
    backwardIncomingDomain f c (fun j => v j.castSucc) P (v (Fin.last n)) univ S) ∩
      {Q | ∀ j a, backwardPoint f c (fun j => v j.castSucc) j Q ∉ S a}

/-- Singular avoidance adds the endpoint and encounter-point tests to the open
finite-segment and incoming-ray avoidance constraints. -/
@[simp]
theorem mem_backwardSingularAvoidanceDomain (Q : V) :
    Q ∈ backwardSingularAvoidanceDomain f c v P S ↔
      Q ∈ backwardAvoidanceDomain f c (fun j => v j.castSucc) P S ∧
      Q ∈ backwardIncomingDomain f c (fun j => v j.castSucc) P (v (Fin.last n)) univ S ∧
      ∀ j a, backwardPoint f c (fun j => v j.castSucc) j Q ∉ S a := by
  simp only [backwardSingularAvoidanceDomain, mem_inter_iff, mem_ofPred_eq, and_assoc]

/-- Singular avoidance retains the selected incidences and positive elapsed times. -/
theorem backwardSingularAvoidanceDomain_subset_backwardDomain :
    backwardSingularAvoidanceDomain f c v P S ⊆
      backwardDomain f c (fun j => v j.castSucc) P :=
  fun _ hQ => backwardAvoidanceDomain_subset_backwardDomain _ _ _ _ _
    ((mem_backwardSingularAvoidanceDomain _ _ _ _ _ _).mp hQ).1

/-- Empty singular sets impose no restrictions beyond the selected itinerary. -/
@[simp]
theorem backwardSingularAvoidanceDomain_empty :
    backwardSingularAvoidanceDomain f c v P (fun _ : J => ∅) =
      backwardDomain f c (fun j => v j.castSucc) P := by
  ext Q
  simp

variable (Q : V) (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q)

local notation "τ" => fun j : Fin (n + 1) =>
  backwardParameter f c (fun l : Fin n => v (Fin.castSucc l)) j Q
local notation "β" => backwardRay f c v Q hpos

/-- Singular avoidance on the endpoint domain is equivalent to avoidance along
the entire realized negative half-line, including time zero and recorded times.
The avoided sets may be arbitrary and the incoming direction may be zero. -/
theorem mem_backwardSingularAvoidanceDomain_iff :
    Q ∈ backwardSingularAvoidanceDomain f c v P S ↔
      (∀ j : Fin n, β (τ j.succ) ∈ P j) ∧
        ∀ a t, t ≤ 0 → β t ∉ S a := by
  have htimes (j : Fin (n + 1)) : τ j ≤ 0 := by
    simpa using (strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos).antitone
      (Fin.zero_le j)
  have hsplit := mem_backwardAvoidanceDomain_inter_incoming_iff f c v Q hpos P S univ
  simp only [mem_univ, Filter.eventually_true, and_true] at hsplit
  constructor
  · intro hQ
    obtain ⟨hfinite, hincoming, hpoints⟩ :=
      (mem_backwardSingularAvoidanceDomain _ _ _ _ _ _).mp hQ
    obtain ⟨hP, havoid⟩ := hsplit.mp ⟨hfinite, hincoming⟩
    refine ⟨hP, fun a t ht => ?_⟩
    rcases ht.eq_or_lt with rfl | ht
    · simpa using hpoints 0 a
    · by_cases he : ∃ j : Fin n, t = τ j.succ
      · obtain ⟨j, rfl⟩ := he
        simpa only [backwardRay_apply_parameter] using hpoints j.succ a
      · exact havoid a t ht (fun j hj => he ⟨j, hj⟩)
  · rintro ⟨hP, havoid⟩
    have hopen := hsplit.mpr ⟨hP, fun a t ht _ => havoid a t ht.le⟩
    exact (mem_backwardSingularAvoidanceDomain _ _ _ _ _ _).mpr
      ⟨hopen.1, hopen.2, fun j a => by
        simpa only [backwardRay_apply_parameter] using havoid a (τ j) (htimes j)⟩

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- Avoidance of a finite family of closed rational-normal singular cells along
the whole realized ray preserves rational semilinearity of the endpoint domain.
The incoming source is unrestricted. Selected supports may themselves be semilinear;
offsets are arbitrary real numbers. -/
theorem isRationalSemilinear_backwardSingularAvoidanceDomain [Finite J]
    (w : Fin (n + 1) → N)
    (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hS : ∀ a, IsRationalNormalPolyhedron h (S a)) :
    IsRationalSemilinear h
      (backwardSingularAvoidanceDomain f c (fun j => i (w j)) P S) := by
  have hpoints : IsRationalSemilinear h
      (⋂ j : Fin (n + 1), ⋂ a : J,
        backwardPoint f c (fun j => i (w j.castSucc)) j ⁻¹' (S a)ᶜ) :=
    .iInter fun j => .iInter fun a =>
      ((hS a).isLocallyClosedPolyhedron.isRationalSemilinear.compl).preimage _
        (isRationalLinearMap_backwardPoint f c (fun j => w j.castSucc) hf j)
  convert ((isRationalSemilinear_backwardAvoidanceDomain f c P S
    (fun j => w j.castSucc) hf hP hS).inter
    (isRationalSemilinear_backwardIncomingDomain f c P univ S (fun j => w j.castSucc)
      (w (Fin.last n)) hf hP (IsRationalNormalPolyhedron.univ h) hS)).inter hpoints using 1
  ext Q
  simp only [backwardSingularAvoidanceDomain, mem_inter_iff, mem_iInter, mem_preimage,
    mem_compl_iff, mem_ofPred_eq]

end Mei.Convex
