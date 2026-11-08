/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Incoming
public import Mei.Geometry.Convex.Sweep.Admissible.Limit

/-!
# Polyhedral source admission of backward paths

Admission of the incoming tail of a backward path to a convex polyhedral source
depends only on the incoming base point and incoming direction. A source
inequality that increases strictly along the incoming direction cannot be
satisfied eventually; otherwise only the inequalities tangent to that direction
constrain the base point. Hence the endpoints with admitted tails form a closed
set, even for lower-dimensional sources or a zero incoming direction.

At a boundary endpoint of this set the whole incoming tail lies in a tight
tangential source face, and the corresponding inequality varies with the
endpoint after backward reconstruction, so constant rows give no spurious event.

These statements concern the backward path family itself and apply to every
broken-line carrier whose type paths are backward paths. They use
`backwardPath_eventually_mem_iff`, its incoming affine germ and the polyhedral
source-admission boundary criterion. The interpretation of incoming source
faces follows Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*,
§4 (arXiv:2205.07753v2).
-/

public section

open Set Filter Topology

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin (n + 1) → V)
  [Finite ι] (g : ι → V →ᴬ[ℝ] ℝ)

local notation "X" => backwardPoint f c (fun j : Fin n => v (Fin.castSucc j)) (Fin.last n)
local notation "C" => Set.iInter fun j : ι => Set.ofPred fun x : V => g j x ≤ 0
local notation "A" => Set.ofPred fun Q : V => ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ C

/-- The full incoming tail is admitted precisely when its affine base satisfies
every tangential source inequality. No time-order or admissibility assumption on
the endpoint is needed. -/
theorem backwardPath_eventually_mem_polyhedron_iff
    (hv : ∀ j, (g j).linear (v (Fin.last n)) ≤ 0) (Q : V) :
    (∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ C) ↔
      ∀ j, (g j).linear (v (Fin.last n)) = 0 → g j (X Q) ≤ 0 := by
  rw [backwardPath_eventually_mem_iff]
  simp only [mem_iInter, mem_ofPred_eq]
  exact AffineMap.eventually_forall_apply_add_smul_le_iff_of_nonpos
    (fun j => (g j).toAffineMap) (v (Fin.last n)) hv _

/-- The incoming-source condition is closed in endpoint space, including when
the source is lower-dimensional or the incoming velocity is zero. -/
theorem isClosed_backwardPath_sourceAdmission : IsClosed A := by
  have hC : TauCeti.IsConvexPolyhedron C := by
    have he : C = {x | ∀ j, g j x ≤ 0} := by ext x; simp
    rw [he]
    exact TauCeti.isConvexPolyhedron_setOf_forall g
  simpa only [backwardPath_eventually_mem_iff, Set.preimage_ofPred_eq] using
    (hC.eventually_add_smul_mem (v (Fin.last n))).isClosed.preimage (X).continuous

/-- Source-admission boundary endpoints are exactly the admitted endpoints
where a tangential row is tight and nonconstant after backward reconstruction.
This includes tangential source faces and excludes redundant constant rows. -/
theorem mem_frontier_backwardPath_sourceAdmission_iff (Q : V) :
    Q ∈ frontier A ↔
      (∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ C) ∧
        ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧ g j (X Q) = 0 ∧
          ((g j).comp X).toAffineMap.linear ≠ 0 := by
  have he :
      A = {Q : V | ∀ᶠ s : ℝ in atTop, ∀ j, g j (X Q + s • v (Fin.last n)) ≤ 0} := by
    ext Q
    rw [mem_ofPred_eq, backwardPath_eventually_mem_iff]
    simp only [mem_iInter, mem_ofPred_eq]
  have hsource := congrArg (fun E : Set V => Q ∈ E) he
  simp only [mem_ofPred_eq] at hsource
  rw [he, hsource]
  exact ContinuousAffineMap.mem_frontier_eventually_forall_apply_add_smul_le_comp_iff
    g X (v (Fin.last n)) Q

/-- At a source-admission boundary the incoming tail lies entirely in a tight
source face tangent to its velocity. The row varies with the endpoint, and the
tail is the original global incoming germ, even for collapsed encounters. -/
theorem backwardPath_eventually_mem_sourceFace_of_mem_frontier
    {Q : V} (hQ : Q ∈ frontier A) :
    ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
      ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ {x ∈ C | g j x = 0} := by
  obtain ⟨hsource, j, hjv, hjQ, hne⟩ :=
    (mem_frontier_backwardPath_sourceAdmission_iff f c v g Q).mp hQ
  refine ⟨j, hjv, hne, ?_⟩
  filter_upwards [hsource, backwardPath_eventuallyEq_incoming f c v Q] with s hs hpath
  refine ⟨hs, ?_⟩
  rw [hpath, ContinuousAffineMap.apply_add_smul, hjv, hjQ, zero_mul, add_zero]

variable {J K : Type*} (P : Fin n → Set V) (W : J → Set V) (S : K → Set V)

/-- Admissible endpoints have admitted incoming tails. -/
theorem admissibleBackwardDomain_subset_sourceAdmission (C₀ : Set V) :
    admissibleBackwardDomain f c v P W S C₀ ⊆
      {Q | ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ C₀} := by
  intro Y hY
  rw [mem_ofPred_eq, backwardPath_eventually_mem_iff]
  exact ((mem_backwardIncomingDomain _ _ _ _ _ _ _ _).mp
    ((mem_admissibleBackwardDomain ..).mp hY).2.1).2.2

/-- In the closure of the admissible domain, loss of interior source admission
forces the original incoming tail into a tangential source face. No rationality
of the source rows or nonzero-velocity hypothesis is needed. -/
theorem backwardPath_eventually_mem_sourceFace_of_mem_closure
    {Q : V} (hQ : Q ∈ closure (admissibleBackwardDomain f c v P W S C))
    (hnot : Q ∉ interior A) :
    ∃ j, (g j).linear (v (Fin.last n)) = 0 ∧ ((g j).comp X).toAffineMap.linear ≠ 0 ∧
      ∀ᶠ s : ℝ in atBot, backwardPath f c v Q s ∈ {x ∈ C | g j x = 0} := by
  have hsource := closure_minimal (admissibleBackwardDomain_subset_sourceAdmission f c v P W S C)
    (isClosed_backwardPath_sourceAdmission f c v g) hQ
  exact backwardPath_eventually_mem_sourceFace_of_mem_frontier f c v g
    ((mem_frontier_iff_notMem_interior hsource).mpr hnot)

end Mei.Convex
