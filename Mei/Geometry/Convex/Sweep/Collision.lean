/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Itinerary
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Interior collisions of backward encounters

A strict backward itinerary cannot encounter the same affine supporting space
twice consecutively: after reaching that space, the next elapsed time would be
zero. Consequently, when consecutive encounters collide in a limit, their
supporting directions differ and the collision lies in the wall family's
singular support. The first encounter can instead collapse onto the endpoint.

The closed walls may be indexed independently of the itinerary. In particular,
selected simultaneous-event supports need not themselves be closed: it suffices
that they lie in the corresponding closed walls. No convexity, dimension or
rationality hypothesis is needed.

We use `AffineMap.eqOn_affineSpan`,
`affineSpan_eq_of_notMem_singularSupport`, and continuity of `backwardPoint`.
The degeneration interpretation follows Carl–Pumperla–Siebert, *A tropical view
on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public section

open Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (u : Fin n → V)
  (W : ι → Set V) (wall : Fin n → ι)
  (hheight : ∀ j x, x ∈ W (wall j) → f j x = c j)

include hheight

/-- A zero elapsed time between two consecutive encounters in a limit of
strict itineraries places their common point in singular support. Closedness
is required only of the ambient walls, not of the endpoint family. -/
theorem backwardPoint_mem_singularSupport_of_time_eq_zero
    (hclosed : ∀ j, IsClosed (W j)) {D : Set V}
    (hD : D ⊆ backwardDomain f c u (fun j => W (wall j)))
    {Q : V} (hQ : Q ∈ closure D) {i j : Fin n} (hij : i.succ = j.castSucc)
    (ht : backwardTime f c u j Q = 0) :
    backwardPoint f c u j.succ Q ∈ singularSupport W := by
  have hinc (l : Fin n) : backwardPoint f c u l.succ Q ∈ W (wall l) :=
    closure_minimal (fun x hx => ((mem_backwardDomain f c u _ x).mp (hD hx) l).2)
      ((hclosed _).preimage (backwardPoint f c u l.succ).continuous) hQ
  have he : backwardPoint f c u j.succ Q = backwardPoint f c u i.succ Q := by
    rw [backwardPoint_succ_apply, ht, zero_smul, add_zero, ← hij]
  by_contra hreg
  obtain ⟨Q₁, hQ₁⟩ := (Set.nonempty_of_mem hQ).of_closure
  exact affineSpan_ne_of_mem_backwardDomain f c u W wall hheight (hD hQ₁) hij
    (affineSpan_eq_of_notMem_singularSupport hreg (he.symm ▸ hinc i) (hinc j))

/-- At a limit of strict itineraries, a zero elapsed time is either a terminal
wall encounter or an interior collision in singular support. This includes
multiple simultaneous collisions and repeated or coincident wall indices. -/
theorem backwardTime_eq_zero_imp_terminal_or_singularSupport
    (hclosed : ∀ j, IsClosed (W j)) {D : Set V}
    (hD : D ⊆ backwardDomain f c u (fun j => W (wall j)))
    {Q : V} (hQ : Q ∈ closure D) (j : Fin n)
    (ht : backwardTime f c u j Q = 0) :
    (j.val = 0 ∧ Q ∈ W (wall j)) ∨
      backwardPoint f c u j.succ Q ∈ singularSupport W := by
  by_cases hj : j.val = 0
  · left
    refine ⟨hj, ?_⟩
    have hinc : backwardPoint f c u j.succ Q ∈ W (wall j) :=
      closure_minimal (fun x hx => ((mem_backwardDomain f c u _ x).mp (hD hx) j).2)
        ((hclosed _).preimage (backwardPoint f c u j.succ).continuous) hQ
    have he : j.castSucc = 0 := Fin.ext hj
    simpa only [backwardPoint_succ_apply, ht, zero_smul, add_zero, he,
      backwardPoint_zero, ContinuousAffineMap.coe_id, id_eq] using hinc
  · right
    let i : Fin n := ⟨j.val - 1, by omega⟩
    have hij : i.succ = j.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      dsimp only [i]
      omega
    exact backwardPoint_mem_singularSupport_of_time_eq_zero f c u W wall hheight
      hclosed hD hQ hij ht

end Mei.Convex
