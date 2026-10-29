/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Rational
public import Mei.Geometry.Convex.Polyhedron.Rational.Segment

/-!
# Avoiding additional walls in backward itineraries

A selected backward itinerary imposes its recorded support incidences and positive
elapsed times. Its avoidance domain additionally requires every open finite segment
to miss a specified family of sets. For finitely many closed rational-normal
polyhedra and lattice velocities this domain is rational semilinear, hence admits
a finite disjoint decomposition into locally closed rational-normal polyhedra.

These conditions detect all encounters in the open segments, including tangencies
and singleton intersections. Recorded encounter points themselves are excluded
from the avoidance test, so simultaneous wall encounters remain possible. The
unbounded incoming segment, source admission and coefficient propagation are
separate conditions.

We combine `backwardPoint`, `backwardTime` and their rationality with bounded
one-parameter elimination. The endpoint-chart interpretation follows
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
-/

public section

namespace Mei.Convex

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (v : Fin n → V)
  (P : Fin n → Set V) (W : J → Set V)

/-- The selected support and time constraints, together with absence of additional
encounters in all open finite segments. Encounter endpoints are not tested. -/
def backwardAvoidanceDomain : Set V :=
  backwardDomain f c v P ∩
    {Q | ∀ j a t, 0 < t → t < backwardTime f c v j Q →
      backwardPoint f c v j.castSucc Q + t • v j ∉ W a}

/-- Avoidance consists of the selected incidences, positive elapsed times, and
absence of wall points strictly between successive recorded encounters. -/
@[simp]
theorem mem_backwardAvoidanceDomain (Q : V) :
    Q ∈ backwardAvoidanceDomain f c v P W ↔
      Q ∈ backwardDomain f c v P ∧
        ∀ j a t, 0 < t → t < backwardTime f c v j Q →
          backwardPoint f c v j.castSucc Q + t • v j ∉ W a := Iff.rfl

/-- Forgetting avoidance retains the selected support and time constraints. -/
theorem backwardAvoidanceDomain_subset_backwardDomain :
    backwardAvoidanceDomain f c v P W ⊆ backwardDomain f c v P :=
  Set.inter_subset_left

/-- Empty wall supports impose no additional endpoint constraint. -/
@[simp]
theorem backwardAvoidanceDomain_empty :
    backwardAvoidanceDomain f c v P (fun _ : J => ∅) = backwardDomain f c v P := by
  ext Q
  simp

/-- With no finite encounters, avoidance and support constraints are empty. This
does not impose a condition on the unbounded incoming segment. -/
@[simp]
theorem backwardAvoidanceDomain_zero (f : Fin 0 → V →L[ℝ] ℝ) (c : Fin 0 → ℝ)
    (v : Fin 0 → V) (P : Fin 0 → Set V) (W : J → Set V) :
    backwardAvoidanceDomain f c v P W = Set.univ := by
  ext Q
  simp

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  {h : TauCeti.Toric.IsIntegralLattice i}

/-- Adding open-segment avoidance of finitely many closed rational-normal
polyhedra preserves semilinearity of the backward endpoint domain. No
transversality, genericity or nonemptiness assumption is required. -/
theorem isRationalSemilinear_backwardAvoidanceDomain [Finite J]
    (w : Fin n → N) (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
    (hP : ∀ j, IsRationalSemilinear h (P j))
    (hW : ∀ a, IsRationalNormalPolyhedron h (W a)) :
    IsRationalSemilinear h (backwardAvoidanceDomain f c (fun j => i (w j)) P W) := by
  have hhit (j : Fin n) (a : J) : IsRationalSemilinear h
      {Q | ∃ t : ℝ, 0 < t ∧ t < backwardTime f c (fun j => i (w j)) j Q ∧
        backwardPoint f c (fun j => i (w j)) j.castSucc Q + t • i (w j) ∈ W a} :=
    isRationalSemilinear_setOf_exists_pos_lt_add_smul_mem (hW a) (w j)
      (backwardPoint f c (fun j => i (w j)) j.castSucc)
      (backwardTime f c (fun j => i (w j)) j)
      (isRationalLinearMap_backwardPoint f c w hf j.castSucc)
      (isRationalFunctional_backwardTime f c w hf j)
  convert (isRationalSemilinear_backwardDomain f c w hf hP).inter
    (IsRationalSemilinear.iInter fun j =>
      IsRationalSemilinear.iInter fun a => (hhit j a).compl) using 1
  ext Q
  simp only [mem_backwardAvoidanceDomain, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and]

end Mei.Convex
