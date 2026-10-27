/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Cancellation of finite incidence sums

A sum over parent-fiber incidences vanishes when each incidence has a unique
other parent containing its reversed fiber element, and reversed terms cancel.
Parent indices retain multiplicities even when fiber elements coincide.

The pairing argument is extracted from
`Mei.OrientedCell.IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`
and uses Mathlib's `Finset.sum_involution`. It applies to additive commutative
monoids, without cancellation of multiplication by two.
-/

public section

namespace Finset

/-- A finite incidence sum vanishes if each incidence has a unique other parent
containing its reversed fiber element, reversal is involutive, and reversed
terms sum to zero. Parent indices preserve incidence multiplicities. -/
theorem sum_sum_eq_zero_of_unique_partner {ι κ A : Type*} [AddCommMonoid A]
    (s : Finset ι) (t : ι → Finset κ) (rev : κ → κ) (hrev : Function.Involutive rev)
    (hpartner : ∀ a ∈ s, ∀ b ∈ t a,
      ∃! a', a' ∈ s ∧ a' ≠ a ∧ rev b ∈ t a')
    (f : κ → A) (hf : ∀ b, f b + f (rev b) = 0) :
    (∑ a ∈ s, ∑ b ∈ t a, f b) = 0 := by
  classical
  let S := s.sigma t
  have hS (x : Σ _ : ι, κ) : x ∈ S ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 := by
    simp only [S, mem_sigma]
  have hex (x) (hx : x ∈ S) :
      ∃! a', a' ∈ s ∧ a' ≠ x.1 ∧ rev x.2 ∈ t a' :=
    hpartner x.1 ((hS x).mp hx).1 x.2 ((hS x).mp hx).2
  let g (x) (hx : x ∈ S) : Σ _ : ι, κ := ⟨(hex x hx).choose, rev x.2⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S :=
    (hS _).mpr ⟨(hex x hx).choose_spec.1.1, (hex x hx).choose_spec.1.2.2⟩
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hp := (hex x hx).choose_spec.1
    have hfirst : (hex (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hex (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨((hS x).mp hx).1, Ne.symm hp.2.1, by
          simpa only [g, hrev x.2] using ((hS x).mp hx).2⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (hrev x.2))
  rw [sum_sigma' s]
  refine sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    exact hf x.2
  · intro x hx _ he
    exact (hex x hx).choose_spec.1.2.1 (congrArg Sigma.fst he)

end Finset
