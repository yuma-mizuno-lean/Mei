/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code
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
and shared with `Mei.PolyhedralCochain.sum_mk_eq_zero_of_existsUnique_reverse`.
It uses Mathlib's `Finset.sum_involution` and applies to additive commutative
monoids, without cancellation of multiplication by two.
-/

public section

namespace Finset

/-- An indexed finite sum vanishes if every occurrence has a unique occurrence
with a different index and reversed value, and the two values sum to zero. -/
theorem sum_eq_zero_of_unique_partner {ι κ A : Type*} [AddCommMonoid A]
    (S : Finset (Σ _ : ι, κ)) (rev : κ → κ) (hrev : Function.Involutive rev)
    (hpartner : ∀ x ∈ S, ∃! a', ⟨a', rev x.2⟩ ∈ S ∧ a' ≠ x.1)
    (f : κ → A) (hf : ∀ b, f b + f (rev b) = 0) :
    (∑ x ∈ S, f x.2) = 0 := by
  let g (x) (hx : x ∈ S) : Σ _ : ι, κ := ⟨(hpartner x hx).choose, rev x.2⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S := (hpartner x hx).choose_spec.1.1
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hfirst : (hpartner (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hpartner (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨by simpa only [g, hrev x.2] using hx,
          Ne.symm (hpartner x hx).choose_spec.1.2⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (hrev x.2))
  refine sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    exact hf x.2
  · intro x hx _ he
    exact (hpartner x hx).choose_spec.1.2 (congrArg Sigma.fst he)

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
  rw [sum_sigma' s]
  refine (s.sigma t).sum_eq_zero_of_unique_partner rev hrev ?_ f hf
  intro x hx
  obtain ⟨ha, hb⟩ := mem_sigma.mp hx
  obtain ⟨a', ⟨ha', hne, hrevb⟩, huniq⟩ := hpartner x.1 ha x.2 hb
  exact ⟨a', ⟨mem_sigma.mpr ⟨ha', hrevb⟩, hne⟩, fun a'' ⟨hmem, hne'⟩ =>
    huniq a'' ⟨(mem_sigma.mp hmem).1, hne', (mem_sigma.mp hmem).2⟩⟩

end Finset
