/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Stratification
public import Mei.Geometry.Affine.Arrangement
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Generic stability of finite semilinear families

A finite family of rational semilinear sets has a common finite exceptional
arrangement containing all of its frontiers. Off that arrangement, one neighborhood
preserves every membership test, including multiplicities of distinct labels with
coincident domains. Consequently the label set and any function of it, such as a
finite weighted sum or its cardinality, are locally constant on the generic locus.

The sets may be nonclosed or lower-dimensional. Empty domains, identically zero
conditions and arbitrary real offsets are permitted. Rationality is used to obtain
a common finite sign arrangement; its constant rows are omitted only from the
exceptional locus, never from the membership tests.

We combine `IsRationalSemilinear.exists_common_signCell` with
`ExceptionalArrangement.eventually_sign_eq_of_isGeneric`. This applies to endpoint
domains after imposing semilinear support, avoidance and incoming-source constraints.
-/

public section

open Set Filter Topology

namespace Mei

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite J] {S : J → Set V}

/-- A finite semilinear family has a common exceptional arrangement outside which
all admitted labels are unchanged on an ambient neighborhood. All domain frontiers
are exceptional, including those of lower-dimensional domains. -/
theorem IsRationalSemilinear.exists_membershipArrangement
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ E : ExceptionalArrangement V,
      (∀ j, frontier (S j) ⊆ {x | ¬ E.IsGeneric x}) ∧
        ∀ x, E.IsGeneric x → ∀ᶠ y in 𝓝 x, ∀ j, y ∈ S j ↔ x ∈ S j := by
  obtain ⟨κ, _, g, _, hmem⟩ := IsRationalSemilinear.exists_common_signCell hS
  let E := ExceptionalArrangement.ofAffineForms (fun a => (g a).toAffineMap)
  have hstable (x : V) (hx : E.IsGeneric x) :
      ∀ᶠ y in 𝓝 x, ∀ j, y ∈ S j ↔ x ∈ S j := by
    apply (ExceptionalArrangement.eventually_sign_eq_of_isGeneric g hx).mono
    intro y hy
    exact hmem (fun a => SignType.sign (g a x)) y x
      (Convex.mem_signCell.mpr hy) (Convex.mem_signCell_sign g x)
  refine ⟨E, ?_, hstable⟩
  intro j x hx hgen
  have he := (hstable x hgen).mono fun y hy => hy j
  by_cases hm : x ∈ S j
  · exact hx.2 (mem_interior_iff_mem_nhds.mpr (he.mono fun _ hy => hy.mpr hm))
  · have hi : x ∈ interior (S j)ᶜ :=
      mem_interior_iff_mem_nhds.mpr (he.mono fun _ hy => mt hy.mp hm)
    exact (mem_interior_iff_notMem_frontier hm).mp hi (by rwa [frontier_compl])

/-- The admitted-label set of a finite semilinear family is locally constant off
one finite exceptional arrangement. Every statistic or weighted evaluation depending
only on those labels is therefore locally constant there as well. -/
theorem IsRationalSemilinear.exists_isLocallyConstant_labels
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ E : ExceptionalArrangement V,
      (∀ j, frontier (S j) ⊆ {x | ¬ E.IsGeneric x}) ∧
        IsLocallyConstant (fun x : {x // E.IsGeneric x} => {j | x.val ∈ S j}) := by
  obtain ⟨E, hfrontier, hstable⟩ := IsRationalSemilinear.exists_membershipArrangement hS
  refine ⟨E, hfrontier, (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_⟩
  exact (continuous_subtype_val.continuousAt.tendsto.eventually
    (hstable x.val x.property)).mono fun y hy => Set.ext hy

end Mei
