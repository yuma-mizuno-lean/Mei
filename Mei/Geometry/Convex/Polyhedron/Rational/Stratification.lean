/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.LocallyClosed
public import Mei.Geometry.Convex.Polyhedron.SignCell.Interior

/-!
# Common stratifications of rational semilinear domains

A finite collection of rational semilinear sets admits one finite rational-normal
affine arrangement whose sign cells determine membership in every set. Its nonempty
sign cells partition the whole space into locally closed convex polyhedra. Each
original set is a union of these strata, including its lower-dimensional pieces.

A rational semilinear set also decomposes into disjoint relative interiors of
finitely many closed rational-normal polyhedra contained in its closure. These
closed charts retain boundary limits of points in the original set.

This simultaneous construction is useful for endpoint domains of finitely many
affine histories: the set of admitted history labels is constant on each stratum.
It combines the individual arrangements supplied by
`IsRationalSemilinear.exists_eq_biUnion_signCell`, using their dependent disjoint
union as a common row index. Offsets remain arbitrary real numbers.
-/

public section

namespace Mei

variable {N V J : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Finite J]
  {S : J → Set V}

/-- One finite rational-normal arrangement determines membership in all sets of a
finite semilinear family. In particular, membership is constant on each sign cell. -/
theorem IsRationalSemilinear.exists_common_signCell
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (ι : Type) (_ : Finite ι) (g : ι → (V →ᴬ[ℝ] ℝ)),
      (∀ a, Toric.IsRationalFunctional h (g a).toAffineMap.linear) ∧
        ∀ (σ : ι → SignType) (x y : V), x ∈ Convex.signCell g σ →
          y ∈ Convex.signCell g σ → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  classical
  choose κ hκ g hg t ht using fun j => (hS j).exists_eq_biUnion_signCell
  let rows := Σ j, κ j
  let G : rows → (V →ᴬ[ℝ] ℝ) := fun a => g a.1 a.2
  let : ∀ j, Finite (κ j) := hκ
  -- The theorem's small row universe is recovered even when the label universe is larger.
  let := Fintype.ofFinite rows
  let e := Fintype.equivFin rows
  refine ⟨Fin (Fintype.card rows), inferInstance, fun a => G (e.symm a),
    fun a => hg _ _, ?_⟩
  intro σ x y hx hy j
  have he (a : κ j) : SignType.sign (g j a x) = SignType.sign (g j a y) := by
    have hx' := Convex.mem_signCell.mp hx (e ⟨j, a⟩)
    have hy' := Convex.mem_signCell.mp hy (e ⟨j, a⟩)
    simpa only [Equiv.symm_apply_apply, G] using hx'.trans hy'.symm
  rw [← ht j]
  simp only [Set.mem_iUnion]
  constructor <;> rintro ⟨τ, hτ, hz⟩
  · exact ⟨τ, hτ, Convex.mem_signCell.mpr
      (fun a => (he a).symm.trans (Convex.mem_signCell.mp hz a))⟩
  · exact ⟨τ, hτ, Convex.mem_signCell.mpr
      (fun a => (he a).trans (Convex.mem_signCell.mp hz a))⟩

/-- A finite semilinear family has a common partition of the entire space into
nonempty locally closed rational-normal polyhedra, on which all memberships agree.
The strata include boundary pieces, and no closedness of the original sets is needed. -/
theorem IsRationalSemilinear.exists_common_partition
    (hS : ∀ j, IsRationalSemilinear h (S j)) :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → Set V),
      (∀ a, (C a).Nonempty ∧ IsLocallyClosedPolyhedron h (C a)) ∧
        (Pairwise fun a b => Disjoint (C a) (C b)) ∧ (⋃ a, C a) = Set.univ ∧
          ∀ a x, x ∈ C a → ∀ y, y ∈ C a → ∀ j, (x ∈ S j ↔ y ∈ S j) := by
  obtain ⟨ι, _, g, hg, hmem⟩ := IsRationalSemilinear.exists_common_signCell hS
  let κ := {σ : ι → SignType // (Convex.signCell g σ).Nonempty}
  refine ⟨κ, inferInstance, fun σ => Convex.signCell g σ,
    fun σ => ⟨σ.property, isLocallyClosedPolyhedron_signCell g hg σ⟩,
    fun σ τ hστ => Convex.signCell_disjoint (Subtype.coe_injective.ne hστ), ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨⟨_, x, Convex.mem_signCell_sign g x⟩,
      Convex.mem_signCell_sign g x⟩
  · intro σ x hx y hy
    exact hmem σ x y hx hy

/-- A rational semilinear set is a finite disjoint union of relative interiors of
nonempty closed rational-normal polyhedra with locally closed polyhedral interiors.
Each closed chart lies in the closure of the original set, so it adds only limits
of valid points. -/
theorem IsRationalSemilinear.exists_disjoint_intrinsicInteriors
    {S : Set V} (hS : IsRationalSemilinear h S) :
    ∃ (κ : Type) (_ : Finite κ) (K : κ → Set V),
      (∀ a, (K a).Nonempty ∧ IsRationalNormalPolyhedron h (K a) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (K a)) ∧ K a ⊆ closure S) ∧
        (Pairwise fun a b => Disjoint (intrinsicInterior ℝ (K a))
          (intrinsicInterior ℝ (K b))) ∧ ⋃ a, intrinsicInterior ℝ (K a) = S := by
  obtain ⟨ι, _, g, hg, s, hs⟩ := hS.exists_eq_biUnion_signCell
  let κ := {σ : ι → SignType // σ ∈ s ∧ (Convex.signCell g σ).Nonempty}
  refine ⟨κ, inferInstance, fun σ => closure (Convex.signCell g σ), ?_, ?_, ?_⟩
  · intro σ
    refine ⟨σ.property.2.mono subset_closure, ?_, ?_, ?_⟩
    · exact (isLocallyClosedPolyhedron_signCell g hg σ).isRationalNormalPolyhedron_closure
    · rw [Convex.intrinsicInterior_closure_signCell]
      exact isLocallyClosedPolyhedron_signCell g hg σ
    · apply closure_mono
      rw [← hs]
      exact Set.subset_iUnion₂_of_subset σ.val σ.property.1 Set.Subset.rfl
  · intro σ τ hστ
    simp only [Convex.intrinsicInterior_closure_signCell]
    exact Convex.signCell_disjoint (Subtype.coe_injective.ne hστ)
  · simp only [Convex.intrinsicInterior_closure_signCell]
    apply Set.Subset.antisymm
    · rw [← hs]
      exact Set.iUnion_subset fun σ =>
        Set.subset_iUnion₂_of_subset σ.val σ.property.1 Set.Subset.rfl
    · intro x hx
      obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp (hs ▸ hx)
      exact Set.mem_iUnion.mpr ⟨⟨σ, hσ, x, hxσ⟩, hxσ⟩

end Mei
