/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Face
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Exact polyhedral pieces of rational wall singular support

The singular support of finitely many rational-normal polyhedra is exactly a
finite union of rational-normal polyhedra. Relative boundaries are represented
by the active-row faces of finite rational presentations; the other pieces are
intersections of members with different supporting directions. Empty pieces,
arbitrary real offsets, lineality and lower-dimensional members are allowed.

This is an exact union, rather than an affine-subspace cover, so avoidance of
these pieces is equivalent to avoidance of the original singular support.
The proof uses `intrinsicFrontier_eq_iUnion_active` and `activeFace`.
-/

public section

open TauCeti (singularSupport mem_singularSupport)

open Set

namespace Mei.Convex

universe u

variable {N V : Type*} {ι : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Singular support of a finite rational-normal family is exactly a finite
union of rational-normal polyhedra. No codimension or nonemptiness is required. -/
theorem exists_finite_singularSupport_polyhedra [Finite ι]
    (W : ι → Set V) (hW : ∀ j, IsRationalNormalPolyhedron h (W j)) :
    ∃ (κ : Type u) (_ : Finite κ) (S : κ → Set V),
      (∀ a, IsRationalNormalPolyhedron h (S a)) ∧ singularSupport W = ⋃ a, S a := by
  classical
  choose P hP using fun j => isRationalNormalPolyhedron_iff.mp (hW j)
  let A (j : ι) := {r : Fin (P j).numConstraints //
    ∃ x ∈ (P j).carrier, (P j).inequality r x < 0}
  let B := {jk : ι × ι //
    (affineSpan ℝ (W jk.1)).direction ≠ (affineSpan ℝ (W jk.2)).direction}
  let S : (Σ j, A j) ⊕ B → Set V := Sum.elim
    (fun jr => ((P jr.1).activeFace {jr.2.val}).carrier)
    (fun jk => W jk.val.1 ∩ W jk.val.2)
  have hfront (j : ι) : intrinsicFrontier ℝ (W j) =
      ⋃ r : A j, ((P j).activeFace {r.val}).carrier := by
    have hpres : (P j).carrier = {x | ∀ r, (P j).inequality r x ≤ 0} :=
      Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
    rw [← hP j, intrinsicFrontier_eq_iUnion_active (P j).inequality hpres]
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr, hxP, hxr⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, by
        simpa only [RationalAffinePolyhedron.carrier_activeFace, mem_ofPred_eq,
          Finset.mem_singleton, forall_eq] using And.intro hxP hxr⟩
    · intro hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
      have hxP : x ∈ (P j).carrier ∧ (P j).inequality r.val x = 0 := by
        simpa only [RationalAffinePolyhedron.carrier_activeFace, mem_ofPred_eq,
          Finset.mem_singleton, forall_eq] using hr
      exact Set.mem_iUnion₂.mpr ⟨r.val, r.property, hxP⟩
  refine ⟨(Σ j, A j) ⊕ B, inferInstance, S, ?_, ?_⟩
  · intro a
    cases a with
    | inl jr =>
      exact (isRationalNormalPolyhedron_iff (h := h)).mpr
        ⟨(P jr.1).activeFace {jr.2.val}, rfl⟩
    | inr jk => exact (hW jk.val.1).inter (hW jk.val.2)
  · ext x
    rw [mem_singularSupport]
    constructor
    · rintro (⟨j, hj⟩ | ⟨j, k, hjk, hj, hk⟩)
      · rw [hfront j] at hj
        obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hj
        exact Set.mem_iUnion.mpr ⟨.inl ⟨j, r⟩, hr⟩
      · exact Set.mem_iUnion.mpr ⟨.inr ⟨(j, k), hjk⟩, hj, hk⟩
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      cases a with
      | inl jr => exact Or.inl ⟨jr.1, (hfront jr.1).symm ▸
          Set.mem_iUnion.mpr ⟨jr.2, ha⟩⟩
      | inr jk => exact Or.inr ⟨jk.val.1, jk.val.2, jk.property, ha⟩

end Mei.Convex
