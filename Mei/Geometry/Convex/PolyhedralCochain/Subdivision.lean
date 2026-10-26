/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Sweep
public import Mei.Geometry.Convex.Sweep.Topology

/-!
# Sweeping oriented subdivisions

Sweeping every piece of an oriented subdivision along a common transverse
lattice vector gives an oriented subdivision of the swept cell. The pieces
retain disjoint relative interiors and inherit the contracted orientation.
Consequently the swept generators satisfy the subdivision relation in
polyhedral cochains. This is the relation needed to descend the transverse
sweep from generators to cochains.

The construction uses `OrientedCell.sweep` for the oriented generators and
`Mei.Convex.sweep_coordinates_unique` for their supports. Relative interior
disjointness uses the base-point recovery in
`Mei.Convex.disjoint_intrinsicInterior_sweep`. No boundedness or absence of
lineality is assumed.
-/

public section

noncomputable section

open Module Set

namespace Mei.OrientedCell.IsOrientedSubdivision

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {σ : OrientedCell h (k + 1)} {Q : Finset (OrientedCell h (k + 1))}

/-- The swept pieces of an oriented subdivision, with the contracted orientations. -/
def sweepPieces (hQ : IsOrientedSubdivision σ Q) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) : Finset (OrientedCell h k) := by
  classical
  exact Q.attach.image fun τ => τ.val.sweep n (by rwa [hQ.direction_eq τ.property])

/-- Membership in the swept subdivision is witnessed by an original piece. -/
@[simp]
theorem mem_sweepPieces (hQ : IsOrientedSubdivision σ Q) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (τ : OrientedCell h k) :
    τ ∈ hQ.sweepPieces n hn ↔
      ∃ q : Q, q.val.sweep n (by rwa [hQ.direction_eq q.property]) = τ := by
  classical
  simp [sweepPieces]

/-- Distinct original pieces remain distinct after sweeping. -/
theorem sweep_injective (hQ : IsOrientedSubdivision σ Q) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    Function.Injective (fun τ : Q =>
      τ.val.sweep n (by rwa [hQ.direction_eq τ.property])) := by
  intro τ υ he
  have hcarrier : τ.val.carrier = υ.val.carrier :=
    (Convex.sweep_eq_sweep_iff_of_subset (by simpa [direction_affineSpan] using hn)
      (hQ.carrier_subset τ.property) (hQ.carrier_subset υ.property)).mp
        (by simpa using congrArg OrientedCell.carrier he)
  apply Subtype.ext
  exact OrientedCell.ext hcarrier
    ((hQ.orientation_eq τ.val τ.property).trans (hQ.orientation_eq υ.val υ.property).symm)

/-- Sweeping an oriented subdivision gives an oriented subdivision of the sweep. -/
theorem sweep (hQ : IsOrientedSubdivision σ Q) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    IsOrientedSubdivision (σ.sweep n hn) (hQ.sweepPieces n hn) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp only [mem_sweepPieces, iUnion_exists, iUnion_iUnion_eq', sweep_carrier]
    rw [← Convex.sweep_iUnion]
    simpa only [iUnion_subtype] using
      congrArg (fun P => Convex.sweep P (i n)) hQ.biUnion_carrier
  · intro τ hτ υ hυ hne
    obtain ⟨q, rfl⟩ := (mem_sweepPieces hQ n hn τ).mp hτ
    obtain ⟨r, rfl⟩ := (mem_sweepPieces hQ n hn υ).mp hυ
    dsimp only [Function.onFun]
    rw [sweep_carrier, sweep_carrier]
    apply Convex.disjoint_intrinsicInterior_sweep
      (fun hm => hn (by
        rw [direction_affineSpan]
        exact vectorSpan_mono ℝ
          (union_subset (hQ.carrier_subset q.property) (hQ.carrier_subset r.property)) hm))
    exact hQ.pairwiseDisjoint q.property r.property (fun he => hne (by cases Subtype.ext he; rfl))
  · intro τ hτ
    obtain ⟨q, rfl⟩ := (mem_sweepPieces hQ n hn τ).mp hτ
    simp only [sweep_orientation]
    have hd := hQ.direction_eq q.property
    have ho := hQ.orientation_eq q.val q.property
    congr 1

end Mei.OrientedCell.IsOrientedSubdivision

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Swept generators respect the original subdivision relation, indexed by the
original pieces so that every coefficient occurs exactly once. -/
theorem mk_sweep_eq_sum_of_isOrientedSubdivision
    {σ : OrientedCell h (k + 1)} {Q : Finset (OrientedCell h (k + 1))}
    (hQ : OrientedCell.IsOrientedSubdivision σ Q) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    mk (R := R) (σ.sweep n hn) c =
      ∑ τ : Q, mk (τ.val.sweep n (by rwa [hQ.direction_eq τ.property])) c := by
  classical
  rw [mk_eq_sum_of_isOrientedSubdivision (hQ.sweep n hn)]
  simp only [OrientedCell.IsOrientedSubdivision.sweepPieces]
  rw [Finset.sum_image (fun a _ b _ he => hQ.sweep_injective n hn he)]
  simp

end Mei.PolyhedralCochain
