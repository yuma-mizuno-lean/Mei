/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Basic

/-!
# Families of walls with a common support and normal

Index the walls of a directed diagram by families `a : ι → κ`, and suppose that every wall of
the family `i` has support `S i` and normal `ν i`. At order `k`, the *family logarithm*
(`DirectedDiagram.familyLog`) is the sum of the logarithms of the projected labels of the
active walls of the family; any finite set of walls of the family containing the active ones
computes it (`DirectedDiagram.familyLog_eq_sum`). The walls through a regular point commute,
so the logarithm of their combined label is the sum, over the families through the point, of
the signed family logarithms (`DirectedDiagram.log_combinedLabel_eq_sum_familyLog`). Hence two
diagrams with families of the same supports, normals and family logarithms are equivalent at
order `k` (`DirectedDiagram.levelEquivalent_of_familyLog_eq`), however the families are split
into individual walls. For instance, a function wall may be presented by its ray factors in
two different lattices of degrees.

Pushforward along `DirectedWall.Pushforward` maps family logarithms by the truncated Lie map
from the order of the cutoff modulus (`DirectedDiagram.familyLog_pushforward`).

The comparison uses `DirectedDiagram.log_combinedLabel_eq_sum` and the characterization of
finite-order equivalence by combined labels, `DirectedDiagram.levelEquivalent_iff_combinedLabel_eq`.
-/

public section

open TauCeti (singularSupport)

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u

variable {Γ Λ R V ι ι' κ : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι) (a : ι → κ)

open Classical in
/-- The order-`k` logarithm of the family `i`: the sum of the logarithms of the projected
labels of the active walls `j` with `a j = i`. -/
def familyLog (k : ℕ) (i : κ) : d.lieTruncation ℒ k :=
  ∑ j ∈ (Set.toFinite (D.active k)).toFinset with a j = i,
    BCHGroup.log (L := d.lieTruncation ℒ k) (CompletedGroup.projection k (D.wall j).label)

/-- Any finite set of walls of the family `i` containing its active walls computes the family
logarithm. -/
theorem familyLog_eq_sum (k : ℕ) (i : κ) (s : Finset ι) (hs : ∀ j ∈ s, a j = i)
    (hact : ∀ j ∈ D.active k, a j = i → j ∈ s) :
    D.familyLog a k i =
      ∑ j ∈ s, BCHGroup.log (L := d.lieTruncation ℒ k)
        (CompletedGroup.projection k (D.wall j).label) := by
  classical
  unfold familyLog
  refine Finset.sum_subset_zero_on_sdiff (fun j hj => ?_) (fun j hj => ?_) fun _ _ => rfl
  · obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    exact hact j ((Set.toFinite (D.active k)).mem_toFinset.mp hj) hji
  · obtain ⟨hjs, hj⟩ := Finset.mem_sdiff.mp hj
    have hna : j ∉ D.active k := fun ha =>
      hj (Finset.mem_filter.mpr ⟨(Set.toFinite (D.active k)).mem_toFinset.mpr ha, hs j hjs⟩)
    rw [(D.mem_active k j).not_left.mp hna]
    exact BCHGroup.log_one

variable {a} (S : κ → Set V) (ν : κ → Λ →+ ℤ)

open Classical in
/-- At a regular point, the logarithm of the combined label is the sum over the families of
the signed family logarithms of the families whose support contains the point. The sum runs
over any finite set of families containing those of the active walls. -/
theorem log_combinedLabel_eq_sum_familyLog (hS : ∀ j, (D.wall j).support = S (a j))
    (hν : ∀ j, (D.wall j).normal = ν (a j)) (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) (t : Finset κ)
    (ht : ∀ j ∈ D.active k, a j ∈ t) :
    BCHGroup.log (D.combinedLabel k θ v hθ) = ∑ i ∈ t,
      if θ ∈ S i then
        (if 0 < h.realCharacter (ν i) v then -1 else 1 : ℤ) • D.familyLog a k i else 0 := by
  classical
  let := Fintype.ofFinite (D.active k)
  let A := (Set.toFinite (D.active k)).toFinset
  let G (j : ι) : d.lieTruncation ℒ k := if θ ∈ (D.wall j).support then
    (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ) •
      BCHGroup.log (L := d.lieTruncation ℒ k) (CompletedGroup.projection k (D.wall j).label)
    else 0
  have hsum : BCHGroup.log (D.combinedLabel k θ v hθ) = ∑ j ∈ A, G j :=
    (D.log_combinedLabel_eq_sum k θ v hθ).trans
      (Finset.sum_subtype A (fun j => (Set.toFinite (D.active k)).mem_toFinset) G).symm
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := a) (t := t)
    fun j hj => ht j ((Set.toFinite (D.active k)).mem_toFinset.mp hj)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.familyLog_eq_sum a k i (A.filter (a · = i)) (fun j hj => (Finset.mem_filter.mp hj).2)
    fun j hj hji =>
      Finset.mem_filter.mpr ⟨(Set.toFinite (D.active k)).mem_toFinset.mpr hj, hji⟩]
  by_cases hθi : θ ∈ S i
  · simp only [hθi, ↓reduceIte, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji := (Finset.mem_filter.mp hj).2
    simp only [G, hS j, hν j, hji, hθi, ↓reduceIte]
  · simp only [hθi, ↓reduceIte]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hji := (Finset.mem_filter.mp hj).2
    simp only [G, hS j, hji, hθi, ↓reduceIte]

/-- Two diagrams whose walls are grouped into families with the same supports and normals are
equivalent at order `k` when their family logarithms agree at order `k`. -/
theorem levelEquivalent_of_familyLog_eq (E : DirectedDiagram (d := d) h H ι') {b : ι' → κ}
    (hDS : ∀ j, (D.wall j).support = S (a j)) (hDν : ∀ j, (D.wall j).normal = ν (a j))
    (hES : ∀ j, (E.wall j).support = S (b j)) (hEν : ∀ j, (E.wall j).normal = ν (b j))
    (k : ℕ) (hlog : ∀ i, D.familyLog a k i = E.familyLog b k i) :
    D.LevelEquivalent E k := by
  classical
  let t := (Set.toFinite (D.active k)).toFinset.image a ∪
    (Set.toFinite (E.active k)).toFinset.image b
  refine (D.levelEquivalent_iff_combinedLabel_eq E k).mpr fun θ v hD hE _ _ =>
    BCHGroup.log_injective ?_
  rw [D.log_combinedLabel_eq_sum_familyLog S ν hDS hDν k θ v hD t fun j hj =>
      Finset.mem_union_left _
        (Finset.mem_image_of_mem a ((Set.toFinite (D.active k)).mem_toFinset.mpr hj)),
    E.log_combinedLabel_eq_sum_familyLog S ν hES hEν k θ v hE t fun j hj =>
      Finset.mem_union_right _
        (Finset.mem_image_of_mem b ((Set.toFinite (E.active k)).mem_toFinset.mpr hj))]
  simp only [hlog]

section Pushforward

variable {Γ' Λ' V' : Type*} {L' : Type u} [AddCommGroup Γ'] [AddCommGroup Λ']
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [DecidableEq Γ']
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ' : Γ' →+ Λ'} {ℳ : Γ' → Submodule R L'} {e : PositiveDegrees Γ'}
  [GradedLieAlgebra ℳ] [IsPositiveGrading e ℳ]
  {i' : Λ' →+ V'} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H' : DirectedWallSpaces ρ' ℳ} (P : DirectedWall.Pushforward d e h h' H H') (a)

/-- Pushforward maps the family logarithms at the order of the cutoff modulus by the truncated
Lie map. -/
theorem familyLog_pushforward (k : ℕ) (i : κ) :
    (D.pushforward P).familyLog a k i =
      P.lieHom.truncatedMap k le_rfl (D.familyLog a (P.degreeMap.modulus k) i) := by
  classical
  let s := (Set.toFinite (D.active (P.degreeMap.modulus k))).toFinset.filter (a · = i)
  have hs : ∀ j ∈ s, a j = i := fun j hj => (Finset.mem_filter.mp hj).2
  rw [(D.pushforward P).familyLog_eq_sum a k i s hs fun j hj hji => Finset.mem_filter.mpr
      ⟨(Set.toFinite _).mem_toFinset.mpr (D.active_pushforward_subset P k le_rfl hj), hji⟩,
    D.familyLog_eq_sum a _ i s hs fun j hj hji =>
      Finset.mem_filter.mpr ⟨(Set.toFinite _).mem_toFinset.mpr hj, hji⟩, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.projection_pushforward_wall_label P k le_rfl j]
  exact LieHom.log_bchGroupMap _ _

end Pushforward

end Mei.DirectedDiagram
