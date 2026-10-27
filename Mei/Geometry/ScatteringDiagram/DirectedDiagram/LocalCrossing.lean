/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Convex.Polyhedron.Path.LocalCrossing

/-!
# Combined labels at regular directed wall germs

At a fixed cutoff, all active walls through a point outside singular support have
commuting labels. Their combined label in a transverse direction is the unordered
product of the signed projected labels. Every enumeration gives the same value.
Any segment crossing precisely this germ computes that label, and sufficiently
short transverse segments realize it. These are the local crossing values used
when replacing an indexed wall presentation by an adapted polyhedral complex.

The construction uses `DirectedDiagram.activeLabels_commute`, the grouped products
of `WallComplement.segmentPathProduct`, and the short-segment isolation theorem
`WallComplement.eventually_exists_crossings_iff`. The sign convention follows
Travis Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), equation (8).
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex WallComplement

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {ι : Type*}
  (D : DirectedDiagram (d := d) h H ι)

/-- The signed combined label of all active indexed walls through a regular point.
The vector is the crossing velocity: positive normal evaluation contributes the
inverse label. In geometric applications it is transverse to the incident walls. -/
def combinedLabel (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    d.truncatedGroup ℒ k := by
  classical
  let S := (Set.toFinite {j : D.active k | θ ∈ (D.wall j).support}).toFinset
  exact S.noncommProd
    (fun j => CompletedGroup.projection k (D.wall j).label ^
      (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)) (by
    intro a ha b hb _
    have ha : θ ∈ (D.wall a).support := by simpa [S] using ha
    have hb : θ ∈ (D.wall b).support := by simpa [S] using hb
    apply (D.activeLabels_commute k a b ?_).zpow_zpow
    apply AffineSubspace.ext_of_direction_eq _
      ⟨θ, subset_affineSpan ℝ _ ha, subset_affineSpan ℝ _ hb⟩
    by_contra hne
    exact hθ (mem_singularSupport.mpr (Or.inr ⟨a, b, hne, ha, hb⟩)))

/-- Any finite set containing exactly the active incident indices computes the
combined label, independently of the proof of commutation. -/
theorem combinedLabel_eq_noncommProd (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (S : Finset (D.active k)) (hS : ∀ j, j ∈ S ↔ θ ∈ (D.wall j).support)
    (comm : (S : Set (D.active k)).Pairwise (fun a b =>
      Commute (CompletedGroup.projection k (D.wall a).label ^
        (if 0 < h.realCharacter (D.wall a).normal v then -1 else 1 : ℤ))
        (CompletedGroup.projection k (D.wall b).label ^
          (if 0 < h.realCharacter (D.wall b).normal v then -1 else 1 : ℤ)))) :
    D.combinedLabel k θ v hθ = S.noncommProd
      (fun j => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)) comm := by
  classical
  unfold combinedLabel
  apply Finset.noncommProd_congr _ (fun _ _ => rfl)
  ext j
  simpa using (hS j).symm

/-- Every enumeration without repetitions of the active incident walls gives the
same combined label. Repeated supports with distinct indices remain separate factors. -/
theorem combinedLabel_eq_prod (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (l : List (D.active k)) (hl : l.Nodup)
    (hm : ∀ j, j ∈ l ↔ θ ∈ (D.wall j).support) :
    D.combinedLabel k θ v hθ =
      (l.map fun j : D.active k => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)).prod := by
  classical
  unfold combinedLabel
  have hs : (Set.toFinite {j : D.active k | θ ∈ (D.wall j).support}).toFinset =
      l.toFinset := by ext j; simpa using (hm j).symm
  exact (Finset.noncommProd_congr hs (fun _ _ => rfl) _).trans
    (Finset.noncommProd_toFinset l _ _ hl)

/-- Lowering the cutoff projects a regular combined label to the combined label
of the surviving walls, for every vector `v`. Walls killed by truncation
contribute no factor. -/
theorem truncation_combinedLabel {k l : ℕ} (hkl : k ≤ l) (θ v : V)
    (hl : θ ∉ singularSupport (fun j : D.active l => (D.wall j).support))
    (hk : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.combinedLabel l θ v hl) =
      D.combinedLabel k θ v hk := by
  classical
  -- Filter an enumeration of the incident walls to those surviving at the lower cutoff.
  let S := (Set.toFinite {j : D.active l | θ ∈ (D.wall j).support}).toFinset.toList
  let q : D.active l → Option (D.active k) := fun j =>
    if hj : j.val ∈ D.active k then some ⟨j.val, hj⟩ else none
  have hq (a : D.active l) (b : D.active k) : q a = some b ↔ a.val = b.val := by
    simp only [q]
    split_ifs with ha
    · simp only [Option.some.injEq, Subtype.ext_iff]
    · simp only [false_iff]
      intro hab
      exact ha (hab ▸ b.property)
  have hnodup : (S.filterMap q).Nodup := by
    apply List.Nodup.filterMap ?_ (Finset.nodup_toList _)
    intro a a' b hab ha'b
    exact Subtype.ext ((hq a b).mp hab |>.trans ((hq a' b).mp ha'b).symm)
  have hmem (b : D.active k) : b ∈ S.filterMap q ↔ θ ∈ (D.wall b).support := by
    simp only [List.mem_filterMap, hq]
    constructor
    · rintro ⟨a, ha, hab⟩
      have ha : θ ∈ (D.wall a).support := by simpa [S] using ha
      simpa only [hab] using ha
    · intro hb
      exact ⟨⟨b.val, D.active_mono hkl b.property⟩, by simpa [S] using hb, rfl⟩
  rw [D.combinedLabel_eq_prod l θ v hl S (Finset.nodup_toList _)
    (fun j => by simp [S]), D.combinedLabel_eq_prod k θ v hk _ hnodup hmem]
  -- Work with the tower group instances when mapping the enumerated product.
  let F := ((d.groupTower ℒ).map (CategoryTheory.homOfLE hkl).op).hom
  have hproj (a : D.active l) : F (CompletedGroup.projection l (D.wall a).label) =
      CompletedGroup.projection k (D.wall a).label :=
    CompletedGroup.map_projection k l hkl (D.wall a).label
  have hprod (s : List (D.active l)) :
      F
        ((s.map fun j : D.active l => CompletedGroup.projection l (D.wall j).label ^
          (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)).prod) =
      ((s.filterMap q).map fun j : D.active k => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ)).prod := by
    induction s with
    | nil => exact map_one F
    | cons a s ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [map_mul, map_zpow, hproj, ih]
      by_cases ha : a.val ∈ D.active k
      · simp only [List.filterMap_cons, q, dite_eq_left ha, List.map_cons, List.prod_cons]
      · have hone : CompletedGroup.projection k (D.wall a).label = 1 := by
          simpa only [mem_active, not_not] using ha
        simp only [List.filterMap_cons, q, dite_eq_right ha, hone, one_zpow, one_mul]
  -- The tower transition is the BCH truncation map, as in `groupTower_map_hom`.
  exact hprod S

/-- A point on no active wall has trivial combined label. -/
@[simp]
theorem combinedLabel_eq_one_of_forall_notMem (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hoff : ∀ j : D.active k, θ ∉ (D.wall j).support) :
    D.combinedLabel k θ v hθ = 1 := by
  exact (D.combinedLabel_eq_prod k θ v hθ [] (by simp) (by simp [hoff])).trans (by rfl)

/-- Positive rescaling of a crossing velocity preserves the combined label. -/
@[simp]
theorem combinedLabel_smul_pos (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    {r : ℝ} (hr : 0 < r) : D.combinedLabel k θ (r • v) hθ = D.combinedLabel k θ v hθ := by
  classical
  unfold combinedLabel
  apply Finset.noncommProd_congr rfl
  intro j _
  simp only [map_smul, smul_eq_mul, mul_pos_iff_of_pos_left hr]
  rfl

/-- Reversing a transverse crossing direction inverts the combined label. -/
@[simp]
theorem combinedLabel_neg (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0) :
    D.combinedLabel k θ (-v) hθ = (D.combinedLabel k θ v hθ)⁻¹ := by
  classical
  unfold combinedLabel
  refine (Finset.noncommProd_congr rfl
    (g := fun j : D.active k =>
      (CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ))⁻¹)
    ?_ _).trans (Finset.noncommProd_inv _ _ _)
  intro j hj
  have hne := hv j (by simpa using hj)
  have hsign : (if 0 < h.realCharacter (D.wall j).normal (-v) then -1 else 1 : ℤ) =
      -(if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ) := by
    rw [map_neg]
    split_ifs <;> norm_num <;> grind
  rw [hsign, zpow_neg]

/-- A segment meeting precisely one regular wall germ computes its combined label
in the direction of the segment, including all coincident indexed walls. -/
theorem levelPathProduct_toPath_eq_combinedLabel (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)} (e : x ⟶ y)
    (θ : V) (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (t : ℝ) (hcross : ∀ j s, (j, s) ∈ crossings x y ↔
      θ ∈ (D.wall j).support ∧ s = t) :
    D.levelPathProduct k e.toPath = D.combinedLabel k θ (y.val - x.val) hθ := by
  classical
  rw [D.levelPathProduct_eq_wallPathProduct k e.toPath (D.activeLabels_commute k),
    Quiver.Path.wallPathProduct_toPath]
  unfold combinedLabel
  apply segmentPathProduct_eq_noncommProd_of_crossings
  simpa using hcross

/-- Arbitrarily short transverse segments through a regular point realize its
combined label at the given cutoff. -/
theorem eventually_exists_levelPathProduct_eq_combinedLabel (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support))
    (hv : ∀ j : D.active k, θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∃ (x y : WallComplement (fun j : D.active k => (D.wall j).support)) (e : x ⟶ y),
        x.val = θ - a • v ∧ y.val = θ + a • v ∧
        D.levelPathProduct k e.toPath = D.combinedLabel k θ v hθ := by
  let := h.finiteDimensional
  have htrans (j : D.active k) (hj : θ ∈ (D.wall j).support) :
      v ∉ (affineSpan ℝ (D.wall j).support).direction := by
    rw [(D.wall j).direction_support, LinearMap.mem_ker]
    exact hv j hj
  filter_upwards [eventually_exists_crossings_iff
    (fun j : D.active k => (D.wall j).isConvexPolyhedron.isClosed) hθ htrans,
    self_mem_nhdsWithin] with a ha ha0
  obtain ⟨x, y, e, hx, hy, hcross⟩ := ha
  refine ⟨x, y, e, hx, hy, ?_⟩
  rw [D.levelPathProduct_toPath_eq_combinedLabel k e θ hθ (1 / 2) hcross]
  have hd : y.val - x.val = (2 * a) • v := by rw [hx, hy]; module
  rw [hd, D.combinedLabel_smul_pos k θ v hθ (by have ha0 : 0 < a := ha0; positivity)]

end Mei.DirectedDiagram
