/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Germ
public import Mei.Geometry.Affine.Generic

/-!
# Completed crossing labels at generic wall points

A point `θ` is *regular* for a directed diagram `D` (`DirectedDiagram.IsRegular`) when it lies
outside the singular support of the walls active at every order. It is a *generic point* of an
affine subspace `A` (`DirectedDiagram.IsGenericPoint`) when moreover `θ ∈ A` and every wall active
at some order and passing through `θ` has affine span `A`. At a generic point, every direction
`v ∉ A.direction` is transverse to all walls through `θ`
(`DirectedDiagram.IsGenericPoint.realCharacter_normal_ne_zero`).

Generic points exist in abundance. For an affine hyperplane `A`, the points of `A` that are not
generic for `D` lie in countably many affine subspaces, none of which contains `A`: at each order,
the singular support of the finitely many active walls is covered by finitely many affine
subspaces of codimension at least two, and the active walls whose affine span is not `A` meet
`A` inside their own spans (`DirectedDiagram.exists_obstacles`). Hence every nonempty relatively
open subset of `A` contains a point that is generic for `D`, and also, after an affine equivalence
`e`, generic for a second diagram `E` on the image of `A`
(`DirectedDiagram.exists_isGenericPoint`, `DirectedDiagram.exists_isGenericPoint_pair`). No
consistency, refinement relation or bound on the walls is needed.

At each order `k`, the combined crossing label at a point outside the singular support is the
product of the signed projected labels over the finite set `DirectedDiagram.incidentActive` of
active walls through the point (`DirectedDiagram.combinedLabel_eq_noncommProd_incidentActive`);
these signed labels commute pairwise (`DirectedDiagram.pairwise_commute_incidentActive`).

At a regular point, the combined crossing labels of `D` at all orders
(`DirectedDiagram.combinedLabel`) are compatible under truncation, so they form an element of the
completed group, the *germ label* `DirectedDiagram.germLabel` of `D` at `θ` in the direction `v`.
It does not change under positive rescaling of `v` (`DirectedDiagram.germLabel_smul_pos`) and is
inverted by reversing a transverse direction (`DirectedDiagram.germLabel_neg`). Equivalent
diagrams have the same germ label at a common generic point of `A`, for every direction
`v ∉ A.direction` (`DirectedDiagram.Equivalent.germLabel_eq`). In contrast to the comparison of
function-wall groupings in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Equivalence`, this requires no
grouping and no matching of crossing germs: the germ label is an invariant of the completed
class at each common generic point. It is the label of "the wall function on a ray" of a
scattering diagram in Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1.1 (arXiv:1411.1394v2), and in Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, Theorem 9.5 (arXiv:2503.03719v1).

The comparison uses `DirectedDiagram.LevelEquivalent.combinedLabel_eq`, and the existence uses
`Mei.Convex.exists_finite_singularSupport_cover` and
`AffineSubspace.exists_mem_open_avoid_of_not_le`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι κ : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}
  (D : DirectedDiagram (d := d) h H ι)

section Generic

/-- A point is regular for `D` when it lies outside the singular support of the walls active at
every order. -/
def IsRegular (θ : V) : Prop :=
  ∀ k, θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)

/-- The defining condition of a regular point. -/
theorem isRegular_iff (θ : V) :
    D.IsRegular θ ↔ ∀ k, θ ∉ singularSupport (fun j : D.active k => (D.wall j).support) :=
  Iff.rfl

variable {D} in
/-- A regular point is regular for the walls active at each order. -/
theorem IsRegular.notMem_singularSupport {θ : V} (hθ : D.IsRegular θ) (k : ℕ) :
    θ ∉ singularSupport (fun j : D.active k => (D.wall j).support) :=
  hθ k

/-- A generic point of the affine subspace `A` for `D`: a point of `A`, regular for `D`, such that
every wall active at some order and passing through it has affine span `A`. -/
structure IsGenericPoint (A : AffineSubspace ℝ V) (θ : V) : Prop where
  /-- The point lies on `A`. -/
  mem : θ ∈ A
  /-- The point is regular for the walls active at every order. -/
  isRegular : D.IsRegular θ
  /-- Every active wall through the point spans `A`. -/
  affineSpan_eq {k : ℕ} (j : D.active k) :
    θ ∈ (D.wall j).support → affineSpan ℝ (D.wall j).support = A

variable {D}

/-- The defining conditions of a generic point. -/
theorem isGenericPoint_iff {A : AffineSubspace ℝ V} {θ : V} :
    D.IsGenericPoint A θ ↔ θ ∈ A ∧ D.IsRegular θ ∧
      ∀ (k : ℕ) (j : D.active k), θ ∈ (D.wall j).support → affineSpan ℝ (D.wall j).support = A :=
  ⟨fun hθ => ⟨hθ.mem, hθ.isRegular, fun _ => hθ.affineSpan_eq⟩,
    fun hθ => ⟨hθ.1, hθ.2.1, hθ.2.2 _⟩⟩

/-- At a generic point of `A`, every direction outside the direction of `A` is transverse to all
active walls through the point. -/
theorem IsGenericPoint.realCharacter_normal_ne_zero {A : AffineSubspace ℝ V} {θ : V}
    (hθ : D.IsGenericPoint A θ) {v : V} (hv : v ∉ A.direction) {k : ℕ} (j : D.active k)
    (hj : θ ∈ (D.wall j).support) : h.realCharacter (D.wall j).normal v ≠ 0 := by
  rwa [← hθ.affineSpan_eq j hj, (D.wall j).direction_support, LinearMap.mem_ker] at hv

variable (D)

/-- **Obstacles to generic points.** For a nonempty affine hyperplane `A`, there are finitely many
affine subspaces at each order, none containing `A`, such that every point of `A` outside all of
them is a generic point of `A` for `D`. They are a cover of the singular support of the active
walls by subspaces of codimension at least two, and the affine spans of the active walls whose
span is not `A`. -/
theorem exists_obstacles (A : AffineSubspace ℝ V) (hA : (A : Set V).Nonempty)
    (hdim : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V) :
    ∃ O : ℕ → Finset (AffineSubspace ℝ V), (∀ k, ∀ B ∈ O k, ¬ A ≤ B) ∧
      ∀ θ ∈ A, (∀ k, ∀ B ∈ O k, θ ∉ B) → D.IsGenericPoint A θ := by
  classical
  have := h.finiteDimensional
  choose S hS hSdim using fun k => exists_finite_singularSupport_cover
    (fun j : D.active k => (D.wall j).support) (fun j => (D.wall j).isConvexPolyhedron)
    (fun j => (D.wall j).finrank_direction_add_one)
  let T (k : ℕ) : Finset (AffineSubspace ℝ V) :=
    (Set.toFinite {j : D.active k | affineSpan ℝ (D.wall j).support ≠ A}).toFinset.image
      fun j : D.active k => affineSpan ℝ (D.wall j).support
  refine ⟨fun k => S k ∪ T k, fun k B hB hle => ?_, fun θ hθ havoid =>
    ⟨hθ, fun k hk => ?_, fun {k} j hj => ?_⟩⟩
  · rcases Finset.mem_union.mp hB with hB | hB
    · have := Submodule.finrank_mono (AffineSubspace.direction_le hle)
      have := hSdim k B hB
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
      have hj : affineSpan ℝ (D.wall j).support ≠ A := by simpa using hj
      have hfin := (D.wall j).finrank_direction_add_one
      exact hj (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
        (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (by omega))
        hA hle).symm
  · obtain ⟨B, hB, hθB⟩ := Set.mem_iUnion₂.mp (hS k hk)
    exact havoid k B (Finset.mem_union_left _ hB) hθB
  · by_contra hne
    exact havoid k _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, by simpa using hne, rfl⟩))
      (subset_affineSpan ℝ _ hj)

section Pair

variable {Γ' Λ' R' L' V' κ : Type*} [AddCommGroup Γ'] [AddCommGroup Λ']
  [CommRing R'] [Algebra ℚ R'] [LieRing L'] [LieAlgebra R' L']
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R' L'] [DecidableEq Γ']
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ' : Γ' →+ Λ'} {ℳ : Γ' → Submodule R' L'} {d' : PositiveDegrees Γ'}
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i' : Λ' →+ V'} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H' : DirectedWallSpaces ρ' ℳ}

/-- **Common generic points.** Let `A` be an affine hyperplane, `e` an affine equivalence and `E` a
second directed diagram on the target of `e`. Every relatively open subset `U ∩ A` that is
nonempty contains a point `θ` that is a generic point of `A` for `D` and whose image `e θ` is a
generic point of the image of `A` for `E`. -/
theorem exists_isGenericPoint_pair (E : DirectedDiagram (d := d') h' H' κ) (e : V ≃ᴬ[ℝ] V')
    (A : AffineSubspace ℝ V) (hdim : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V)
    {U : Set V} (hU : IsOpen U) (hne : (U ∩ A).Nonempty) :
    ∃ θ ∈ U ∩ A, D.IsGenericPoint A θ ∧
      E.IsGenericPoint (A.map e.toAffineEquiv.toAffineMap) (e θ) := by
  have := h.finiteDimensional
  let f := e.toAffineEquiv.toAffineMap
  have hA : (A : Set V).Nonempty := hne.mono inter_subset_right
  have hdim' : Module.finrank ℝ (A.map f).direction + 1 = Module.finrank ℝ V' := by
    rw [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap,
      LinearEquiv.finrank_map_eq, ← e.toAffineEquiv.linear.finrank_eq, hdim]
  obtain ⟨O, hO, hgen⟩ := D.exists_obstacles A hA hdim
  obtain ⟨O', hO', hgen'⟩ := E.exists_obstacles (A.map f) (hA.image f) hdim'
  let B : (Σ k, (O k ⊕ O' k)) → AffineSubspace ℝ V := fun x => x.2.elim (↑) fun B => B.1.comap f
  have hB (x) : ¬ A ≤ B x := by
    obtain ⟨k, b | b⟩ := x
    · exact hO k b b.2
    · exact fun hle => hO' k b b.2 (AffineSubspace.map_le_iff_le_comap.mpr hle)
  obtain ⟨⟨θ, hθA⟩, hθU, hθ⟩ := A.exists_mem_open_avoid_of_not_le B hB
    (hU.preimage continuous_subtype_val) (by obtain ⟨x, hxU, hxA⟩ := hne; exact ⟨⟨x, hxA⟩, hxU⟩)
  refine ⟨θ, ⟨hθU, hθA⟩, hgen θ hθA fun k b hb => hθ ⟨k, .inl ⟨b, hb⟩⟩,
    hgen' (e θ) (AffineSubspace.mem_map_of_mem f hθA) fun k b hb => hθ ⟨k, .inr ⟨b, hb⟩⟩⟩

end Pair

/-- **Generic points.** Every nonempty relatively open subset `U ∩ A` of an affine hyperplane `A`
contains a generic point of `A` for `D`. -/
theorem exists_isGenericPoint (A : AffineSubspace ℝ V)
    (hdim : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V)
    {U : Set V} (hU : IsOpen U) (hne : (U ∩ A).Nonempty) :
    ∃ θ ∈ U ∩ A, D.IsGenericPoint A θ :=
  (D.exists_isGenericPoint_pair D (ContinuousAffineEquiv.refl ℝ V) A hdim hU hne).imp
    fun _ hθ => ⟨hθ.1, hθ.2.1⟩

end Generic

section Incident

/-- The walls active at order `k` whose support contains `θ`, as a finite set. -/
def incidentActive (k : ℕ) (θ : V) : Finset (D.active k) :=
  (Set.toFinite {j : D.active k | θ ∈ (D.wall j).support}).toFinset

/-- Membership in the finite set of active walls through a point. -/
@[simp]
theorem mem_incidentActive {k : ℕ} {θ : V} {j : D.active k} :
    j ∈ D.incidentActive k θ ↔ θ ∈ (D.wall j).support := by
  simp [incidentActive]

/-- At a point outside the singular support of the walls active at order `k`, the signed
projected labels of the active walls through the point commute pairwise, for every direction
`v`. -/
theorem pairwise_commute_incidentActive (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    (D.incidentActive k θ : Set (D.active k)).Pairwise fun x y =>
      Commute (CompletedGroup.projection k (D.wall x).label ^
          (if 0 < h.realCharacter (D.wall x).normal v then -1 else 1 : ℤ))
        (CompletedGroup.projection k (D.wall y).label ^
          (if 0 < h.realCharacter (D.wall y).normal v then -1 else 1 : ℤ)) := by
  intro x hx y hy _
  exact (D.activeLabels_commute k x y (affineSpan_eq_of_notMem_singularSupport
    (W := fun j : D.active k => (D.wall j).support) hθ
    (D.mem_incidentActive.mp hx) (D.mem_incidentActive.mp hy))).zpow_zpow _ _

/-- The combined crossing label is the product of the signed projected labels of the active walls
through the point. -/
theorem combinedLabel_eq_noncommProd_incidentActive (k : ℕ) (θ v : V)
    (hθ : θ ∉ singularSupport (fun j : D.active k => (D.wall j).support)) :
    D.combinedLabel k θ v hθ = (D.incidentActive k θ).noncommProd
      (fun j => CompletedGroup.projection k (D.wall j).label ^
        (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ))
      (D.pairwise_commute_incidentActive k θ v hθ) :=
  D.combinedLabel_eq_noncommProd k θ v hθ _ (fun _ => D.mem_incidentActive) _

end Incident

section GermLabel

/-- The *germ label* of `D` at a regular point `θ` in the direction `v`: the element of the
completed group whose order-`k` projection is the combined crossing label of the walls active at
order `k`. For `v` pairing negatively with the normals of the walls through `θ`, it is the
convergent product of their labels. -/
def germLabel (θ v : V) (hθ : D.IsRegular θ) : d.completedBCHGroup ℒ :=
  ⟨fun k => D.combinedLabel k θ v (hθ.notMem_singularSupport k),
    (mem_completedGroup_iff _ _).mpr fun _ _ hkl => D.truncation_combinedLabel hkl θ v _ _⟩

/-- The finite-order projections of a germ label are the combined crossing labels. -/
@[simp]
theorem projection_germLabel (θ v : V) (hθ : D.IsRegular θ) (k : ℕ) :
    CompletedGroup.projection k (D.germLabel θ v hθ) =
      D.combinedLabel k θ v (hθ.notMem_singularSupport k) :=
  CompletedGroup.projection_apply k _

/-- The germ label is the unique element with the combined crossing labels as projections. -/
theorem eq_germLabel_iff (θ v : V) (hθ : D.IsRegular θ) (l : d.completedBCHGroup ℒ) :
    l = D.germLabel θ v hθ ↔
      ∀ k, CompletedGroup.projection k l = D.combinedLabel k θ v (hθ.notMem_singularSupport k) :=
  ⟨by rintro rfl k; exact D.projection_germLabel θ v hθ k,
    fun hl => CompletedGroup.ext fun k => (hl k).trans (D.projection_germLabel θ v hθ k).symm⟩

/-- Positive rescaling of the direction preserves the germ label. -/
@[simp]
theorem germLabel_smul_pos (θ v : V) (hθ : D.IsRegular θ) {r : ℝ} (hr : 0 < r) :
    D.germLabel θ (r • v) hθ = D.germLabel θ v hθ :=
  ((D.eq_germLabel_iff θ (r • v) hθ _).mpr fun k => by
    rw [projection_germLabel, combinedLabel_smul_pos _ _ _ _ _ hr]).symm

/-- Reversing a direction transverse to every active wall through `θ` inverts the germ label. -/
theorem germLabel_neg (θ v : V) (hθ : D.IsRegular θ)
    (hv : ∀ (k : ℕ) (j : D.active k), θ ∈ (D.wall j).support →
      h.realCharacter (D.wall j).normal v ≠ 0) :
    D.germLabel θ (-v) hθ = (D.germLabel θ v hθ)⁻¹ :=
  ((D.eq_germLabel_iff θ (-v) hθ _).mpr fun k => by
    rw [map_inv, projection_germLabel]
    exact (D.combinedLabel_neg k θ v _ (hv k)).symm).symm

variable {D} {E : DirectedDiagram (d := d) h H κ}

/-- **Germ labels of equivalent diagrams.** Equivalent directed diagrams have the same germ label
at a common generic point of an affine subspace `A`, in every direction outside the direction of
`A`. -/
theorem Equivalent.germLabel_eq (hDE : D.Equivalent E) {A : AffineSubspace ℝ V} {θ v : V}
    (hD : D.IsGenericPoint A θ) (hE : E.IsGenericPoint A θ) (hv : v ∉ A.direction) :
    D.germLabel θ v hD.isRegular = E.germLabel θ v hE.isRegular :=
  CompletedGroup.ext fun k => by
    rw [projection_germLabel, projection_germLabel]
    exact ((equivalent_iff D E).mp hDE k).combinedLabel_eq θ v _ _
      (hD.realCharacter_normal_ne_zero hv) (hE.realCharacter_normal_ne_zero hv)

end GermLabel

end Mei.DirectedDiagram
