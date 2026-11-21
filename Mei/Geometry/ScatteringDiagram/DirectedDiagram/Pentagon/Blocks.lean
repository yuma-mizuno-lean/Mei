/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Binomial
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Sigma

/-!
# Ray presentations of commuting blocks of type `A₂`

Let `D` be the ray presentation (`DirectedDiagram.IsRayFactorPresentation`), in the tropical vertex
wall spaces of `(Γ, Λ, ρ)`, of labels `g_j` on the hyperplanes `{μ_j = 0}` through the origin. It
is *of type `A₂` in blocks* (`DirectedDiagram.IsTypeA₂BlocksPresentation`) for pairs of indices
`(j₁ b, j₂ b)`, `b : β`, with degrees `n₁ b, n₂ b` and coefficients `c₁ b, c₂ b`, when the
`2 |β|` indices `j₁ b, j₂ b` are distinct, every pair satisfies the conditions of
`DirectedDiagram.IsTypeA₂Presentation` (binomial labels `θ[μ_{j₁ b}, n₁ b, c₁ b]` and
`θ[μ_{j₂ b}, n₂ b, c₂ b]`, with `μ_{j₁ b}(ρ n₂ b) = -1` and `μ_{j₂ b}(ρ n₁ b) = 1`), and the labels
of two walls commute unless both walls lie over the hyperplanes of one block. The remaining
indices are *isolated*; their walls may have arbitrary labels commuting with all labels of `D`.

* The walls of `D` over the two hyperplanes of a block `b` form a ray presentation of type `A₂`
  without isolated indices (`IsTypeA₂BlocksPresentation.isTypeA₂Presentation_restrictSigma`).
* For finitely many blocks, adding to `D` one outgoing wall for every block `b`, the
  half-hyperplane `{μ_{j₁ b} + μ_{j₂ b} = 0, μ_{j₁ b} ≥ 0}` labelled by the binomial label of
  `1 + c₁ b c₂ b z^{n₁ b + n₂ b}` (`IsTypeA₂BlocksPresentation.outgoingWall`), gives a consistent
  diagram, the *blocks diagram* (`IsTypeA₂BlocksPresentation.blocksDiagram_consistent`). Its new
  walls are outgoing, so it is an outgoing completion of `D`
  (`IsTypeA₂BlocksPresentation.isOutgoingCompletion_blocksDiagram`) and represents its scattering
  class (`IsTypeA₂BlocksPresentation.scat_eq_toClass_blocksDiagram`).
* If `D` has a grouping of its walls into function walls which is positive for the image of
  `S[Q]` under a semiring map `φ : S →+* R`, every product `c₁ b c₂ b` lies in the image of `φ`,
  and `Q` contains for every block an exponent `p` with `-p ∈ Q` and
  `(μ_{j₁ b} + μ_{j₂ b})(ρ p) = 1`, the blocks diagram is a positive wall representative of the
  scattering class
  (`IsTypeA₂BlocksPresentation.isPositiveWallRepresentative_blocksDiagram_of_isPositive`,
  `IsTypeA₂BlocksPresentation.exists_isPositiveWallRepresentative_scat_of_isPositive`).

The consistency splits the blocks diagram into the pentagon diagrams of the blocks and the walls
at the isolated indices, whose labels commute across parts
(`DirectedDiagram.consistent_of_restrict_preimage`); the outgoing walls of distinct blocks commute
since each outgoing label is a product of the two binomial labels of its block and their inverses
(`DirectedDiagram.IsTypeA₂Presentation.commute_outgoingWall_label`). For a single block the walls
of the blocks diagram are those of the pentagon diagram of `DirectedDiagram.IsTypeA₂Presentation`,
with the outgoing wall indexed by `Σ _ : β, Unit` instead of `Unit`. A concrete instance is in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Examples`.

Without isolated indices, the blocks diagram is the union of commuting scattering diagrams of type
`A₂` of
Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*, Example 1.6
(arXiv:0902.0779v3), and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Example 1.15 (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra Set

variable {R Γ Λ V ι β : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [AddCommGroup Λ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {latticeMap : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice latticeMap}

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

namespace IsTypeA₂BlocksPresentation

/-- The block containing the index `j`, for the blocks `{j₁ b, j₂ b}`: `some b` if `j` is `j₁ b` or
`j₂ b` (unique if `Sum.elim j₁ j₂` is injective, `blockOf_eq_some_iff`), and `none` if `j` lies in
no block. -/
def blockOf (j₁ j₂ : β → ι) (j : ι) : Option β :=
  (Function.partialInv (Sum.elim j₁ j₂) j).map (Sum.elim id id)

/-- If the indices `j₁ b, j₂ b` are pairwise distinct, `j` lies in the block `b` exactly when it is
`j₁ b` or `j₂ b`. -/
theorem blockOf_eq_some_iff {j₁ j₂ : β → ι} (hj : Function.Injective (Sum.elim j₁ j₂)) {j : ι}
    {b : β} : blockOf j₁ j₂ j = some b ↔ j = j₁ b ∨ j = j₂ b := by
  rw [blockOf, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a | a, ha, rfl⟩
    · exact Or.inl ((hj.isPartialInv _ j).mp ha).symm
    · exact Or.inr ((hj.isPartialInv _ j).mp ha).symm
  · rintro (rfl | rfl)
    exacts [⟨.inl b, Function.partialInv_left hj (.inl b), rfl⟩,
      ⟨.inr b, Function.partialInv_left hj (.inr b), rfl⟩]

variable {μ : ι → Λ →+ ℤ}

/-- The block of a wall of the blocks diagram: the block of its hyperplane for a wall of `D`, and
`b` for the outgoing wall of the block `b`. -/
def blockOfIndex (j₁ j₂ : β → ι) :
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ (Σ _ : β, Unit) → Option β :=
  Sum.elim (fun x => blockOf j₁ j₂ x.1) fun z => some z.1

@[simp]
theorem blockOfIndex_inl (j₁ j₂ : β → ι)
    (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    blockOfIndex j₁ j₂ (.inl x : _ ⊕ (Σ _ : β, Unit)) = blockOf j₁ j₂ x.1 := (rfl)

@[simp]
theorem blockOfIndex_inr (j₁ j₂ : β → ι) (b : β) (u : Unit) :
    blockOfIndex j₁ j₂ (.inr ⟨b, u⟩ : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ _) =
      some b := (rfl)

/-- The walls of the pentagon diagram of the block `b` as walls of the blocks diagram: a wall over
the hyperplane of `j₁ b` or `j₂ b` is the same wall of `D`, and the outgoing wall is the outgoing
wall of `b`. -/
def blockEmbedding (j₁ j₂ : β → ι) (b : β) :
    (Σ j : ({j₁ b, j₂ b} : Set ι), {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit →
      (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ (Σ _ : β, Unit) :=
  Sum.map (Sigma.map Subtype.val fun _ => id) (Sigma.mk (β := fun _ => Unit) b)

/-- The embedding of the walls of a block is injective. -/
theorem blockEmbedding_injective (j₁ j₂ : β → ι) (b : β) :
    Function.Injective (blockEmbedding (d := d) (ρ := ρ) (μ := μ) j₁ j₂ b) :=
  (Subtype.val_injective.sigma_map fun _ => Function.injective_id).sumMap sigma_mk_injective

end IsTypeA₂BlocksPresentation

variable [DecidableEq Γ]

/-- The diagram `D` is a ray presentation *of type `A₂` in blocks* `(j₁ b, j₂ b)`, `b : β`, of
the labels `g_j`, with degrees `n₁ b, n₂ b` and coefficients `c₁ b, c₂ b`: it is the ray
presentation of the `g_j` on the hyperplanes `{μ_j = 0}`, the indices `j₁ b, j₂ b` are pairwise
distinct, the labels of two walls commute unless both lie over the hyperplanes of one block, and
for every block `b` the degrees `n₁ b, n₂ b` are allowed with `μ_{j₁ b}(ρ n₁ b) = 0`,
`μ_{j₂ b}(ρ n₂ b) = 0`, `μ_{j₁ b}(ρ n₂ b) = -1` and `μ_{j₂ b}(ρ n₁ b) = 1`, and `g_{j₁ b}`,
`g_{j₂ b}` are the binomial labels of `1 + c₁ b z^{n₁ b}` and `1 + c₂ b z^{n₂ b}` with the normals
`μ_{j₁ b}`, `μ_{j₂ b}`. -/
structure IsTypeA₂BlocksPresentation {μ : ι → Λ →+ ℤ}
    (D : DirectedDiagram (d := d) h H (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}))
    (g : ι → d.completedBCHGroup ℒ) (j₁ j₂ : β → ι) (n₁ n₂ : β → Γ) (c₁ c₂ : β → R) : Prop where
  /-- The diagram is the ray presentation of the labels on the hyperplanes `{μ_j = 0}`. -/
  isRayFactorPresentation :
    D.IsRayFactorPresentation (fun j => {x | h.realCharacter (μ j) x = 0}) g
  /-- The indices `j₁ b, j₂ b` of all blocks are pairwise distinct. -/
  injective : Function.Injective (Sum.elim j₁ j₂)
  /-- The labels of two walls commute unless both lie over the hyperplanes of one block. -/
  commute (x y : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    (¬ ∃ b, (x.1 = j₁ b ∨ x.1 = j₂ b) ∧ (y.1 = j₁ b ∨ y.1 = j₂ b)) →
      Commute (D.wall x).label (D.wall y).label
  /-- The first degrees are allowed. -/
  mem_monoid_fst (b : β) : n₁ b ∈ d.monoid
  /-- The second degrees are allowed. -/
  mem_monoid_snd (b : β) : n₂ b ∈ d.monoid
  /-- The first degree of a block is tangent to its first hyperplane. -/
  apply_fst_fst (b : β) : μ (j₁ b) (ρ (n₁ b)) = 0
  /-- The second degree of a block is tangent to its second hyperplane. -/
  apply_snd_snd (b : β) : μ (j₂ b) (ρ (n₂ b)) = 0
  /-- The first normal of a block pairs to `-1` with its second degree. -/
  apply_fst_snd (b : β) : μ (j₁ b) (ρ (n₂ b)) = -1
  /-- The second normal of a block pairs to `1` with its first degree. -/
  apply_snd_fst (b : β) : μ (j₂ b) (ρ (n₁ b)) = 1
  /-- The first label of a block is the binomial label of `1 + c₁ b z^{n₁ b}`. -/
  label_fst (b : β) : g (j₁ b) = binomialLabel d ρ (μ (j₁ b)) (mem_monoid_fst b)
    (ne_zero_of_map (f := ρ) (ne_zero_of_map (f := μ (j₂ b)) (apply_snd_fst b ▸ one_ne_zero)))
    (apply_fst_fst b) (c₁ b)
  /-- The second label of a block is the binomial label of `1 + c₂ b z^{n₂ b}`. -/
  label_snd (b : β) : g (j₂ b) = binomialLabel d ρ (μ (j₂ b)) (mem_monoid_snd b)
    (ne_zero_of_map (f := ρ) (ne_zero_of_map (f := -μ (j₁ b)) (by simp [apply_fst_snd b])))
    (apply_snd_snd b) (c₂ b)

namespace IsTypeA₂BlocksPresentation

variable {μ : ι → Λ →+ ℤ} {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : β → ι}
  {n₁ n₂ : β → Γ} {c₁ c₂ : β → R} (hD : D.IsTypeA₂BlocksPresentation g j₁ j₂ n₁ n₂ c₁ c₂)
include hD

/-- The index `j₁ b` lies in the block `b`. -/
theorem blockOf_fst (b : β) : blockOf j₁ j₂ (j₁ b) = some b :=
  (blockOf_eq_some_iff hD.injective).mpr (Or.inl rfl)

/-- The index `j₂ b` lies in the block `b`. -/
theorem blockOf_snd (b : β) : blockOf j₁ j₂ (j₂ b) = some b :=
  (blockOf_eq_some_iff hD.injective).mpr (Or.inr rfl)

/-- Every wall of `D` is a full hyperplane, as required for outgoing completion. -/
theorem full (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    ∃ b : ℝ, (D.wall x).support = {y | h.realCharacter (D.wall x).normal y = b} :=
  ⟨0, by rw [hD.isRayFactorPresentation.support, hD.isRayFactorPresentation.normal]⟩

/-- The walls of `D` over the two hyperplanes of the block `b` form a ray presentation of type `A₂`
without isolated indices. -/
theorem isTypeA₂Presentation_restrictSigma (b : β) :
    (D.restrictSigma {j₁ b, j₂ b}).IsTypeA₂Presentation
      (μ := fun j : ({j₁ b, j₂ b} : Set ι) => μ j) (fun j => g j)
      ⟨j₁ b, mem_insert _ _⟩ ⟨j₂ b, mem_insert_of_mem _ rfl⟩ (n₁ b) (n₂ b) (c₁ b) (c₂ b) where
  isRayFactorPresentation :=
    { support := fun ⟨_, _⟩ => by rw [restrictSigma_wall, hD.isRayFactorPresentation.support]
      normal := fun ⟨_, _⟩ => by rw [restrictSigma_wall, hD.isRayFactorPresentation.normal]
      ray := fun ⟨_, _⟩ => by rw [restrictSigma_wall, hD.isRayFactorPresentation.ray]
      label := fun ⟨_, _⟩ => by rw [restrictSigma_wall, hD.isRayFactorPresentation.label] }
  commute_isolated := fun ⟨⟨_, hj⟩, _⟩ _ h₁ h₂ =>
    (hj.elim (fun he => h₁ (Subtype.ext he)) fun he => h₂ (Subtype.ext he)).elim
  mem_monoid_fst := hD.mem_monoid_fst b
  mem_monoid_snd := hD.mem_monoid_snd b
  apply_fst_fst := hD.apply_fst_fst b
  apply_snd_snd := hD.apply_snd_snd b
  apply_fst_snd := hD.apply_fst_snd b
  apply_snd_fst := hD.apply_snd_fst b
  label_fst := hD.label_fst b
  label_snd := hD.label_snd b

/-- The outgoing wall of the block `b`: the half-hyperplane
`{μ_{j₁ b} + μ_{j₂ b} = 0, μ_{j₁ b} ≥ 0}`, cooriented by `μ_{j₁ b} + μ_{j₂ b}`, on the ray through
`n₁ b + n₂ b`, labelled by the binomial label of `1 + c₁ b c₂ b z^{n₁ b + n₂ b}`. -/
def outgoingWall (b : β) : DirectedWall (d := d) h H :=
  (hD.isTypeA₂Presentation_restrictSigma b).outgoingWall

/-- The outgoing wall of the block `b` is cooriented by `μ_{j₁ b} + μ_{j₂ b}`. -/
@[simp]
theorem outgoingWall_normal (b : β) : (hD.outgoingWall b).normal = μ (j₁ b) + μ (j₂ b) := by
  rw [outgoingWall, IsTypeA₂Presentation.outgoingWall_normal]

/-- The outgoing wall of the block `b` is supported on `{μ_{j₁ b} + μ_{j₂ b} = 0, μ_{j₁ b} ≥ 0}`. -/
@[simp]
theorem outgoingWall_support (b : β) : (hD.outgoingWall b).support =
    {x | h.realCharacter (μ (j₁ b) + μ (j₂ b)) x = 0} ∩
      {x | 0 ≤ h.realCharacter (μ (j₁ b)) x} := by
  rw [outgoingWall, IsTypeA₂Presentation.outgoingWall_support]

/-- The outgoing wall of the block `b` is labelled by the binomial label of
`1 + c₁ b c₂ b z^{n₁ b + n₂ b}`. -/
@[simp]
theorem outgoingWall_label (b : β) : (hD.outgoingWall b).label =
    binomialLabel d ρ (μ (j₁ b) + μ (j₂ b))
      (hD.isTypeA₂Presentation_restrictSigma b).add_mem_monoid
      (hD.isTypeA₂Presentation_restrictSigma b).add_ne_zero
      (hD.isTypeA₂Presentation_restrictSigma b).apply_add_add (c₁ b * c₂ b) := by
  rw [outgoingWall, IsTypeA₂Presentation.outgoingWall_label]

variable [Finite β]

/-- The outgoing walls of the blocks, one for each block. -/
def outgoingDiagram : DirectedDiagram (d := d) h H (Σ _ : β, Unit) :=
  sigma fun b => ofFinite fun _ : Unit => hD.outgoingWall b

/-- The blocks diagram: the diagram `D` together with the outgoing walls of the blocks. -/
def blocksDiagram : DirectedDiagram (d := d) h H
    ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ (Σ _ : β, Unit)) :=
  D.append hD.outgoingDiagram

/-- The walls of the blocks diagram indexed by the walls of `D` are the walls of `D`. -/
@[simp]
theorem blocksDiagram_wall_inl (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    hD.blocksDiagram.wall (.inl x) = D.wall x := by
  rw [blocksDiagram, append_wall_inl]

/-- The remaining walls of the blocks diagram are the outgoing walls of the blocks. -/
@[simp]
theorem blocksDiagram_wall_inr (b : β) (u : Unit) :
    hD.blocksDiagram.wall (.inr ⟨b, u⟩) = hD.outgoingWall b := by
  rw [blocksDiagram, append_wall_inr, outgoingDiagram, sigma_wall, ofFinite_wall]

omit [Finite β] in
/-- The walls of the blocks diagram in the block `b` are the walls of the embedded pentagon
diagram of `b`. -/
theorem range_blockEmbedding (b : β) :
    range (blockEmbedding (d := d) (ρ := ρ) (μ := μ) j₁ j₂ b) =
      blockOfIndex j₁ j₂ ⁻¹' {some b} := by
  ext (⟨j, w⟩ | ⟨b', u⟩)
  · rw [mem_preimage, blockOfIndex_inl, mem_singleton_iff, blockOf_eq_some_iff hD.injective]
    constructor
    · rintro ⟨⟨⟨j', hj'⟩, w'⟩ | u, he⟩
      · simp only [blockEmbedding, Sum.map_inl, Sum.inl.injEq, Sigma.map, id_eq,
          Sigma.mk.inj_iff] at he
        exact he.1 ▸ hj'
      · simp [blockEmbedding] at he
    · exact fun hj => ⟨.inl ⟨⟨j, hj⟩, w⟩, by simp [blockEmbedding, Sigma.map]⟩
  · simp [blockEmbedding, eq_comm]

/-- The walls of the pentagon diagram of the block `b` are the walls of the blocks diagram at the
embedded indices. -/
theorem pentagonDiagram_wall_eq (b : β)
    (z : (Σ j : ({j₁ b, j₂ b} : Set ι), {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit) :
    (hD.isTypeA₂Presentation_restrictSigma b).pentagonDiagram.wall z =
      hD.blocksDiagram.wall (blockEmbedding j₁ j₂ b z) := by
  rcases z with ⟨j, w⟩ | u
  · simp [blockEmbedding, Sigma.map]
  · simp [blockEmbedding, outgoingWall]

omit [Finite β] in
/-- The labels of two walls of `D` commute when their hyperplanes lie in different blocks, or the
first one in no block. -/
theorem commute_wall_label {x y : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}}
    (hxy : blockOf j₁ j₂ x.1 ≠ blockOf j₁ j₂ y.1 ∨ blockOf j₁ j₂ x.1 = none) :
    Commute (D.wall x).label (D.wall y).label := by
  refine hD.commute x y fun ⟨b, hx, hy⟩ => ?_
  have hx' := (blockOf_eq_some_iff hD.injective).mpr hx
  rcases hxy with hne | hnone
  · exact hne (hx'.trans ((blockOf_eq_some_iff hD.injective).mpr hy).symm)
  · exact Option.some_ne_none b (hx'.symm.trans hnone)

/-- The walls of the blocks diagram at the isolated indices are full hyperplanes. -/
theorem full_restrict_blockOfIndex_none
    (z : (blockOfIndex (d := d) (ρ := ρ) (μ := μ) j₁ j₂ ⁻¹' {none})) :
    ∃ b : ℝ, ((hD.blocksDiagram.restrict _).wall z).support =
      {y | h.realCharacter ((hD.blocksDiagram.restrict _).wall z).normal y = b} := by
  obtain ⟨x | ⟨b, u⟩, hz⟩ := z
  · rw [restrict_wall, blocksDiagram_wall_inl]
    exact hD.full x
  · simp at hz

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)] {M : Type*} [AddCommGroup M] (π : Γ →+ M)
  {S : Type*} [Semiring S] (φ : S →+* R)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- **Positivity of the blocks diagram from a positive grouping of `D`.** Let `G` be a grouping of
the walls of `D` into function walls for the projection `π`, positive for the image of `S[Q]`. If
every product `c₁ b c₂ b` lies in the image of a semiring map `φ : S →+* R`, and for every block
`b` the coefficient monoid `Q` contains an exponent `p` with `-p ∈ Q` and
`(μ_{j₁ b} + μ_{j₂ b})(ρ p) = 1`, the blocks diagram is a positive wall representative for the
image of `S[Q]`: the groups of `G` and the outgoing walls, with the wall functions
`1 + c₁ b c₂ b z^{n₁ b + n₂ b}`, form a positive grouping. -/
theorem isPositiveWallRepresentative_blocksDiagram_of_isPositive
    (hc : ∀ b, c₁ b * c₂ b ∈ φ.rangeS)
    (hQ : ∀ b, ∃ p ∈ Q, -p ∈ Q ∧ (μ (j₁ b) + μ (j₂ b)) (ρ p) = 1) {κ' : Type*}
    {G : D.FunctionWallGrouping π κ'}
    (hG : G.IsPositive ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS) :
    hD.blocksDiagram.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS π :=
  (hG.append (FunctionWallGrouping.IsPositive.sigma fun b =>
    (hD.isTypeA₂Presentation_restrictSigma b).isPositive_discrete_outgoingWall Q π φ (hc b)
      (hQ b))).isPositiveWallRepresentative

end Positive

end IsTypeA₂BlocksPresentation

end Mei.DirectedDiagram

/-! ### Consistency, needing the lattices in `Type`

The pentagon identity `Mei.binomialLabel_pentagon` is transported through `ℤ × ℤ`, so the
theorems below take `Γ Λ : Type`. The blocks are indexed by `β : Type`, so that the blocks diagram
is indexed in the universe of the walls of `D`, as its scattering class is. -/

namespace Mei.DirectedDiagram.IsTypeA₂BlocksPresentation

open _root_.AddMonoidAlgebra Set

variable {R : Type*} {Γ Λ : Type} {V ι : Type*} {β : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {latticeMap : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice latticeMap} {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : β → ι}
  {n₁ n₂ : β → Γ} {c₁ c₂ : β → R} (hD : D.IsTypeA₂BlocksPresentation g j₁ j₂ n₁ n₂ c₁ c₂)
include hD

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The label of a wall of `D` outside the block `b` commutes with the label of the outgoing wall
of `b`. -/
theorem commute_wall_label_outgoingWall_label
    {x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}} {b : β}
    (hx : blockOf j₁ j₂ x.1 ≠ some b) : Commute (D.wall x).label (hD.outgoingWall b).label := by
  -- The outgoing label is a product of the two binomial labels of `b` and their inverses.
  have hb := hD.isTypeA₂Presentation_restrictSigma b
  refine hb.commute_outgoingWall_label ?_ ?_
  · rw [hb.fstIndex_def, restrictSigma_wall]
    exact hD.commute_wall_label (Or.inl fun he => hx (he.trans (hD.blockOf_fst b)))
  · rw [hb.sndIndex_def, restrictSigma_wall]
    exact hD.commute_wall_label (Or.inl fun he => hx (he.trans (hD.blockOf_snd b)))

/-- The labels of the outgoing walls of distinct blocks commute. -/
theorem commute_outgoingWall_label {b b' : β} (hne : b ≠ b') :
    Commute (hD.outgoingWall b).label (hD.outgoingWall b').label := by
  have hb' := hD.isTypeA₂Presentation_restrictSigma b'
  refine hb'.commute_outgoingWall_label ?_ ?_
  · rw [hb'.fstIndex_def, restrictSigma_wall]
    exact (hD.commute_wall_label_outgoingWall_label
      (fun he => hne (Option.some_injective _ ((hD.blockOf_fst b').symm.trans he)).symm)).symm
  · rw [hb'.sndIndex_def, restrictSigma_wall]
    exact (hD.commute_wall_label_outgoingWall_label
      (fun he => hne (Option.some_injective _ ((hD.blockOf_snd b').symm.trans he)).symm)).symm

variable [Finite β]

/-- The labels of two walls of the blocks diagram commute when they lie in different blocks, or
the first one in no block. -/
theorem commute_blocksDiagram_label
    {a c : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ (Σ _ : β, Unit)}
    (hac : blockOfIndex j₁ j₂ a ≠ blockOfIndex j₁ j₂ c ∨ blockOfIndex j₁ j₂ a = none) :
    Commute (hD.blocksDiagram.wall a).label (hD.blocksDiagram.wall c).label := by
  rcases a with x | ⟨b, u⟩ <;> rcases c with y | ⟨b', u'⟩
  · rw [blockOfIndex_inl, blockOfIndex_inl] at hac
    rw [blocksDiagram_wall_inl, blocksDiagram_wall_inl]
    exact hD.commute_wall_label hac
  · rw [blockOfIndex_inl, blockOfIndex_inr] at hac
    rw [blocksDiagram_wall_inl, blocksDiagram_wall_inr]
    exact hD.commute_wall_label_outgoingWall_label fun he =>
      hac.elim (· he) fun hn => Option.some_ne_none b' (he.symm.trans hn)
  · rw [blockOfIndex_inr, blockOfIndex_inl] at hac
    rw [blocksDiagram_wall_inr, blocksDiagram_wall_inl]
    exact (hD.commute_wall_label_outgoingWall_label fun he =>
      hac.resolve_right (Option.some_ne_none b) he.symm).symm
  · rw [blockOfIndex_inr, blockOfIndex_inr] at hac
    rw [blocksDiagram_wall_inr, blocksDiagram_wall_inr]
    exact hD.commute_outgoingWall_label fun he =>
      hac.resolve_right (Option.some_ne_none b) (congrArg some he)

/-- The walls of the blocks diagram at the isolated indices form a consistent diagram: they are full
hyperplanes with commuting labels. -/
theorem restrict_blockOfIndex_none_consistent :
    (hD.blocksDiagram.restrict (blockOfIndex j₁ j₂ ⁻¹' {none})).Consistent :=
  consistent_of_commute_of_full _ hD.full_restrict_blockOfIndex_none fun z z' => by
    rw [restrict_wall, restrict_wall]
    exact hD.commute_blocksDiagram_label (Or.inr z.property)

/-- The walls of the blocks diagram in the block `b` form a consistent diagram, the pentagon diagram
of `b`. -/
theorem restrict_blockOfIndex_some_consistent [HasUniqueDiv Γ] (b : β) :
    (hD.blocksDiagram.restrict (blockOfIndex j₁ j₂ ⁻¹' {some b})).Consistent := by
  rw [← hD.range_blockEmbedding b]
  exact (hD.blocksDiagram.restrict_range_equivalent (blockEmbedding_injective j₁ j₂ b)
    (hD.pentagonDiagram_wall_eq b)).consistent_iff.mpr
    (hD.isTypeA₂Presentation_restrictSigma b).pentagonDiagram_consistent

/-- The blocks diagram is consistent. -/
theorem blocksDiagram_consistent [HasUniqueDiv Γ] : hD.blocksDiagram.Consistent :=
  consistent_of_restrict_preimage (blockOfIndex j₁ j₂)
    (fun
      | none => hD.restrict_blockOfIndex_none_consistent
      | some b => hD.restrict_blockOfIndex_some_consistent b)
    fun _ _ hac => hD.commute_blocksDiagram_label (Or.inl hac)

/-- The blocks diagram is an outgoing completion of `D`: its walls indexed by the walls of `D` are
the walls of `D`, its remaining walls are outgoing, and it is consistent. -/
theorem isOutgoingCompletion_blocksDiagram [HasUniqueDiv Γ] :
    IsOutgoingCompletion D.wall hD.blocksDiagram where
  wall_inl := hD.blocksDiagram_wall_inl
  outgoing_inr := fun ⟨b, u⟩ => by
    rw [blocksDiagram_wall_inr]
    exact (hD.isTypeA₂Presentation_restrictSigma b).outgoingWall_outgoing
  consistent := hD.blocksDiagram_consistent

/-- **Scattering diagrams of commuting blocks of type `A₂`.** For a ray presentation of type `A₂`
in finitely many blocks with arbitrary coefficients, the outgoing scattering class of `D` is the
class of the blocks diagram, with one additional outgoing wall
`{μ_{j₁ b} + μ_{j₂ b} = 0, μ_{j₁ b} ≥ 0}` labelled by the binomial label of
`1 + c₁ b c₂ b z^{n₁ b + n₂ b}` for every block `b`. -/
theorem scat_eq_toClass_blocksDiagram [Module.Free ℤ Γ] :
    D.Scat hD.full = hD.blocksDiagram.toClass :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  scat_eq_toClass _ _ hD.isOutgoingCompletion_blocksDiagram

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)] {M : Type*} [AddCommGroup M] (π : Γ →+ M)
  [Module.Free ℤ Γ] {S : Type*} [Semiring S] (φ : S →+* R)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- **Positivity of commuting blocks of type `A₂` with a positive grouping of `D`.** Under the
hypotheses of `isPositiveWallRepresentative_blocksDiagram_of_isPositive`, the outgoing scattering
class of `D` has a consistent outgoing representative, the blocks diagram, which is a positive
wall representative for the image of `S[Q]`. -/
theorem exists_isPositiveWallRepresentative_scat_of_isPositive
    (hc : ∀ b, c₁ b * c₂ b ∈ φ.rangeS)
    (hQ : ∀ b, ∃ p ∈ Q, -p ∈ Q ∧ (μ (j₁ b) + μ (j₂ b)) (ρ p) = 1) {κ' : Type*}
    {G : D.FunctionWallGrouping π κ'}
    (hG : G.IsPositive ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS) :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H
        ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ κ)),
      IsOutgoingCompletion D.wall E ∧ E.toClass = D.Scat hD.full ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS π :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  ⟨Σ _ : β, Unit, hD.blocksDiagram, hD.isOutgoingCompletion_blocksDiagram,
    hD.scat_eq_toClass_blocksDiagram.symm,
    hD.isPositiveWallRepresentative_blocksDiagram_of_isPositive Q π φ hc hQ hG⟩

end Positive

end Mei.DirectedDiagram.IsTypeA₂BlocksPresentation
