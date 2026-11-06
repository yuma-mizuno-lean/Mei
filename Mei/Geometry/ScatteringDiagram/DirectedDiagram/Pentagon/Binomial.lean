/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Binomial
public import Mei.Algebra.Lie.Logarithmic.Pentagon

/-!
# Ray presentations of two binomial labels of type `A₂`

Let `D` be the ray presentation (`DirectedDiagram.IsRayFactorPresentation`), in the tropical
vertex wall spaces of `(Γ, Λ, ρ)`, of labels `g_j` on the hyperplanes `{μ_j = 0}` through the
origin, indexed by exactly two indices `j₁, j₂`. It is *of type `A₂`* with degrees `n₁, n₂` and
coefficients `c₁, c₂` (`DirectedDiagram.IsTypeA₂Presentation`) when `g_{j₁}` and `g_{j₂}` are the
binomial labels `θ[μ_{j₁}, n₁, c₁]` and `θ[μ_{j₂}, n₂, c₂]` of `1 + c₁ z^{n₁}` and `1 + c₂ z^{n₂}`
and the normals pair with the degrees by `μ_{j₁}(ρ n₂) = -1` and `μ_{j₂}(ρ n₁) = 1`. Write
`μ₁ = μ_{j₁}` and `μ₂ = μ_{j₂}`.

* Adding to `D` the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}`, cooriented by `μ₁ + μ₂` and
  labelled by the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}` (`IsTypeA₂Presentation.outgoingWall`),
  gives a consistent diagram, the *pentagon diagram*
  (`IsTypeA₂Presentation.pentagonDiagram_consistent`). Its new wall is outgoing, so it is an
  outgoing completion of `D` (`IsTypeA₂Presentation.isOutgoingCompletion_pentagonDiagram`) and
  represents its scattering class (`IsTypeA₂Presentation.scat_eq_toClass_pentagonDiagram`).
* If the coefficient monoid `Q` contains exponents `p₁, p₂` with `-p₁, -p₂ ∈ Q`,
  `μ₁(ρ p₁) = 1`, `μ₂(ρ p₁) = 0` and `μ₂(ρ p₂) = 1`, the discrete grouping of the pentagon diagram
  has the wall functions `1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}` and `1 + c₁ c₂ z^{n₁ + n₂}` on its three
  nontrivial walls and `1` on all other walls. If `c₁, c₂` lie in the image of a semiring map
  `φ : S →+* R`, the pentagon diagram is a positive wall representative of the scattering class
  for the image of `S[Q]` (`IsTypeA₂Presentation.exists_isPositiveWallRepresentative_scat`).

The walls of `D` on the rays through `n₁` and `n₂` carry the two binomial labels, all its other
walls have trivial labels (`IsTypeA₂Presentation.label_eq_one`), and the three nontrivial walls of
the pentagon diagram are in pentagon configuration
(`IsTypeA₂Presentation.isPentagonConfiguration`); their labels satisfy the pentagon identity
`Mei.binomialLabel_pentagon` of the tropical vertex group.

The incoming diagrams of rank-two polynomial inputs of type `A₂`
(`Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Pentagon.Basic`) and of BLM polynomial
inputs of type `A₂` (`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon`) are such
presentations. The consistent diagram is the scattering diagram of type `A₂` of
Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*, Example 1.6
(arXiv:0902.0779v3), and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Example 1.15 (arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

open _root_.AddMonoidAlgebra

variable {R Γ Λ V ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [AddCommGroup Λ]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {latticeMap : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice latticeMap}

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The diagram `D` is a ray presentation *of type `A₂`* of the labels `g_j` at the indices `j₁, j₂`
with degrees `n₁, n₂` and coefficients `c₁, c₂`: it is the ray presentation of the `g_j` on the
hyperplanes `{μ_j = 0}`, every index is `j₁` or `j₂`, the degrees `n₁, n₂` are allowed with
`μ_{j₁}(ρ n₁) = μ_{j₂}(ρ n₂) = 0`, `μ_{j₁}(ρ n₂) = -1` and `μ_{j₂}(ρ n₁) = 1`, and `g_{j₁}`,
`g_{j₂}` are the binomial labels of `1 + c₁ z^{n₁}` and `1 + c₂ z^{n₂}` with the normals `μ_{j₁}`,
`μ_{j₂}`. -/
structure IsTypeA₂Presentation {μ : ι → Λ →+ ℤ}
    (D : DirectedDiagram (d := d) h H (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}))
    (g : ι → d.completedBCHGroup ℒ) (j₁ j₂ : ι) (n₁ n₂ : Γ) (c₁ c₂ : R) : Prop where
  /-- The diagram is the ray presentation of the labels on the hyperplanes `{μ_j = 0}`. -/
  isRayFactorPresentation :
    D.IsRayFactorPresentation (fun j => {x | h.realCharacter (μ j) x = 0}) g
  /-- Every index is one of the two. -/
  eq_or_eq (j : ι) : j = j₁ ∨ j = j₂
  /-- The first degree is allowed. -/
  mem_monoid_fst : n₁ ∈ d.monoid
  /-- The second degree is allowed. -/
  mem_monoid_snd : n₂ ∈ d.monoid
  /-- The first degree is tangent to the first hyperplane. -/
  apply_fst_fst : μ j₁ (ρ n₁) = 0
  /-- The second degree is tangent to the second hyperplane. -/
  apply_snd_snd : μ j₂ (ρ n₂) = 0
  /-- The first normal pairs to `-1` with the second degree. -/
  apply_fst_snd : μ j₁ (ρ n₂) = -1
  /-- The second normal pairs to `1` with the first degree. -/
  apply_snd_fst : μ j₂ (ρ n₁) = 1
  /-- The first label is the binomial label of `1 + c₁ z^{n₁}`. -/
  label_fst : g j₁ = binomialLabel d ρ (μ j₁) mem_monoid_fst
    (ne_zero_of_map (f := ρ) (ne_zero_of_map (f := μ j₂) (apply_snd_fst ▸ one_ne_zero)))
    apply_fst_fst c₁
  /-- The second label is the binomial label of `1 + c₂ z^{n₂}`. -/
  label_snd : g j₂ = binomialLabel d ρ (μ j₂) mem_monoid_snd
    (ne_zero_of_map (f := ρ) (ne_zero_of_map (f := -μ j₁) (by simp [apply_fst_snd])))
    apply_snd_snd c₂

namespace IsTypeA₂Presentation

-- The binder types spell out the wall spaces and the grading: the local notations `H` and `ℒ` do
-- not elaborate inside `variable` binders here.
variable {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : ι} {n₁ n₂ : Γ}
  {c₁ c₂ : R} (hD : D.IsTypeA₂Presentation g j₁ j₂ n₁ n₂ c₁ c₂)
include hD

/-- The first degree is nonzero. -/
theorem ne_zero_fst : n₁ ≠ 0 :=
  ne_zero_of_map (f := ρ) (ne_zero_of_map (f := μ j₂) (hD.apply_snd_fst ▸ one_ne_zero))

/-- The second degree is nonzero. -/
theorem ne_zero_snd : n₂ ≠ 0 :=
  ne_zero_of_map (f := ρ) (ne_zero_of_map (f := -μ j₁) (by simp [hD.apply_fst_snd]))

/-- The two indices are distinct. -/
theorem fst_ne_snd : j₁ ≠ j₂ := by
  intro he
  have h₁ := hD.apply_snd_fst
  rw [← he, hD.apply_fst_fst] at h₁
  exact zero_ne_one h₁

/-- The sum `n₁ + n₂` is tangent to the sum `μ₁ + μ₂` of the normals. -/
theorem apply_add_add : (μ j₁ + μ j₂) (ρ (n₁ + n₂)) = 0 := by
  simp [hD.apply_fst_fst, hD.apply_fst_snd, hD.apply_snd_fst, hD.apply_snd_snd]

/-- The first normal pairs to `-1` with `n₁ + n₂`. -/
theorem apply_fst_add : μ j₁ (ρ (n₁ + n₂)) = -1 := by
  rw [map_add, map_add, hD.apply_fst_fst, hD.apply_fst_snd, zero_add]

/-- The second normal pairs to `1` with `n₁ + n₂`. -/
theorem apply_snd_add : μ j₂ (ρ (n₁ + n₂)) = 1 := by
  rw [map_add, map_add, hD.apply_snd_fst, hD.apply_snd_snd, add_zero]

/-- The sum `n₁ + n₂` is an allowed degree. -/
theorem add_mem_monoid : n₁ + n₂ ∈ d.monoid := add_mem hD.mem_monoid_fst hD.mem_monoid_snd

/-- The sum `n₁ + n₂` is nonzero. -/
theorem add_ne_zero : n₁ + n₂ ≠ 0 :=
  d.add_ne_zero hD.mem_monoid_fst hD.mem_monoid_snd hD.ne_zero_fst

/-- The supported ray through `n₁`: the degree `n₁` is primitive, since `μ₂(ρ n₁) = 1`. -/
def fstRay : SupportedRay d :=
  SupportedRay.ofMem n₁ hD.mem_monoid_fst
    (TauCeti.isPrimitive_def.mpr ⟨((μ j₂).comp ρ).toIntLinearMap, hD.apply_snd_fst⟩)

/-- The supported ray through `n₂`: the degree `n₂` is primitive, since `-μ₁(ρ n₂) = 1`. -/
def sndRay : SupportedRay d :=
  SupportedRay.ofMem n₂ hD.mem_monoid_snd
    (TauCeti.isPrimitive_def.mpr ⟨((-μ j₁).comp ρ).toIntLinearMap, by
      simp [hD.apply_fst_snd]⟩)

/-- The supported ray through `n₁ + n₂`: the degree `n₁ + n₂` is primitive, since
`μ₂(ρ (n₁ + n₂)) = 1`. -/
def addRay : SupportedRay d :=
  SupportedRay.ofMem (n₁ + n₂) hD.add_mem_monoid
    (TauCeti.isPrimitive_def.mpr ⟨((μ j₂).comp ρ).toIntLinearMap, hD.apply_snd_add⟩)

/-- The generator of the first ray is `n₁`. -/
@[simp]
theorem fstRay_generator : hD.fstRay.generator = n₁ := SupportedRay.generator_ofMem ..

/-- The generator of the second ray is `n₂`. -/
@[simp]
theorem sndRay_generator : hD.sndRay.generator = n₂ := SupportedRay.generator_ofMem ..

/-- The generator of the ray through `n₁ + n₂` is `n₁ + n₂`. -/
@[simp]
theorem addRay_generator : hD.addRay.generator = n₁ + n₂ := SupportedRay.generator_ofMem ..

/-- The degree `n₁` lies on the first ray. -/
theorem mem_fstRay_rayDegrees : n₁ ∈ hD.fstRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₂` lies on the second ray. -/
theorem mem_sndRay_rayDegrees : n₂ ∈ hD.sndRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₁ + n₂` lies on the ray through it. -/
theorem mem_addRay_rayDegrees : n₁ + n₂ ∈ hD.addRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The wall of `D` over the first hyperplane on the ray through `n₁`. -/
def fstIndex : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0} :=
  ⟨j₁, hD.fstRay, by rw [fstRay_generator]; exact hD.apply_fst_fst⟩

/-- The wall of `D` over the second hyperplane on the ray through `n₂`. -/
def sndIndex : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0} :=
  ⟨j₂, hD.sndRay, by rw [sndRay_generator]; exact hD.apply_snd_snd⟩

/-- The first index is the wall over the first hyperplane on the ray through `n₁`. -/
theorem fstIndex_def :
    hD.fstIndex = ⟨j₁, hD.fstRay, by rw [fstRay_generator]; exact hD.apply_fst_fst⟩ := (rfl)

/-- The second index is the wall over the second hyperplane on the ray through `n₂`. -/
theorem sndIndex_def :
    hD.sndIndex = ⟨j₂, hD.sndRay, by rw [sndRay_generator]; exact hD.apply_snd_snd⟩ := (rfl)

/-- The wall of `D` over the first hyperplane on the ray through `n₁` is labelled by the binomial
label of `1 + c₁ z^{n₁}`. -/
theorem label_fstIndex : (D.wall hD.fstIndex).label =
    binomialLabel d ρ (μ j₁) hD.mem_monoid_fst hD.ne_zero_fst hD.apply_fst_fst c₁ := by
  rw [hD.isRayFactorPresentation.label, fstIndex_def, hD.label_fst]
  exact rayFactor_binomialLabel_self d ρ _ _ _ _ _ hD.mem_fstRay_rayDegrees

/-- The wall of `D` over the second hyperplane on the ray through `n₂` is labelled by the binomial
label of `1 + c₂ z^{n₂}`. -/
theorem label_sndIndex : (D.wall hD.sndIndex).label =
    binomialLabel d ρ (μ j₂) hD.mem_monoid_snd hD.ne_zero_snd hD.apply_snd_snd c₂ := by
  rw [hD.isRayFactorPresentation.label, sndIndex_def, hD.label_snd]
  exact rayFactor_binomialLabel_self d ρ _ _ _ _ _ hD.mem_sndRay_rayDegrees

/-- The walls of `D` other than those on the rays through `n₁` and `n₂` have trivial labels. -/
theorem label_eq_one [HasUniqueDiv Γ] {x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}}
    (h₁ : x ≠ hD.fstIndex) (h₂ : x ≠ hD.sndIndex) : (D.wall x).label = 1 := by
  obtain ⟨j, w, hw⟩ := x
  rw [hD.isRayFactorPresentation.label]
  rcases hD.eq_or_eq j with rfl | rfl
  · refine hD.label_fst.symm ▸
      rayFactor_binomialLabel_of_ne d ρ _ _ _ _ _ hD.mem_fstRay_rayDegrees fun he => h₁ ?_
    subst he
    exact hD.fstIndex_def.symm
  · refine hD.label_snd.symm ▸
      rayFactor_binomialLabel_of_ne d ρ _ _ _ _ _ hD.mem_sndRay_rayDegrees fun he => h₂ ?_
    subst he
    exact hD.sndIndex_def.symm

/-- Every wall of `D` is a full hyperplane, as required for outgoing completion. -/
theorem full (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    ∃ b : ℝ, (D.wall x).support = {y | h.realCharacter (D.wall x).normal y = b} :=
  ⟨0, by rw [hD.isRayFactorPresentation.support, hD.isRayFactorPresentation.normal]⟩

/-- The binomial label of `1 + c₁ c₂ z^{n₁ + n₂}` with the normal `μ₁ + μ₂`, as a wall label of
the ray through `n₁ + n₂`. -/
def outgoingLabel : (H).wallGroup hD.addRay (μ j₁ + μ j₂) :=
  ⟨binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add (c₁ * c₂),
    binomialLabel_mem_wallGroup d ρ _ _ _ _ _ hD.mem_addRay_rayDegrees⟩

/-- The outgoing label is the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem coe_outgoingLabel : (hD.outgoingLabel : d.completedBCHGroup ℒ) =
    binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add (c₁ * c₂) :=
  (rfl)

/-- The normals `μ₁, μ₂` take the values `1` and `-1` at the image of `-(n₁ + n₂)`. -/
theorem realCharacter_neg_add :
    h.realCharacter (μ j₁) (latticeMap (ρ (-(n₁ + n₂)))) = 1 ∧
      h.realCharacter (μ j₂) (latticeMap (ρ (-(n₁ + n₂)))) = -1 := by
  simp [hD.apply_fst_fst, hD.apply_fst_snd, hD.apply_snd_fst, hD.apply_snd_snd]

/-- The outgoing wall of the pentagon diagram: the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}`,
cooriented by `μ₁ + μ₂`, on the ray through `n₁ + n₂`, labelled by the binomial label of
`1 + c₁ c₂ z^{n₁ + n₂}`. -/
def outgoingWall : DirectedWall (d := d) h H :=
  (DirectedWall.ofAffineHyperplane h H (μ j₁ + μ j₂)
    (fun he => by
      have h₁ := congrArg (fun ν : Λ →+ ℤ => ν (ρ (-n₂))) he
      simp [hD.apply_fst_snd, hD.apply_snd_snd] at h₁)
    0 hD.addRay (by rw [addRay_generator]; exact hD.apply_add_add) hD.outgoingLabel)
    |>.cutHalfspace (μ j₁) 0 ⟨latticeMap (ρ (-(n₁ + n₂))), by
      simp only [DirectedWall.ofAffineHyperplane_support, Set.mem_ofPred_eq, map_add,
        LinearMap.add_apply, hD.realCharacter_neg_add.1, hD.realCharacter_neg_add.2,
        add_neg_cancel], by
      rw [hD.realCharacter_neg_add.1]
      exact one_pos⟩

/-- The outgoing wall is cooriented by `μ₁ + μ₂`. -/
@[simp]
theorem outgoingWall_normal : hD.outgoingWall.normal = μ j₁ + μ j₂ := by
  rw [outgoingWall, DirectedWall.cutHalfspace_normal, DirectedWall.ofAffineHyperplane_normal]

/-- The outgoing wall lies on the ray through `n₁ + n₂`. -/
@[simp]
theorem outgoingWall_ray : hD.outgoingWall.ray = hD.addRay := by
  rw [outgoingWall, DirectedWall.cutHalfspace_ray, DirectedWall.ofAffineHyperplane_ray]

/-- The outgoing wall is supported on the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}`. -/
@[simp]
theorem outgoingWall_support : hD.outgoingWall.support =
    {x | h.realCharacter (μ j₁ + μ j₂) x = 0} ∩ {x | 0 ≤ h.realCharacter (μ j₁) x} := by
  rw [outgoingWall, DirectedWall.cutHalfspace_support, DirectedWall.ofAffineHyperplane_support]

/-- The outgoing wall is labelled by the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem outgoingWall_label : hD.outgoingWall.label =
    binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add
      (c₁ * c₂) := by
  rw [outgoingWall, DirectedWall.cutHalfspace_label, DirectedWall.ofAffineHyperplane_label,
    coe_outgoingLabel]

/-- The outgoing wall is outgoing: the direction of its ray is not a recession direction of its
support. -/
theorem outgoingWall_outgoing : hD.outgoingWall.Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [outgoingWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  simp only [DirectedWall.ofAffineHyperplane_ray, addRay_generator, hD.apply_fst_add] at hinc
  exact absurd hinc (by decide)

/-- The pentagon diagram: the diagram `D` together with the outgoing wall. -/
def pentagonDiagram :
    DirectedDiagram (d := d) h H ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit) :=
  D.append (ofFinite fun _ : Unit => hD.outgoingWall)

/-- The walls of the pentagon diagram indexed by the walls of `D` are the walls of `D`. -/
@[simp]
theorem pentagonDiagram_wall_inl (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    hD.pentagonDiagram.wall (.inl x) = D.wall x := by
  rw [pentagonDiagram, append_wall_inl]

/-- The remaining wall of the pentagon diagram is the outgoing wall. -/
@[simp]
theorem pentagonDiagram_wall_inr (u : Unit) :
    hD.pentagonDiagram.wall (.inr u) = hD.outgoingWall := by
  rw [pentagonDiagram, append_wall_inr, ofFinite_wall]

/-- The three walls of the pentagon diagram with nontrivial labels: the walls of `D` on the rays
through `n₁` and `n₂` and the outgoing wall. -/
def pentagonIndices : Set ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit) :=
  {.inl hD.fstIndex, .inl hD.sndIndex, .inr ()}

/-- Membership in the three nontrivial walls. -/
theorem mem_pentagonIndices {x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit} :
    x ∈ hD.pentagonIndices ↔ x = .inl hD.fstIndex ∨ x = .inl hD.sndIndex ∨ x = .inr () :=
  Iff.rfl

/-- The walls of the pentagon diagram outside the three nontrivial ones have trivial labels. -/
theorem pentagonDiagram_label_eq_one [HasUniqueDiv Γ]
    {x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit}
    (hx : x ∉ hD.pentagonIndices) : (hD.pentagonDiagram.wall x).label = 1 := by
  rw [mem_pentagonIndices, not_or, not_or] at hx
  rcases x with x | u
  · rw [pentagonDiagram_wall_inl]
    exact hD.label_eq_one (fun he => hx.1 (he ▸ rfl)) fun he => hx.2.1 (he ▸ rfl)
  · exact absurd rfl hx.2.2

/-- The three nontrivial walls of the pentagon diagram are in pentagon configuration: the
hyperplanes `{μ₁ = 0}`, `{μ₂ = 0}` and the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}` cooriented by
`μ₁ + μ₂`. -/
theorem isPentagonConfiguration :
    (hD.pentagonDiagram.restrict hD.pentagonIndices).IsPentagonConfiguration
      ⟨.inl hD.fstIndex, hD.mem_pentagonIndices.mpr (Or.inl rfl)⟩
      ⟨.inl hD.sndIndex, hD.mem_pentagonIndices.mpr (Or.inr (Or.inl rfl))⟩
      ⟨.inr (), hD.mem_pentagonIndices.mpr (Or.inr (Or.inr rfl))⟩ (μ j₁) (μ j₂) where
  eq_or_eq_or_eq := by
    rintro ⟨x, hx⟩
    rcases hD.mem_pentagonIndices.mp hx with rfl | rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  normal_fst := by simp [hD.isRayFactorPresentation.normal, fstIndex_def]
  normal_snd := by simp [hD.isRayFactorPresentation.normal, sndIndex_def]
  normal_half := by simp
  support_fst := by simp [hD.isRayFactorPresentation.support, fstIndex_def]
  support_snd := by simp [hD.isRayFactorPresentation.support, sndIndex_def]
  support_half := by
    ext x
    simp
  exists_fst := ⟨latticeMap (ρ n₁), by simp [hD.apply_fst_fst], by simp [hD.apply_snd_fst]⟩
  exists_snd := ⟨latticeMap (ρ n₂), by simp [hD.apply_snd_snd], by simp [hD.apply_fst_snd]⟩

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

omit [Fact (d.monoid ≤ Q)] in
/-- If `Q` contains exponents `p₁, p₂` whose monomials are invertible, with `μ₁(ρ p₁) = 1`,
`μ₂(ρ p₁) = 0` and `μ₂(ρ p₂) = 1`, the normal of every wall of the pentagon diagram takes the
value one at one of them: `p₁` for the walls cooriented by `μ₁` or `μ₁ + μ₂`, and `p₂` for those
cooriented by `μ₂`. -/
theorem exists_normal_eq_one_isUnit
    (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
    (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1)
    (x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit) :
    ∃ p : Q, (hD.pentagonDiagram.wall x).normal (ρ p) = 1 ∧
      IsUnit ((F).toCompletion (single p (1 : R))) := by
  obtain ⟨p₁, hp₁, hp₁', h₁₁, h₂₁⟩ := hQ₁
  obtain ⟨p₂, hp₂, hp₂', h₂₂⟩ := hQ₂
  rcases x with ⟨j, w⟩ | u
  · rw [pentagonDiagram_wall_inl, hD.isRayFactorPresentation.normal]
    rcases hD.eq_or_eq j with rfl | rfl
    · exact ⟨⟨p₁, hp₁⟩, h₁₁, TropicalVertexCoefficientAction.isUnit_toCompletion_single hp₁ hp₁'⟩
    · exact ⟨⟨p₂, hp₂⟩, h₂₂, TropicalVertexCoefficientAction.isUnit_toCompletion_single hp₂ hp₂'⟩
  · rw [pentagonDiagram_wall_inr, outgoingWall_normal]
    exact ⟨⟨p₁, hp₁⟩, by simp [h₁₁, h₂₁],
      TropicalVertexCoefficientAction.isUnit_toCompletion_single hp₁ hp₁'⟩

omit [Fact (d.monoid ≤ Q)] in
/-- Under the hypotheses of `exists_normal_eq_one_isUnit`, the coorientations of the walls of the
pentagon diagram are primitive. -/
theorem isPrimitive_pentagonDiagram_normal
    (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
    (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1)
    (x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit) :
    TauCeti.IsPrimitive (hD.pentagonDiagram.wall x).normal := by
  obtain ⟨p, hp, -⟩ := hD.exists_normal_eq_one_isUnit (R := R) Q hQ₁ hQ₂ x
  exact TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (ρ p)), hp⟩

/-- Each of the three nontrivial walls of the pentagon diagram is cooriented by a character `ν`
and labelled by the binomial label of `ν`, a degree `n` and a coefficient `b` among `c₁`, `c₂` and
`c₁ c₂`. -/
theorem exists_label_eq_binomialLabel
    {x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Unit}
    (hx : x ∈ hD.pentagonIndices) :
    ∃ (ν : Λ →+ ℤ) (n : Γ) (hn : n ∈ d.monoid) (hn0 : n ≠ 0) (hν : ν (ρ n) = 0) (b : R),
      (b = c₁ ∨ b = c₂ ∨ b = c₁ * c₂) ∧ (hD.pentagonDiagram.wall x).normal = ν ∧
      (hD.pentagonDiagram.wall x).label = binomialLabel d ρ ν hn hn0 hν b := by
  rcases hD.mem_pentagonIndices.mp hx with rfl | rfl | rfl
  · refine ⟨μ j₁, n₁, hD.mem_monoid_fst, hD.ne_zero_fst, hD.apply_fst_fst, _, Or.inl rfl, ?_,
      by rw [pentagonDiagram_wall_inl, hD.label_fstIndex]⟩
    rw [pentagonDiagram_wall_inl, hD.isRayFactorPresentation.normal, fstIndex_def]
  · refine ⟨μ j₂, n₂, hD.mem_monoid_snd, hD.ne_zero_snd, hD.apply_snd_snd, _,
      Or.inr (Or.inl rfl), ?_, by rw [pentagonDiagram_wall_inl, hD.label_sndIndex]⟩
    rw [pentagonDiagram_wall_inl, hD.isRayFactorPresentation.normal, sndIndex_def]
  · exact ⟨μ j₁ + μ j₂, n₁ + n₂, hD.add_mem_monoid, hD.add_ne_zero, hD.apply_add_add, _,
      Or.inr (Or.inr rfl), by rw [pentagonDiagram_wall_inr, outgoingWall_normal],
      by rw [pentagonDiagram_wall_inr, outgoingWall_label]⟩

variable {M : Type*} [AddCommGroup M] (π : Γ →+ M) [HasUniqueDiv Γ]
  {S : Type*} [Semiring S] (φ : S →+* R) (hc₁ : c₁ ∈ φ.rangeS) (hc₂ : c₂ ∈ φ.rangeS)
  (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
  (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1)

include hc₁ hc₂ in
/-- Under the hypotheses of `exists_normal_eq_one_isUnit`, if the coefficients `c₁, c₂` lie in the
image of a semiring map `φ : S →+* R`, the discrete grouping of the pentagon diagram is positive
for the image of `S[Q]`: its wall functions are `1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}` and
`1 + c₁ c₂ z^{n₁ + n₂}` on the three nontrivial walls and `1` on all other walls. -/
theorem isPositive_discrete_pentagonDiagram :
    (FunctionWallGrouping.discrete hD.pentagonDiagram
      (hD.isPrimitive_pentagonDiagram_normal Q hQ₁ hQ₂) π).IsPositive
      ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS := by
  refine (FunctionWallGrouping.isPositive_iff _ _ _).mpr fun x => ?_
  obtain ⟨p, hp, hunit⟩ := hD.exists_normal_eq_one_isUnit Q hQ₁ hQ₂ x
  by_cases hx : x ∈ hD.pentagonIndices
  · obtain ⟨ν, n, hn, hn0, hν, b, hb, hnormal, hlabel⟩ := hD.exists_label_eq_binomialLabel hx
    have hbφ : b ∈ φ.rangeS := by
      rcases hb with rfl | rfl | rfl
      exacts [hc₁, hc₂, mul_mem hc₁ hc₂]
    refine ⟨binomialUnit d Q hn hn0 b,
      FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_,
      isPositive_binomialUnit d Q φ hn hn0 hbφ⟩
    rw [hlabel, completedBCHAction_binomialLabel, hnormal]
  · refine ⟨1, FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_,
      AlgFiltration.isPositive_one⟩
    rw [hD.pentagonDiagram_label_eq_one hx, map_one, AlgEquiv.one_apply, one_zpow,
      Units.val_one, one_mul]

include hc₁ hc₂ hQ₁ hQ₂ in
/-- Under the hypotheses of `isPositive_discrete_pentagonDiagram`, the pentagon diagram is a
positive wall representative for the image of `S[Q]`. -/
theorem isPositiveWallRepresentative_pentagonDiagram :
    hD.pentagonDiagram.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS π :=
  (hD.isPositive_discrete_pentagonDiagram Q π φ hc₁ hc₂ hQ₁ hQ₂).isPositiveWallRepresentative

end Positive

end IsTypeA₂Presentation

end Mei.DirectedDiagram

/-! ### Consistency, needing the lattices in `Type`

The pentagon identity `Mei.binomialLabel_pentagon` is transported through `ℤ × ℤ`, so the
theorems below take `Γ Λ : Type`. -/

namespace Mei.DirectedDiagram.IsTypeA₂Presentation

open _root_.AddMonoidAlgebra

variable {R : Type*} {Γ Λ : Type} {V ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ]
  [AddCommGroup Λ] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {latticeMap : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice latticeMap} {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : ι} {n₁ n₂ : Γ}
  {c₁ c₂ : R} (hD : D.IsTypeA₂Presentation g j₁ j₂ n₁ n₂ c₁ c₂)
include hD

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The labels of the three nontrivial walls of the pentagon diagram satisfy the pentagon identity
`θ[μ₂, n₂, c₂] θ[μ₁, n₁, c₁] = θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂] θ[μ₂, n₂, c₂]` of binomial
labels. -/
theorem pentagonDiagram_label_pentagon :
    (hD.pentagonDiagram.wall (.inl hD.sndIndex)).label *
        (hD.pentagonDiagram.wall (.inl hD.fstIndex)).label =
      (hD.pentagonDiagram.wall (.inl hD.fstIndex)).label *
        (hD.pentagonDiagram.wall (.inr ())).label *
        (hD.pentagonDiagram.wall (.inl hD.sndIndex)).label := by
  simp only [pentagonDiagram_wall_inl, pentagonDiagram_wall_inr, hD.label_fstIndex,
    hD.label_sndIndex, outgoingWall_label]
  exact binomialLabel_pentagon d ρ hD.mem_monoid_fst hD.mem_monoid_snd hD.ne_zero_fst
    hD.ne_zero_snd hD.apply_fst_fst hD.apply_snd_snd hD.apply_fst_snd hD.apply_snd_fst _ _

/-- The pentagon diagram is consistent. -/
theorem pentagonDiagram_consistent [HasUniqueDiv Γ] : hD.pentagonDiagram.Consistent := by
  -- The three nontrivial walls are consistent by the pentagon identity; all other walls are full
  -- hyperplanes with trivial labels.
  refine consistent_of_restrict_of_restrict_compl
    (hD.isPentagonConfiguration.consistent ?_) ?_ fun x _ x' hx' => ?_
  · simpa only [restrict_wall] using hD.pentagonDiagram_label_pentagon
  · refine consistent_of_commute_of_full _ (fun x => ?_) fun x x' => ?_
    · obtain ⟨x | u, hx⟩ := x
      · rw [restrict_wall, pentagonDiagram_wall_inl]
        exact hD.full x
      · exact absurd (hD.mem_pentagonIndices.mpr (Or.inr (Or.inr rfl))) hx
    · rw [restrict_wall, hD.pentagonDiagram_label_eq_one x.property]
      exact Commute.one_left _
  · rw [hD.pentagonDiagram_label_eq_one hx']
    exact Commute.one_right _

/-- The pentagon diagram is an outgoing completion of `D`: its walls indexed by the walls of `D` are
the walls of `D`, its remaining wall is outgoing, and it is consistent. -/
theorem isOutgoingCompletion_pentagonDiagram [HasUniqueDiv Γ] :
    IsOutgoingCompletion D.wall hD.pentagonDiagram where
  wall_inl := hD.pentagonDiagram_wall_inl
  outgoing_inr u := by
    rw [pentagonDiagram_wall_inr]
    exact hD.outgoingWall_outgoing
  consistent := hD.pentagonDiagram_consistent

/-- **The scattering diagram of type `A₂`.** For a ray presentation of type `A₂` with arbitrary
coefficients `c₁, c₂`, the outgoing scattering class of `D` is the class of the pentagon diagram,
with the one additional outgoing wall `{μ₁ + μ₂ = 0, μ₁ ≥ 0}` labelled by the binomial label of
`1 + c₁ c₂ z^{n₁ + n₂}`. -/
theorem scat_eq_toClass_pentagonDiagram [Module.Free ℤ Γ] :
    D.Scat hD.full = hD.pentagonDiagram.toClass :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  scat_eq_toClass _ _ hD.isOutgoingCompletion_pentagonDiagram

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]
  {M : Type*} [AddCommGroup M] (π : Γ →+ M) [Module.Free ℤ Γ]
  {S : Type*} [Semiring S] (φ : S →+* R) (hc₁ : c₁ ∈ φ.rangeS) (hc₂ : c₂ ∈ φ.rangeS)
  (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
  (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

include hc₁ hc₂ hQ₁ hQ₂ in
/-- **Positivity of ray presentations of type `A₂`.** If the coefficients `c₁, c₂` lie in the image
of a semiring map `φ : S →+* R`, and the coefficient monoid `Q` contains exponents `p₁, p₂` with
`-p₁, -p₂ ∈ Q`, `μ₁(ρ p₁) = 1`, `μ₂(ρ p₁) = 0` and `μ₂(ρ p₂) = 1`, the outgoing scattering class of
`D` has a consistent outgoing representative, the pentagon diagram, whose grouped wall functions
`1 + c₁ z^{n₁}`, `1 + c₂ z^{n₂}`, `1 + c₁ c₂ z^{n₁ + n₂}` (and `1` on the remaining walls) are
positive for the image of `S[Q]`, for every projection `π` of the monomial directions. -/
theorem exists_isPositiveWallRepresentative_scat :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H
        ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ κ)),
      IsOutgoingCompletion D.wall E ∧ E.toClass = D.Scat hD.full ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS π :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  ⟨Unit, hD.pentagonDiagram, hD.isOutgoingCompletion_pentagonDiagram,
    hD.scat_eq_toClass_pentagonDiagram.symm,
    hD.isPositiveWallRepresentative_pentagonDiagram Q π φ hc₁ hc₂ hQ₁ hQ₂⟩

end Positive

end Mei.DirectedDiagram.IsTypeA₂Presentation
