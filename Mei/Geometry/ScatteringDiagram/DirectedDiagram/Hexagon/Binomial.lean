/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hexagon.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Halfspace
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Binomial
public import Mei.Algebra.Lie.Logarithmic.Hexagon

/-!
# Ray presentations of two binomial labels of type `B₂`

Let `D` be the ray presentation (`DirectedDiagram.IsRayFactorPresentation`), in the tropical
vertex wall spaces of `(Γ, Λ, ρ)`, of labels `g_j` on the hyperplanes `{μ_j = 0}` through the
origin, indexed by two indices `j₁, j₂`. It is *of type `B₂`* with degrees `n₁, n₂` and
coefficients `c₁, c₂` (`DirectedDiagram.IsTypeB₂Presentation`) when `g_{j₁}` is the binomial label
`θ[μ_{j₁}, n₁, c₁]` of `1 + c₁ z^{n₁}`, `g_{j₂}` is the square `θ[μ_{j₂}, n₂, c₂]^2`, the label of
the wall function `(1 + c₂ z^{n₂})^2`, and the normals pair with the degrees by
`μ_{j₁}(ρ n₂) = -1` and `μ_{j₂}(ρ n₁) = 1`. Write `μ₁ = μ_{j₁}` and `μ₂ = μ_{j₂}`.

* Adding to `D` the half-hyperplanes `{μ₁ + μ₂ = 0, μ₁ ≥ 0}` and `{μ₁ + 2 μ₂ = 0, μ₁ ≥ 0}`,
  cooriented by `μ₁ + μ₂` and `μ₁ + 2 μ₂`, on the rays through `n₁ + n₂` and `n₁ + 2 n₂`, and
  labelled by `θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂]^2` and `θ[μ₁ + 2 μ₂, n₁ + 2 n₂, c₁ c₂^2]`
  (`IsTypeB₂Presentation.addWall`, `IsTypeB₂Presentation.addTwoWall`), gives a consistent diagram,
  the *hexagon diagram* (`IsTypeB₂Presentation.hexagonDiagram_consistent`). Its new walls are
  outgoing, so it is an outgoing completion of `D`
  (`IsTypeB₂Presentation.isOutgoingCompletion_hexagonDiagram`) and represents its scattering class
  (`IsTypeB₂Presentation.scat_eq_toClass_hexagonDiagram`).
* If `D` has a grouping of its walls into function walls (`FunctionWallGrouping`) which is
  positive for the image of `S[Q]` under a semiring map `φ : S →+* R`, the products `c₁ c₂` and
  `c₁ c₂^2` lie in the image of `φ`, and the coefficient monoid `Q` contains exponents `p, p'`
  with `-p, -p' ∈ Q`, `(μ₁ + μ₂)(ρ p) = 1` and `(μ₁ + 2 μ₂)(ρ p') = 1`, then the hexagon diagram is
  a positive wall representative of the scattering class: its grouping is that of `D` together
  with the two outgoing walls, with the wall functions `(1 + c₁ c₂ z^{n₁ + n₂})^2` and
  `1 + c₁ c₂^2 z^{n₁ + 2 n₂}`
  (`IsTypeB₂Presentation.isPositiveWallRepresentative_hexagonDiagram_of_isPositive`,
  `IsTypeB₂Presentation.exists_isPositiveWallRepresentative_scat_of_isPositive`). If `c₁, c₂` lie
  in the image of `φ`, and `Q` contains `p₁` with `-p₁ ∈ Q`, `μ₁(ρ p₁) = 1` and `μ₂(ρ p₁) = 0`,
  and `p₂` with `-p₂ ∈ Q` and `μ₂(ρ p₂) = 1`, the discrete grouping of `D` is positive, with the
  wall functions `1 + c₁ z^{n₁}` and `(1 + c₂ z^{n₂})^2` on the walls on the rays through `n₁` and
  `n₂` and `1` on all other walls (`IsTypeB₂Presentation.exists_isPositiveWallRepresentative_scat`).

The walls of `D` on the rays through `n₁` and `n₂` carry the labels `g_{j₁}` and `g_{j₂}`, all its
other walls have trivial labels (`IsTypeB₂Presentation.label_eq_one`), and the four distinguished
walls of the hexagon diagram, namely these two walls and the two outgoing walls, are in hexagon
configuration (`IsTypeB₂Presentation.isHexagonConfiguration`); their labels satisfy the hexagon
identity `Mei.binomialLabel_hexagon` of the tropical vertex group.

The consistent diagram is the scattering diagram of type `B₂`, the case `ℓ₁ = 1`, `ℓ₂ = 2` of
Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*, Example 1.6
(arXiv:0902.0779v3).
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

/-- The diagram `D` is a ray presentation *of type `B₂`* of the labels `g_j` at the indices
`j₁, j₂` with degrees `n₁, n₂` and coefficients `c₁, c₂`: it is the ray presentation of the `g_j`
on the hyperplanes `{μ_j = 0}`, every index is `j₁` or `j₂`, the degrees `n₁, n₂` are allowed with
`μ_{j₁}(ρ n₁) = μ_{j₂}(ρ n₂) = 0`, `μ_{j₁}(ρ n₂) = -1` and `μ_{j₂}(ρ n₁) = 1`, `g_{j₁}` is the
binomial label of `1 + c₁ z^{n₁}` with the normal `μ_{j₁}`, and `g_{j₂}` is the square of the
binomial label of `1 + c₂ z^{n₂}` with the normal `μ_{j₂}`, the label of `(1 + c₂ z^{n₂})^2`. -/
structure IsTypeB₂Presentation {μ : ι → Λ →+ ℤ}
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
  /-- The second label is the square of the binomial label of `1 + c₂ z^{n₂}`. -/
  label_snd : g j₂ = binomialLabel d ρ (μ j₂) mem_monoid_snd
    (ne_zero_of_map (f := ρ) (ne_zero_of_map (f := -μ j₁) (by simp [apply_fst_snd])))
    apply_snd_snd c₂ ^ 2

namespace IsTypeB₂Presentation

-- The binder types spell out the wall spaces and the grading: the local notations `H` and `ℒ` do
-- not elaborate inside `variable` binders here.
variable {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : ι} {n₁ n₂ : Γ}
  {c₁ c₂ : R} (hD : D.IsTypeB₂Presentation g j₁ j₂ n₁ n₂ c₁ c₂)
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

/-- The degree `n₁ + 2 n₂` is tangent to the normal `μ₁ + 2 μ₂`. -/
theorem apply_add_two : (μ j₁ + 2 • μ j₂) (ρ (n₁ + 2 • n₂)) = 0 := by
  simp [hD.apply_fst_fst, hD.apply_fst_snd, hD.apply_snd_fst, hD.apply_snd_snd]

/-- The sum `n₁ + n₂` is an allowed degree. -/
theorem add_mem_monoid : n₁ + n₂ ∈ d.monoid := add_mem hD.mem_monoid_fst hD.mem_monoid_snd

/-- The degree `n₁ + 2 n₂` is allowed. -/
theorem add_two_mem_monoid : n₁ + 2 • n₂ ∈ d.monoid :=
  add_mem hD.mem_monoid_fst (nsmul_mem hD.mem_monoid_snd 2)

/-- The sum `n₁ + n₂` is nonzero. -/
theorem add_ne_zero : n₁ + n₂ ≠ 0 :=
  d.add_ne_zero hD.mem_monoid_fst hD.mem_monoid_snd hD.ne_zero_fst

/-- The degree `n₁ + 2 n₂` is nonzero. -/
theorem add_two_ne_zero : n₁ + 2 • n₂ ≠ 0 :=
  d.add_ne_zero hD.mem_monoid_fst (nsmul_mem hD.mem_monoid_snd 2) hD.ne_zero_fst

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
    (TauCeti.isPrimitive_def.mpr ⟨((μ j₂).comp ρ).toIntLinearMap, by
      simp [hD.apply_snd_fst, hD.apply_snd_snd]⟩)

/-- The supported ray through `n₁ + 2 n₂`: the degree `n₁ + 2 n₂` is primitive, since
`μ₂(ρ (n₁ + 2 n₂)) = 1`. -/
def addTwoRay : SupportedRay d :=
  SupportedRay.ofMem (n₁ + 2 • n₂) hD.add_two_mem_monoid
    (TauCeti.isPrimitive_def.mpr ⟨((μ j₂).comp ρ).toIntLinearMap, by
      simp [hD.apply_snd_fst, hD.apply_snd_snd]⟩)

/-- The generator of the first ray is `n₁`. -/
@[simp]
theorem fstRay_generator : hD.fstRay.generator = n₁ := SupportedRay.generator_ofMem ..

/-- The generator of the second ray is `n₂`. -/
@[simp]
theorem sndRay_generator : hD.sndRay.generator = n₂ := SupportedRay.generator_ofMem ..

/-- The generator of the ray through `n₁ + n₂` is `n₁ + n₂`. -/
@[simp]
theorem addRay_generator : hD.addRay.generator = n₁ + n₂ := SupportedRay.generator_ofMem ..

/-- The generator of the ray through `n₁ + 2 n₂` is `n₁ + 2 n₂`. -/
@[simp]
theorem addTwoRay_generator : hD.addTwoRay.generator = n₁ + 2 • n₂ :=
  SupportedRay.generator_ofMem ..

/-- The degree `n₁` lies on the first ray. -/
theorem mem_fstRay_rayDegrees : n₁ ∈ hD.fstRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₂` lies on the second ray. -/
theorem mem_sndRay_rayDegrees : n₂ ∈ hD.sndRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₁ + n₂` lies on the ray through it. -/
theorem mem_addRay_rayDegrees : n₁ + n₂ ∈ hD.addRay.rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

/-- The degree `n₁ + 2 n₂` lies on the ray through it. -/
theorem mem_addTwoRay_rayDegrees : n₁ + 2 • n₂ ∈ hD.addTwoRay.rayDegrees :=
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

/-- The square of the second binomial label lies on the ray through `n₂`. -/
theorem sq_binomialLabel_mem_completedRaySubgroup :
    binomialLabel d ρ (μ j₂) hD.mem_monoid_snd hD.ne_zero_snd hD.apply_snd_snd c₂ ^ 2 ∈
      d.completedRaySubgroup ℒ hD.sndRay :=
  pow_mem (binomialLabel_mem_completedRaySubgroup d ρ _ _ _ _ _ hD.mem_sndRay_rayDegrees) 2

/-- The wall of `D` over the first hyperplane on the ray through `n₁` is labelled by the binomial
label of `1 + c₁ z^{n₁}`. -/
theorem label_fstIndex : (D.wall hD.fstIndex).label =
    binomialLabel d ρ (μ j₁) hD.mem_monoid_fst hD.ne_zero_fst hD.apply_fst_fst c₁ := by
  rw [hD.isRayFactorPresentation.label, fstIndex_def, hD.label_fst]
  exact rayFactor_binomialLabel_self d ρ _ _ _ _ _ hD.mem_fstRay_rayDegrees

/-- The wall of `D` over the second hyperplane on the ray through `n₂` is labelled by the square
of the binomial label of `1 + c₂ z^{n₂}`. -/
theorem label_sndIndex : (D.wall hD.sndIndex).label =
    binomialLabel d ρ (μ j₂) hD.mem_monoid_snd hD.ne_zero_snd hD.apply_snd_snd c₂ ^ 2 := by
  rw [hD.isRayFactorPresentation.label, sndIndex_def, hD.label_snd]
  exact d.rayFactor_eq_self ℒ hD.sq_binomialLabel_mem_completedRaySubgroup

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
  · refine hD.label_snd.symm ▸ d.rayFactor_eq_one ℒ hD.sq_binomialLabel_mem_completedRaySubgroup
      fun he => h₂ ?_
    subst he
    exact hD.sndIndex_def.symm

/-- Every wall of `D` is a full hyperplane, as required for outgoing completion. -/
theorem full (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    ∃ b : ℝ, (D.wall x).support = {y | h.realCharacter (D.wall x).normal y = b} :=
  ⟨0, by rw [hD.isRayFactorPresentation.support, hD.isRayFactorPresentation.normal]⟩

/-- The square of the binomial label of `1 + c₁ c₂ z^{n₁ + n₂}` with the normal `μ₁ + μ₂`, the
label of `(1 + c₁ c₂ z^{n₁ + n₂})^2`, as a wall label of the ray through `n₁ + n₂`. -/
def addLabel : (H).wallGroup hD.addRay (μ j₁ + μ j₂) :=
  ⟨binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add
      (c₁ * c₂) ^ 2,
    pow_mem (binomialLabel_mem_wallGroup d ρ _ _ _ _ _ hD.mem_addRay_rayDegrees) 2⟩

/-- The binomial label of `1 + c₁ c₂^2 z^{n₁ + 2 n₂}` with the normal `μ₁ + 2 μ₂`, as a wall label
of the ray through `n₁ + 2 n₂`. -/
def addTwoLabel : (H).wallGroup hD.addTwoRay (μ j₁ + 2 • μ j₂) :=
  ⟨binomialLabel d ρ (μ j₁ + 2 • μ j₂) hD.add_two_mem_monoid hD.add_two_ne_zero hD.apply_add_two
      (c₁ * c₂ ^ 2),
    binomialLabel_mem_wallGroup d ρ _ _ _ _ _ hD.mem_addTwoRay_rayDegrees⟩

/-- The label of the outgoing wall on the ray through `n₁ + n₂` is the square of the binomial
label of `1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem coe_addLabel : (hD.addLabel : d.completedBCHGroup ℒ) =
    binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add
      (c₁ * c₂) ^ 2 :=
  (rfl)

/-- The label of the outgoing wall on the ray through `n₁ + 2 n₂` is the binomial label of
`1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. -/
@[simp]
theorem coe_addTwoLabel : (hD.addTwoLabel : d.completedBCHGroup ℒ) =
    binomialLabel d ρ (μ j₁ + 2 • μ j₂) hD.add_two_mem_monoid hD.add_two_ne_zero
      hD.apply_add_two (c₁ * c₂ ^ 2) :=
  (rfl)

/-- The outgoing wall on the ray through `n₁ + n₂`: the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}`,
cooriented by `μ₁ + μ₂`, labelled by the label of `(1 + c₁ c₂ z^{n₁ + n₂})^2`. -/
def addWall : DirectedWall (d := d) h H :=
  (DirectedWall.ofAffineHyperplane h H (μ j₁ + μ j₂)
    (fun he => by
      have h₁ := congrArg (fun ν : Λ →+ ℤ => ν (ρ (-n₂))) he
      simp [hD.apply_fst_snd, hD.apply_snd_snd] at h₁)
    0 hD.addRay (by rw [addRay_generator]; exact hD.apply_add_add) hD.addLabel)
    |>.cutHalfspace (μ j₁) 0 ⟨latticeMap (ρ (-(n₁ + n₂))), by
      simp [hD.apply_fst_fst, hD.apply_fst_snd, hD.apply_snd_fst, hD.apply_snd_snd], by
      simp [hD.apply_fst_fst, hD.apply_fst_snd]⟩

/-- The outgoing wall on the ray through `n₁ + 2 n₂`: the half-hyperplane
`{μ₁ + 2 μ₂ = 0, μ₁ ≥ 0}`, cooriented by `μ₁ + 2 μ₂`, labelled by the binomial label of
`1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. -/
def addTwoWall : DirectedWall (d := d) h H :=
  (DirectedWall.ofAffineHyperplane h H (μ j₁ + 2 • μ j₂)
    (fun he => by
      have h₁ := congrArg (fun ν : Λ →+ ℤ => ν (ρ (-n₂))) he
      simp [hD.apply_fst_snd, hD.apply_snd_snd] at h₁)
    0 hD.addTwoRay (by rw [addTwoRay_generator]; exact hD.apply_add_two) hD.addTwoLabel)
    |>.cutHalfspace (μ j₁) 0 ⟨latticeMap (ρ (-(n₁ + 2 • n₂))), by
      simp [hD.apply_fst_fst, hD.apply_fst_snd, hD.apply_snd_fst, hD.apply_snd_snd], by
      simp [hD.apply_fst_fst, hD.apply_fst_snd]⟩

/-- The first outgoing wall is cooriented by `μ₁ + μ₂`. -/
@[simp]
theorem addWall_normal : hD.addWall.normal = μ j₁ + μ j₂ := by
  rw [addWall, DirectedWall.cutHalfspace_normal, DirectedWall.ofAffineHyperplane_normal]

/-- The second outgoing wall is cooriented by `μ₁ + 2 μ₂`. -/
@[simp]
theorem addTwoWall_normal : hD.addTwoWall.normal = μ j₁ + 2 • μ j₂ := by
  rw [addTwoWall, DirectedWall.cutHalfspace_normal, DirectedWall.ofAffineHyperplane_normal]

/-- The first outgoing wall lies on the ray through `n₁ + n₂`. -/
@[simp]
theorem addWall_ray : hD.addWall.ray = hD.addRay := by
  rw [addWall, DirectedWall.cutHalfspace_ray, DirectedWall.ofAffineHyperplane_ray]

/-- The second outgoing wall lies on the ray through `n₁ + 2 n₂`. -/
@[simp]
theorem addTwoWall_ray : hD.addTwoWall.ray = hD.addTwoRay := by
  rw [addTwoWall, DirectedWall.cutHalfspace_ray, DirectedWall.ofAffineHyperplane_ray]

/-- The first outgoing wall is supported on the half-hyperplane `{μ₁ + μ₂ = 0, μ₁ ≥ 0}`. -/
@[simp]
theorem addWall_support : hD.addWall.support =
    {x | h.realCharacter (μ j₁ + μ j₂) x = 0} ∩ {x | 0 ≤ h.realCharacter (μ j₁) x} := by
  rw [addWall, DirectedWall.cutHalfspace_support, DirectedWall.ofAffineHyperplane_support]

/-- The second outgoing wall is supported on the half-hyperplane `{μ₁ + 2 μ₂ = 0, μ₁ ≥ 0}`. -/
@[simp]
theorem addTwoWall_support : hD.addTwoWall.support =
    {x | h.realCharacter (μ j₁ + 2 • μ j₂) x = 0} ∩ {x | 0 ≤ h.realCharacter (μ j₁) x} := by
  rw [addTwoWall, DirectedWall.cutHalfspace_support, DirectedWall.ofAffineHyperplane_support]

/-- The first outgoing wall is labelled by the square of the binomial label of
`1 + c₁ c₂ z^{n₁ + n₂}`. -/
@[simp]
theorem addWall_label : hD.addWall.label =
    binomialLabel d ρ (μ j₁ + μ j₂) hD.add_mem_monoid hD.add_ne_zero hD.apply_add_add
      (c₁ * c₂) ^ 2 := by
  rw [addWall, DirectedWall.cutHalfspace_label, DirectedWall.ofAffineHyperplane_label,
    coe_addLabel]

/-- The second outgoing wall is labelled by the binomial label of `1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. -/
@[simp]
theorem addTwoWall_label : hD.addTwoWall.label =
    binomialLabel d ρ (μ j₁ + 2 • μ j₂) hD.add_two_mem_monoid hD.add_two_ne_zero
      hD.apply_add_two (c₁ * c₂ ^ 2) := by
  rw [addTwoWall, DirectedWall.cutHalfspace_label, DirectedWall.ofAffineHyperplane_label,
    coe_addTwoLabel]

/-- The first outgoing wall is outgoing: the direction `n₁ + n₂` of its ray, on which `μ₁` is
negative, is not a recession direction of its support. -/
theorem addWall_outgoing : hD.addWall.Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [addWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  simp [hD.apply_fst_fst, hD.apply_fst_snd] at hinc

/-- The second outgoing wall is outgoing: the direction `n₁ + 2 n₂` of its ray, on which `μ₁` is
negative, is not a recession direction of its support. -/
theorem addTwoWall_outgoing : hD.addTwoWall.Outgoing := by
  refine (DirectedWall.outgoing_iff _).mpr fun hrec => ?_
  have hinc := (DirectedWall.incoming_iff _).mpr (Set.mem_recessionCone.mp hrec)
  rw [addTwoWall, DirectedWall.incoming_cutHalfspace_iff _ _ _ _
    (DirectedWall.ofAffineHyperplane_incoming ..)] at hinc
  simp [hD.apply_fst_fst, hD.apply_fst_snd] at hinc

/-- The two outgoing walls of the hexagon diagram, on the rays through `n₁ + n₂` and
`n₁ + 2 n₂`. -/
def outgoingDiagram : DirectedDiagram (d := d) h H (Fin 2) :=
  ofFinite ![hD.addWall, hD.addTwoWall]

/-- The first outgoing wall is on the ray through `n₁ + n₂`. -/
@[simp]
theorem outgoingDiagram_wall_zero : hD.outgoingDiagram.wall 0 = hD.addWall := by
  rw [outgoingDiagram, ofFinite_wall, Matrix.cons_val_zero]

/-- The second outgoing wall is on the ray through `n₁ + 2 n₂`. -/
@[simp]
theorem outgoingDiagram_wall_one : hD.outgoingDiagram.wall 1 = hD.addTwoWall := by
  rw [outgoingDiagram, ofFinite_wall, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- The hexagon diagram: the diagram `D` together with the two outgoing walls. -/
def hexagonDiagram :
    DirectedDiagram (d := d) h H ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Fin 2) :=
  D.append hD.outgoingDiagram

/-- The walls of the hexagon diagram indexed by the walls of `D` are the walls of `D`. -/
@[simp]
theorem hexagonDiagram_wall_inl (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    hD.hexagonDiagram.wall (.inl x) = D.wall x := by
  rw [hexagonDiagram, append_wall_inl]

/-- The remaining walls of the hexagon diagram are the two outgoing walls. -/
@[simp]
theorem hexagonDiagram_wall_inr (i : Fin 2) :
    hD.hexagonDiagram.wall (.inr i) = hD.outgoingDiagram.wall i := by
  rw [hexagonDiagram, append_wall_inr]

/-- The four distinguished `B₂` walls of the hexagon diagram: the walls of `D` on the rays through
`n₁` and `n₂` and the two outgoing walls. -/
def hexagonIndices : Set ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Fin 2) :=
  {.inl hD.fstIndex, .inl hD.sndIndex, .inr 0, .inr 1}

/-- Membership in the four distinguished `B₂` walls. -/
theorem mem_hexagonIndices {x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Fin 2} :
    x ∈ hD.hexagonIndices ↔
      x = .inl hD.fstIndex ∨ x = .inl hD.sndIndex ∨ x = .inr 0 ∨ x = .inr 1 :=
  Iff.rfl

/-- Every outgoing wall is one of the four distinguished `B₂` walls. -/
theorem inr_mem_hexagonIndices (i : Fin 2) : .inr i ∈ hD.hexagonIndices := by
  fin_cases i <;> simp [mem_hexagonIndices]

/-- The walls of the hexagon diagram outside the four distinguished `B₂` walls have trivial
labels. -/
theorem hexagonDiagram_label_eq_one [HasUniqueDiv Γ]
    {x : (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ Fin 2}
    (hx : x ∉ hD.hexagonIndices) : (hD.hexagonDiagram.wall x).label = 1 := by
  rcases x with x | i
  · rw [hexagonDiagram_wall_inl]
    exact hD.label_eq_one (fun he => hx (he ▸ Or.inl rfl)) fun he => hx (he ▸ Or.inr (Or.inl rfl))
  · exact absurd (hD.inr_mem_hexagonIndices i) hx

/-- The four distinguished `B₂` walls of the hexagon diagram are in hexagon configuration: the
hyperplanes `{μ₁ = 0}`, `{μ₂ = 0}` and the half-hyperplanes `{μ₁ + μ₂ = 0, μ₁ ≥ 0}` and
`{μ₁ + 2 μ₂ = 0, μ₁ ≥ 0}` cooriented by `μ₁ + μ₂` and `μ₁ + 2 μ₂`. -/
theorem isHexagonConfiguration :
    (hD.hexagonDiagram.restrict hD.hexagonIndices).IsHexagonConfiguration
      ⟨.inl hD.fstIndex, hD.mem_hexagonIndices.mpr (Or.inl rfl)⟩
      ⟨.inl hD.sndIndex, hD.mem_hexagonIndices.mpr (Or.inr (Or.inl rfl))⟩
      ⟨.inr 0, hD.inr_mem_hexagonIndices 0⟩ ⟨.inr 1, hD.inr_mem_hexagonIndices 1⟩
      (μ j₁) (μ j₂) where
  eq_or_eq_or_eq_or_eq := by
    rintro ⟨x, hx⟩
    rcases hD.mem_hexagonIndices.mp hx with rfl | rfl | rfl | rfl <;> simp
  normal_fst := by simp [hD.isRayFactorPresentation.normal, fstIndex_def]
  normal_snd := by simp [hD.isRayFactorPresentation.normal, sndIndex_def]
  normal_add := by simp
  normal_add_two := by simp
  support_fst := by simp [hD.isRayFactorPresentation.support, fstIndex_def]
  support_snd := by simp [hD.isRayFactorPresentation.support, sndIndex_def]
  support_add := by
    ext x
    simp
  support_add_two := by
    ext x
    simp
  exists_fst := ⟨latticeMap (ρ n₁), by simp [hD.apply_fst_fst], by simp [hD.apply_snd_fst]⟩
  exists_snd := ⟨latticeMap (ρ n₂), by simp [hD.apply_snd_snd], by simp [hD.apply_fst_snd]⟩

/-- The coorientation `μ₁ + μ₂` of the first outgoing wall is primitive: it takes the value one at
`-ρ n₂`. -/
theorem isPrimitive_addWall_normal : TauCeti.IsPrimitive hD.addWall.normal :=
  TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (ρ (-n₂))),
    by simp [hD.apply_fst_snd, hD.apply_snd_snd]⟩

/-- The coorientation `μ₁ + 2 μ₂` of the second outgoing wall is primitive: it takes the value one
at `-ρ n₂`. -/
theorem isPrimitive_addTwoWall_normal : TauCeti.IsPrimitive hD.addTwoWall.normal :=
  TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (ρ (-n₂))),
    by simp [hD.apply_fst_snd, hD.apply_snd_snd]⟩

/-- The coorientation of every wall of `D` is primitive: `μ₁` takes the value one at `-ρ n₂` and
`μ₂` takes the value one at `ρ n₁`. -/
theorem isPrimitive_normal (x : Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) :
    TauCeti.IsPrimitive (D.wall x).normal := by
  obtain ⟨j, w⟩ := x
  rw [hD.isRayFactorPresentation.normal]
  rcases hD.eq_or_eq j with rfl | rfl
  · exact TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (ρ (-n₂))),
      by simp [hD.apply_fst_snd]⟩
  · exact TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval (ρ n₁)),
      hD.apply_snd_fst⟩

/-- The coorientation of every outgoing wall is primitive. -/
theorem isPrimitive_outgoingDiagram_normal (i : Fin 2) :
    TauCeti.IsPrimitive (hD.outgoingDiagram.wall i).normal := by
  fin_cases i
  · simpa using hD.isPrimitive_addWall_normal
  · simpa using hD.isPrimitive_addTwoWall_normal

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

variable {M : Type*} [AddCommGroup M] (π : Γ →+ M) [HasUniqueDiv Γ]
  {S : Type*} [Semiring S] (φ : S →+* R)

omit [HasUniqueDiv Γ] in
/-- If the products `c₁ c₂` and `c₁ c₂^2` lie in the image of a semiring map `φ : S →+* R`, and
the coefficient monoid `Q` contains exponents `p, p'` with `-p, -p' ∈ Q`, `(μ₁ + μ₂)(ρ p) = 1` and
`(μ₁ + 2 μ₂)(ρ p') = 1`, the discrete grouping of the two outgoing walls is positive for the image
of `S[Q]`: their wall functions are `(1 + c₁ c₂ z^{n₁ + n₂})^2` and
`1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. -/
theorem isPositive_discrete_outgoingDiagram (hc : c₁ * c₂ ∈ φ.rangeS)
    (hc' : c₁ * c₂ ^ 2 ∈ φ.rangeS) (hQ : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + μ j₂) (ρ p) = 1)
    (hQ' : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + 2 • μ j₂) (ρ p) = 1) :
    (FunctionWallGrouping.discrete hD.outgoingDiagram hD.isPrimitive_outgoingDiagram_normal
      π).IsPositive ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS := by
  refine (FunctionWallGrouping.isPositive_iff _ _ _).mpr fun i => ?_
  fin_cases i
  · obtain ⟨p, hp, hp', h₀⟩ := hQ
    refine ⟨binomialUnit d Q hD.add_mem_monoid hD.add_ne_zero (c₁ * c₂) ^ 2,
      FunctionWallGrouping.isWallFunction_discrete _ _ (j := 0) (p := ⟨p, hp⟩) (by simpa using h₀)
        (TropicalVertexCoefficientAction.isUnit_toCompletion_single hp hp') fun q r => ?_, ?_⟩
    · simp only [outgoingDiagram_wall_zero, addWall_label,
        completedBCHAction_binomialLabel_pow, addWall_normal]
    · rw [Units.val_pow_eq_pow_val]
      exact (isPositive_binomialUnit d Q φ _ _ hc).pow 2
  · obtain ⟨p, hp, hp', h₁⟩ := hQ'
    refine ⟨binomialUnit d Q hD.add_two_mem_monoid hD.add_two_ne_zero (c₁ * c₂ ^ 2),
      FunctionWallGrouping.isWallFunction_discrete _ _ (j := 1) (p := ⟨p, hp⟩) (by simpa using h₁)
        (TropicalVertexCoefficientAction.isUnit_toCompletion_single hp hp') fun q r => ?_,
      isPositive_binomialUnit d Q φ _ _ hc'⟩
    simp only [outgoingDiagram_wall_one, addTwoWall_label,
      completedBCHAction_binomialLabel, addTwoWall_normal]

omit [HasUniqueDiv Γ] in
/-- **Positivity of the hexagon diagram from a positive grouping of `D`.** Let `G` be a grouping of
the walls of `D` into function walls for the projection `π`, positive for the image of `S[Q]`. If
the products `c₁ c₂` and `c₁ c₂^2` lie in the image of a semiring map `φ : S →+* R`, and the
coefficient monoid `Q` contains exponents `p, p'` with `-p, -p' ∈ Q`, `(μ₁ + μ₂)(ρ p) = 1` and
`(μ₁ + 2 μ₂)(ρ p') = 1`, the hexagon diagram is a positive wall representative for the image of
`S[Q]`: the groups of `G` and the two outgoing walls, with the wall functions
`(1 + c₁ c₂ z^{n₁ + n₂})^2` and `1 + c₁ c₂^2 z^{n₁ + 2 n₂}`, form a positive grouping. -/
theorem isPositiveWallRepresentative_hexagonDiagram_of_isPositive (hc : c₁ * c₂ ∈ φ.rangeS)
    (hc' : c₁ * c₂ ^ 2 ∈ φ.rangeS) (hQ : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + μ j₂) (ρ p) = 1)
    (hQ' : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + 2 • μ j₂) (ρ p) = 1) {κ' : Type*}
    {G : D.FunctionWallGrouping π κ'}
    (hG : G.IsPositive ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS) :
    hD.hexagonDiagram.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS π :=
  (hG.append
    (hD.isPositive_discrete_outgoingDiagram Q π φ hc hc' hQ hQ')).isPositiveWallRepresentative

/-- If the coefficients `c₁, c₂` lie in the image of a semiring map `φ : S →+* R`, and `Q`
contains exponents `p₁, p₂` with `-p₁, -p₂ ∈ Q`, `μ₁(ρ p₁) = 1` and `μ₂(ρ p₂) = 1`, the discrete
grouping of `D` is positive for the image of `S[Q]`: its wall functions are `1 + c₁ z^{n₁}` and
`(1 + c₂ z^{n₂})^2` on the walls over the rays through `n₁` and `n₂`, and `1` on all other
walls. -/
theorem isPositive_discrete (hc₁ : c₁ ∈ φ.rangeS) (hc₂ : c₂ ∈ φ.rangeS)
    (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1) (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1) :
    (FunctionWallGrouping.discrete D hD.isPrimitive_normal π).IsPositive
      ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS := by
  refine (FunctionWallGrouping.isPositive_iff _ _ _).mpr fun x => ?_
  -- The normal of `x` is `μ₁` or `μ₂`, and takes the value one at `p₁` or `p₂`.
  obtain ⟨p, hp, hunit⟩ : ∃ p : Q, (D.wall x).normal (ρ p) = 1 ∧
      IsUnit ((F).toCompletion (single p (1 : R))) := by
    obtain ⟨p, hp, hp', h₁⟩ : ∃ p ∈ Q, -p ∈ Q ∧ (D.wall x).normal (ρ p) = 1 := by
      rw [hD.isRayFactorPresentation.normal]
      rcases hD.eq_or_eq x.1 with he | he <;> rw [he]
      exacts [hQ₁, hQ₂]
    exact ⟨⟨p, hp⟩, h₁, TropicalVertexCoefficientAction.isUnit_toCompletion_single hp hp'⟩
  by_cases hfst : x = hD.fstIndex
  · subst hfst
    refine ⟨binomialUnit d Q hD.mem_monoid_fst hD.ne_zero_fst c₁,
      FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_,
      isPositive_binomialUnit d Q φ hD.mem_monoid_fst hD.ne_zero_fst hc₁⟩
    rw [hD.label_fstIndex, completedBCHAction_binomialLabel, hD.isRayFactorPresentation.normal,
      fstIndex_def]
  by_cases hsnd : x = hD.sndIndex
  · subst hsnd
    refine ⟨binomialUnit d Q hD.mem_monoid_snd hD.ne_zero_snd c₂ ^ 2,
      FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_, ?_⟩
    · rw [hD.label_sndIndex, completedBCHAction_binomialLabel_pow,
        hD.isRayFactorPresentation.normal, sndIndex_def]
    · rw [Units.val_pow_eq_pow_val]
      exact (isPositive_binomialUnit d Q φ hD.mem_monoid_snd hD.ne_zero_snd hc₂).pow 2
  · refine ⟨1, FunctionWallGrouping.isWallFunction_discrete _ _ hp hunit fun q r => ?_,
      AlgFiltration.isPositive_one⟩
    rw [hD.label_eq_one hfst hsnd, map_one, AlgEquiv.one_apply, one_zpow, Units.val_one, one_mul]

/-- **Positivity of the hexagon diagram.** If the coefficients `c₁, c₂` lie in the image of a
semiring map `φ : S →+* R`, and `Q` contains exponents `p₁, p₂` with `-p₁, -p₂ ∈ Q`,
`μ₁(ρ p₁) = 1`, `μ₂(ρ p₁) = 0` and `μ₂(ρ p₂) = 1`, the hexagon diagram is a positive wall
representative for the image of `S[Q]`, with grouped wall functions `1 + c₁ z^{n₁}`,
`(1 + c₂ z^{n₂})^2`, `(1 + c₁ c₂ z^{n₁ + n₂})^2`, `1 + c₁ c₂^2 z^{n₁ + 2 n₂}` and `1` on the
remaining walls. -/
theorem isPositiveWallRepresentative_hexagonDiagram (hc₁ : c₁ ∈ φ.rangeS) (hc₂ : c₂ ∈ φ.rangeS)
    (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
    (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1) :
    hD.hexagonDiagram.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ)
      (mapRingHom Q φ).rangeS π := by
  obtain ⟨p, hp, hp', h₁, h₂⟩ := hQ₁
  exact hD.isPositiveWallRepresentative_hexagonDiagram_of_isPositive Q π φ (mul_mem hc₁ hc₂)
    (mul_mem hc₁ (pow_mem hc₂ 2)) ⟨p, hp, hp', by simp [h₁, h₂]⟩ ⟨p, hp, hp', by simp [h₁, h₂]⟩
    (hD.isPositive_discrete Q π φ hc₁ hc₂ ⟨p, hp, hp', h₁⟩ hQ₂)

end Positive

end IsTypeB₂Presentation

end Mei.DirectedDiagram

/-! ### Consistency, needing the lattices in `Type`

The hexagon identity `Mei.binomialLabel_hexagon` is derived from the pentagon identity, which is
transported through `ℤ × ℤ`, so the theorems below take `Γ Λ : Type`. -/

namespace Mei.DirectedDiagram.IsTypeB₂Presentation

open _root_.AddMonoidAlgebra

variable {R : Type*} {Γ Λ : Type} {V ι : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup Γ]
  [AddCommGroup Λ] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {d : PositiveDegrees Γ} {ρ : Γ →+ Λ} {latticeMap : Λ →+ V}
  {h : TauCeti.Toric.IsIntegralLattice latticeMap} {μ : ι → Λ →+ ℤ}
  {D : DirectedDiagram (d := d) h (tropicalVertexWallSpaces (R := R) d ρ)
    (Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0})}
  {g : ι → d.completedBCHGroup (tropicalVertexGrading (R := R) d ρ)} {j₁ j₂ : ι} {n₁ n₂ : Γ}
  {c₁ c₂ : R} (hD : D.IsTypeB₂Presentation g j₁ j₂ n₁ n₂ c₁ c₂)
include hD

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The labels of the four distinguished `B₂` walls of the hexagon diagram satisfy the hexagon
identity `θ[μ₂, n₂, c₂]^2 θ[μ₁, n₁, c₁] =
θ[μ₁, n₁, c₁] θ[μ₁ + μ₂, n₁ + n₂, c₁ c₂]^2 θ[μ₁ + 2 μ₂, n₁ + 2 n₂, c₁ c₂^2] θ[μ₂, n₂, c₂]^2` of
binomial labels. -/
theorem hexagonDiagram_label_hexagon :
    (hD.hexagonDiagram.wall (.inl hD.sndIndex)).label *
        (hD.hexagonDiagram.wall (.inl hD.fstIndex)).label =
      (hD.hexagonDiagram.wall (.inl hD.fstIndex)).label *
        (hD.hexagonDiagram.wall (.inr 0)).label * (hD.hexagonDiagram.wall (.inr 1)).label *
        (hD.hexagonDiagram.wall (.inl hD.sndIndex)).label := by
  simp only [hexagonDiagram_wall_inl, hexagonDiagram_wall_inr, outgoingDiagram_wall_zero,
    outgoingDiagram_wall_one, hD.label_fstIndex, hD.label_sndIndex, addWall_label,
    addTwoWall_label]
  exact binomialLabel_hexagon d ρ hD.mem_monoid_fst hD.mem_monoid_snd hD.ne_zero_fst
    hD.ne_zero_snd hD.apply_fst_fst hD.apply_snd_snd hD.apply_fst_snd hD.apply_snd_fst _ _

/-- The hexagon diagram is consistent. -/
theorem hexagonDiagram_consistent [HasUniqueDiv Γ] : hD.hexagonDiagram.Consistent := by
  -- The four distinguished walls are consistent by the hexagon identity; all other walls are
  -- full hyperplanes with trivial labels.
  refine consistent_of_restrict_of_restrict_compl
    (hD.isHexagonConfiguration.consistent ?_) ?_ fun a _ b hb => ?_
  · simpa only [restrict_wall] using hD.hexagonDiagram_label_hexagon
  · refine consistent_of_commute_of_full _ (fun x => ?_) fun x x' => ?_
    · obtain ⟨x | i, hx⟩ := x
      · rw [restrict_wall, hexagonDiagram_wall_inl]
        exact hD.full x
      · exact absurd (hD.inr_mem_hexagonIndices i) hx
    · rw [restrict_wall, restrict_wall, hD.hexagonDiagram_label_eq_one x'.property]
      exact Commute.one_right _
  · rw [hD.hexagonDiagram_label_eq_one hb]
    exact Commute.one_right _

/-- The hexagon diagram is an outgoing completion of `D`: its walls indexed by the walls of `D` are
the walls of `D`, its two remaining walls are outgoing, and it is consistent. -/
theorem isOutgoingCompletion_hexagonDiagram [HasUniqueDiv Γ] :
    IsOutgoingCompletion D.wall hD.hexagonDiagram where
  wall_inl := hD.hexagonDiagram_wall_inl
  outgoing_inr i := by
    rw [hexagonDiagram_wall_inr]
    fin_cases i
    · simpa using hD.addWall_outgoing
    · simpa using hD.addTwoWall_outgoing
  consistent := hD.hexagonDiagram_consistent

/-- **The scattering diagram of type `B₂`.** For a ray presentation of type `B₂` with arbitrary
coefficients `c₁, c₂`, the outgoing scattering class of `D` is the class of the hexagon diagram,
with the two additional outgoing walls `{μ₁ + μ₂ = 0, μ₁ ≥ 0}` and `{μ₁ + 2 μ₂ = 0, μ₁ ≥ 0}`
labelled by the labels of `(1 + c₁ c₂ z^{n₁ + n₂})^2` and `1 + c₁ c₂^2 z^{n₁ + 2 n₂}`. -/
theorem scat_eq_toClass_hexagonDiagram [Module.Free ℤ Γ] :
    D.Scat hD.full = hD.hexagonDiagram.toClass :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  scat_eq_toClass _ _ hD.isOutgoingCompletion_hexagonDiagram

section Positive

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid Γ) [Fact (d.monoid ≤ Q)]
  {M : Type*} [AddCommGroup M] (π : Γ →+ M) [Module.Free ℤ Γ]
  {S : Type*} [Semiring S] (φ : S →+* R)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- **Positivity of ray presentations of type `B₂` with a positive grouping of `D`.** Let `G` be a
grouping of the walls of `D` into function walls for the projection `π`, positive for the image
of `S[Q]`. If the products `c₁ c₂` and `c₁ c₂^2` lie in the image of a semiring map
`φ : S →+* R`, and the coefficient monoid `Q` contains exponents `p, p'` with `-p, -p' ∈ Q`,
`(μ₁ + μ₂)(ρ p) = 1` and `(μ₁ + 2 μ₂)(ρ p') = 1`, the outgoing scattering class of `D` has a
consistent outgoing representative, the hexagon diagram, which is a positive wall representative
for the image of `S[Q]`. -/
theorem exists_isPositiveWallRepresentative_scat_of_isPositive (hc : c₁ * c₂ ∈ φ.rangeS)
    (hc' : c₁ * c₂ ^ 2 ∈ φ.rangeS) (hQ : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + μ j₂) (ρ p) = 1)
    (hQ' : ∃ p ∈ Q, -p ∈ Q ∧ (μ j₁ + 2 • μ j₂) (ρ p) = 1) {κ' : Type*}
    {G : D.FunctionWallGrouping π κ'}
    (hG : G.IsPositive ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS) :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H
        ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ κ)),
      IsOutgoingCompletion D.wall E ∧ E.toClass = D.Scat hD.full ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS π :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  ⟨Fin 2, hD.hexagonDiagram, hD.isOutgoingCompletion_hexagonDiagram,
    hD.scat_eq_toClass_hexagonDiagram.symm,
    hD.isPositiveWallRepresentative_hexagonDiagram_of_isPositive Q π φ hc hc' hQ hQ' hG⟩

/-- **Positivity of ray presentations of type `B₂`.** If the coefficients `c₁, c₂` lie in the
image of a semiring map `φ : S →+* R`, and the coefficient monoid `Q` contains exponents `p₁, p₂`
with `-p₁, -p₂ ∈ Q`, `μ₁(ρ p₁) = 1`, `μ₂(ρ p₁) = 0` and `μ₂(ρ p₂) = 1`, the outgoing scattering
class of `D` has a consistent outgoing representative, the hexagon diagram, whose grouped wall
functions `1 + c₁ z^{n₁}`, `(1 + c₂ z^{n₂})^2`, `(1 + c₁ c₂ z^{n₁ + n₂})^2`,
`1 + c₁ c₂^2 z^{n₁ + 2 n₂}` (and `1` on the remaining walls) are positive for the image of
`S[Q]`, for every projection `π` of the monomial directions. -/
theorem exists_isPositiveWallRepresentative_scat (hc₁ : c₁ ∈ φ.rangeS) (hc₂ : c₂ ∈ φ.rangeS)
    (hQ₁ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₁ (ρ p) = 1 ∧ μ j₂ (ρ p) = 0)
    (hQ₂ : ∃ p ∈ Q, -p ∈ Q ∧ μ j₂ (ρ p) = 1) :
    ∃ (κ : Type) (E : DirectedDiagram (d := d) h H
        ((Σ j, {w : SupportedRay d // μ j (ρ w.generator) = 0}) ⊕ κ)),
      IsOutgoingCompletion D.wall E ∧ E.toClass = D.Scat hD.full ∧
      E.IsPositiveWallRepresentative ((F).completedBCHAction d ℒ) (mapRingHom Q φ).rangeS π :=
  let : HasUniqueDiv Γ := .of_isTorsionFree ℤ Γ
  ⟨Fin 2, hD.hexagonDiagram, hD.isOutgoingCompletion_hexagonDiagram,
    hD.scat_eq_toClass_hexagonDiagram.symm,
    hD.isPositiveWallRepresentative_hexagonDiagram Q π φ hc₁ hc₂ hQ₁ hQ₂⟩

end Positive

end Mei.DirectedDiagram.IsTypeB₂Presentation
