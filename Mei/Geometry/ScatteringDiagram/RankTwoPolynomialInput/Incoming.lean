/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Binomial

/-!
# Incoming diagrams of rank-two polynomial inputs

Let `I` be a rank-two polynomial input on positive degree data `(L, P, δ)`, with projection
`π : L → M`, and fix coefficients `c_{j,n}` in a commutative `ℚ`-algebra `R`. The wall function
`f_j = 1 + ∑_n c_{j,n} z^n` of the line `j` is tangent to the cylinder normal `ν_j ∘ π`, so its
logarithm is a completed tangent field and `exp(log(f_j) ∂_{ν_j ∘ π})` is a completed label
(`RankTwoPolynomialInput.initialLabel`). It acts on `z^p` by multiplication by
`f_j^{⟨ν_j, π(p)⟩}` (`RankTwoPolynomialInput.completedBCHAction_initialLabel`). For a line with
a single term `c z^n` it is the binomial label `exp(log(1 + c z^n) ∂_{ν_j ∘ π})`
(`RankTwoPolynomialInput.initialLabel_eq_binomialLabel`).

The logarithm generally has terms on many supported rays of `L`. Its ray presentation has the
commuting labels `exp((log f_j)_w ∂_{ν_j ∘ π})`, the ray factors on the supported primitive rays
`w` of `L` tangent to the cylinder. We place them on the cylinder `{x ∈ L_ℝ | ν_j(π x) = c_j}`
over the affine line, an incoming full affine hyperplane
(`DirectedWall.ofAffineHyperplane`), and obtain the incoming diagram
(`RankTwoPolynomialInput.incomingDiagram`). All logarithmic degrees lie in the monoid generated
by the exponents of `f_j`; hence a ray factor surviving the cutoff `k` lies on a ray of order at
most `k` and belongs to a line with a term of degree at most `k`. Since only finitely many lines
and rays qualify, the diagram is finitely active at every order. The nontrivial ray labels of a
line have generators projecting to positive multiples of its tangent `m_j`, and at each order
the ray labels of a line reassemble the projection of its unsplit label.

The constructions use `PositiveDegrees.rayFactor` and the ray-factor theorems for tangent
polynomials of `Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor`
(`exists_nsmul_eq_nsmul_of_rayFactor_completedLog_ne_one`,
`mem_raysAtOrder_and_exists_degree_le_of_projection_rayFactor_ne_one`,
`hasFiniteSupport_rayFactor_sigma` and
`projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_tangentRayFactor`),
shared with the BLM inputs of `Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming`.
The diagram is the ray presentation `DirectedDiagram.ofHyperplaneRayFactors`. The rank-two
polynomial inputs and their ray presentations follow Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, Definition 2.1, §9.2 and Theorem 9.9
(arXiv:2503.03719v1), and the function-wall convention of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

open TauCeti (PositiveDegrees SupportedRay)

namespace Mei.RankTwoPolynomialInput

open _root_.AddMonoidAlgebra

variable {L M ι R V : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι) [CommRing R]

local notation "ρ" => AddMonoidHom.id L
local notation "χ" j => AddMonoidHom.comp (Int.castAddHom R) (I.wallNormal j)
local notation "T" j => tropicalTangentMonoid d ρ (χ j)
local notation "F" j => TropicalVertexCoefficientAction.filtration (R := R) d (T j)

/-- An exponent of the wall function of `j`, as a tangent degree of its cylinder. -/
def tangentExponent (j : ι) (n : I.exponents j) : T j :=
  ⟨n, (mem_tropicalTangentMonoid _ _ _ _).mpr ⟨I.mem_monoid_of_mem_exponents n.property, by
    simp [I.wallNormal_eq_zero_of_mem_exponents n.property]⟩⟩

/-- A tangent exponent is the original exponent. -/
@[simp]
theorem coe_tangentExponent (j : ι) (n : I.exponents j) :
    (I.tangentExponent (R := R) j n : L) = n := (rfl)

/-- The wall function `f_j = 1 + ∑_n c_{j,n} z^n` in its tangent coefficient algebra. -/
def tangentInitialFunction (c : I.Variable → R) (j : ι) : R[T j] :=
  1 + ∑ n : I.exponents j, single (I.tangentExponent j n) (c ⟨j, n⟩)

/-- The defining sum of the tangent wall function. -/
theorem tangentInitialFunction_def (c : I.Variable → R) (j : ι) :
    I.tangentInitialFunction c j =
      1 + ∑ n : I.exponents j, single (I.tangentExponent j n) (c ⟨j, n⟩) :=
  (rfl)

/-- The completed wall function is congruent to one, since its exponents are nonzero allowed
degrees. -/
theorem toCompletion_tangentInitialFunction_sub_one_mem (c : I.Variable → R)
    (j : ι) : (F j).toCompletion (I.tangentInitialFunction c j) - 1 ∈ (F j).completionIdeal 1 :=
  toCompletion_one_add_sum_single_sub_one_mem d ρ (I.wallNormal j) (I.tangentExponent j)
    (fun n => c ⟨j, n⟩) fun n => I.ne_zero_of_mem_exponents n.property

variable [DecidableEq L] [Algebra ℚ R]

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "H" => tropicalVertexWallSpaces (R := R) d ρ

/-- The unsplit function-wall label `exp(log(f_j) ∂_{ν_j ∘ π})` in the completed tropical
vertex group. -/
def initialLabel (c : I.Variable → R) (j : ι) : d.completedBCHGroup ℒ :=
  d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ j)
    ((F j).completedLog ⟨(F j).toCompletion (I.tangentInitialFunction c j),
      I.toCompletion_tangentInitialFunction_sub_one_mem c j⟩))

/-- The defining logarithmic tangent field of the unsplit label. -/
theorem initialLabel_def (c : I.Variable → R) (j : ι) :
    I.initialLabel c j = d.completedBCHExp ℒ (completedTropicalTangentField d ρ (χ j)
      ((F j).completedLog ⟨(F j).toCompletion (I.tangentInitialFunction c j),
        I.toCompletion_tangentInitialFunction_sub_one_mem c j⟩)) := (rfl)

/-- The unsplit label of a line with the single term `c z^n` is the binomial label
`exp(log(1 + c z^n) ∂_{ν_j ∘ π})`. -/
theorem initialLabel_eq_binomialLabel (c : I.Variable → R) {j : ι} {n : L}
    (hj : I.exponents j = {n}) :
    I.initialLabel c j = binomialLabel d ρ (I.wallNormal j)
      (I.mem_monoid_of_mem_exponents (I.mem_exponents_of_eq_singleton hj))
      (I.ne_zero_of_mem_exponents (I.mem_exponents_of_eq_singleton hj))
      (I.wallNormal_eq_zero_of_mem_exponents (I.mem_exponents_of_eq_singleton hj))
      (c ⟨j, ⟨n, I.mem_exponents_of_eq_singleton hj⟩⟩) := by
  have hf : I.tangentInitialFunction c j = 1 + single (binomialExponent d ρ (I.wallNormal j)
      (I.mem_monoid_of_mem_exponents (I.mem_exponents_of_eq_singleton hj))
      (I.wallNormal_eq_zero_of_mem_exponents (I.mem_exponents_of_eq_singleton hj)))
      (c ⟨j, ⟨n, I.mem_exponents_of_eq_singleton hj⟩⟩) := by
    rw [tangentInitialFunction_def, Fintype.sum_eq_single ⟨n, I.mem_exponents_of_eq_singleton hj⟩
      fun x hx => absurd (Subtype.ext (Finset.mem_singleton.mp (hj ▸ x.property))) hx]
    exact congrArg (fun q => 1 + single q _)
      (Subtype.ext ((coe_tangentExponent ..).trans (coe_binomialExponent ..).symm))
  simp only [initialLabel_def, binomialLabel_def, hf]

/-- Every degree in which the logarithm of the unsplit label has a nonzero coefficient projects
to a positive multiple of the tangent `m_j`: the exponents do, and the logarithmic degrees lie in
the monoid they generate. -/
theorem exists_projection_eq_of_logComponent_initialLabel_ne_zero (c : I.Variable → R) (j : ι)
    {q : L} (hq : d.logComponent ℒ (I.initialLabel c j) q ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ I.projection q = k • I.tangent j :=
  exists_nsmul_eq_of_logComponent_completedLog_ne_zero d ρ (I.wallNormal j) (I.tangentExponent j)
    (fun n => c ⟨j, n⟩) I.projection (I.tangent j)
    (fun n => I.exists_projection_eq_of_mem_exponents n.property)
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hq

/-- Each ray factor is a wall-group label with the cylinder normal. -/
@[simp high]
theorem rayFactor_initialLabel_mem_wallGroup (c : I.Variable → R) (j : ι) (w : SupportedRay d) :
    d.rayFactor ℒ (I.initialLabel c j) w ∈ (H).wallGroup w (I.wallNormal j) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- Nontangent rays have identity labels. -/
@[simp]
theorem rayFactor_initialLabel_eq_one (c : I.Variable → R) (j : ι) {w : SupportedRay d}
    (hw : I.wallNormal j w.generator ≠ 0) : d.rayFactor ℒ (I.initialLabel c j) w = 1 :=
  rayFactor_completedBCHExp_completedTropicalTangentField_eq_one _ _ _ _ hw

/-- The ray factors of a fixed line commute. -/
theorem commute_rayFactor_initialLabel (c : I.Variable → R) (j : ι) (v w : SupportedRay d) :
    Commute (d.rayFactor ℒ (I.initialLabel c j) v) (d.rayFactor ℒ (I.initialLabel c j) w) :=
  (H).commute_of_mem_wallGroup (I.rayFactor_initialLabel_mem_wallGroup c j v)
    (I.rayFactor_initialLabel_mem_wallGroup c j w) one_ne_zero one_ne_zero rfl

/-- A nontrivial ray label of the line `j` has a generator projecting to a positive rational
multiple of the tangent `m_j`. Identity labels carry no direction constraint. -/
theorem rayFactor_initialLabel_projectedDirection (c : I.Variable → R) (j : ι)
    {w : SupportedRay d} (hw : d.rayFactor ℒ (I.initialLabel c j) w ≠ 1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • I.projection w.generator = b • I.tangent j :=
  exists_nsmul_eq_nsmul_of_rayFactor_completedLog_ne_one d ρ (I.wallNormal j)
    (I.tangentExponent j) (fun n => c ⟨j, n⟩) I.projection (I.tangent j)
    (fun n => I.exists_projection_eq_of_mem_exponents n.property)
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hw

/-- The walls are indexed by a line and a supported ray tangent to its cylinder. Coincident
supports from different lines remain distinct. -/
abbrev IncomingIndex : Type _ :=
  Σ j : ι, {w : SupportedRay d // I.wallNormal j w.generator = 0}

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : L →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming diagram of a rank-two polynomial input: the ray factors of the wall function
of each line on the cylinder `{x | ν_j(π x) = c_j}` over it. -/
def incomingDiagram (c : I.Variable → R) : DirectedDiagram (d := d) h (H) I.IncomingIndex :=
  DirectedDiagram.ofHyperplaneRayFactors h I.wallNormal I.wallNormal_ne_zero I.offset
    (I.initialLabel c) (I.rayFactor_initialLabel_mem_wallGroup c) (by
      let := h.free
      let : HasUniqueDiv L := .of_isTorsionFree ℤ _
      exact hasFiniteSupport_rayFactor_sigma d ρ (I.initialLabel c) fun k =>
        (I.finite_nontrivial k).subset fun j ⟨_, hw⟩ => by
          obtain ⟨-, n, hn⟩ :=
            mem_raysAtOrder_and_exists_degree_le_of_projection_rayFactor_ne_one d ρ
              (I.wallNormal j) (I.tangentExponent j) (fun n => c ⟨j, n⟩)
              (I.toCompletion_tangentInitialFunction_sub_one_mem c j) hw
          exact ⟨n, n.property, hn⟩)

variable (c : I.Variable → R)

/-- The wall over a line is cooriented by the cylinder normal `ν_j ∘ π`. -/
@[simp]
theorem incomingDiagram_normal (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).normal = I.wallNormal j.1 := by
  simp [incomingDiagram]

/-- The wall indexed by a tangent supported ray lies on that ray. -/
@[simp]
theorem incomingDiagram_ray (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).ray = j.2.val := by
  simp [incomingDiagram]

/-- The wall over the line `j` is supported on the cylinder `{x | ν_j(π x) = c_j}`. -/
@[simp]
theorem incomingDiagram_support (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).support =
      {x | h.realCharacter (I.wallNormal j.1) x = I.offset j.1} := by
  simp [incomingDiagram]

/-- The wall over the line `j` on the ray `w` carries the ray factor
`exp((log f_j)_w ∂_{ν_j ∘ π})`. -/
@[simp]
theorem incomingDiagram_label (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).label = d.rayFactor ℒ (I.initialLabel c j.1) j.2.val := by
  simp [incomingDiagram]

/-- Every wall is incoming. -/
@[simp]
theorem incomingDiagram_incoming (j : I.IncomingIndex) :
    ((I.incomingDiagram h c).wall j).Incoming := by
  simp [incomingDiagram]

/-- The full-hyperplane condition required for outgoing completion. -/
theorem incomingDiagram_full (j : I.IncomingIndex) :
    ∃ a : ℝ, ((I.incomingDiagram h c).wall j).support =
      {x | h.realCharacter ((I.incomingDiagram h c).wall j).normal x = a} :=
  DirectedDiagram.ofHyperplaneRayFactors_full ..

/-- The incoming diagram is the ray presentation of the unsplit labels on the cylinders over the
lines. -/
theorem isRayFactorPresentation_incomingDiagram :
    (I.incomingDiagram h c).IsRayFactorPresentation (μ := I.wallNormal)
      (fun j => {x | h.realCharacter (I.wallNormal j) x = I.offset j}) (I.initialLabel c) where
  support := I.incomingDiagram_support h c
  normal := I.incomingDiagram_normal h c
  ray := I.incomingDiagram_ray h c
  label := I.incomingDiagram_label h c

/-- At every cutoff, the labels on the tangent rays of the line `i` reassemble the projection of
its unsplit label. The finite set may contain additional rays, whose surviving factors are
retained automatically. -/
theorem projection_initialLabel_eq_noncommProd_incomingDiagram (i : ι) (k : ℕ)
    (s : Finset {w : SupportedRay d // I.wallNormal i w.generator = 0})
    (hs : ∀ w ∈ d.raysAtOrder k, ∀ hw : I.wallNormal i w.generator = 0, ⟨w, hw⟩ ∈ s) :
    TauCeti.CompletedGroup.projection k (I.initialLabel c i) =
      s.noncommProd (fun w => TauCeti.CompletedGroup.projection k
        ((I.incomingDiagram h c).wall ⟨i, w⟩).label)
        (fun v _ w _ _ => by
          simp only [incomingDiagram_label]
          exact (I.commute_rayFactor_initialLabel c i v.val w.val).map _) := by
  let := h.free
  rw [initialLabel_def,
    projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_tangentRayFactor d ρ
      (I.wallNormal i) _ k s hs]
  exact Finset.noncommProd_congr rfl (fun w _ => by rw [incomingDiagram_label, initialLabel_def]) _

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid L) [Fact (d.monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d Q

/-- The wall function `1 + ∑_n c_{j,n} z^n` in the coefficient algebra `R[Q]`. -/
def initialFunction (j : ι) : R[Q] :=
  1 + ∑ n : I.exponents j, single (⟨n, (Fact.out : d.monoid ≤ Q)
    (I.mem_monoid_of_mem_exponents n.property)⟩ : Q) (c ⟨j, n⟩)

omit [DecidableEq L] [Algebra ℚ R] in
/-- Unfold the wall function in the coefficient algebra. -/
theorem initialFunction_def (j : ι) :
    I.initialFunction c Q j = 1 + ∑ n : I.exponents j, single (⟨n, (Fact.out : d.monoid ≤ Q)
      (I.mem_monoid_of_mem_exponents n.property)⟩ : Q) (c ⟨j, n⟩) := (rfl)

omit [DecidableEq L] [Algebra ℚ R] in
/-- The tangent wall function includes as the wall function of the coefficient algebra. -/
theorem tropicalTangentInclusion_tangentInitialFunction (j : ι) :
    tropicalTangentInclusion d ρ (χ j) Q Fact.out (I.tangentInitialFunction c j) =
      I.initialFunction c Q j := by
  simp only [tangentInitialFunction, initialFunction, map_add, map_one, map_sum,
    tropicalTangentInclusion_single, coe_tangentExponent]

/-- The wall function `f_j` as a unit of the completed coefficient algebra. -/
def completedInitialFunction (j : ι) : (G).completionˣ :=
  (isUnit_completedTropicalTangentInclusion d ρ (χ j) Q
    (I.toCompletion_tangentInitialFunction_sub_one_mem c j)).unit

omit [DecidableEq L] [Algebra ℚ R] in
/-- The completed wall function is the completion of the polynomial wall function. -/
@[simp]
theorem coe_completedInitialFunction (j : ι) :
    (I.completedInitialFunction c Q j : (G).completion) =
      (G).toCompletion (I.initialFunction c Q j) := by
  rw [completedInitialFunction, IsUnit.unit_spec, completedTropicalTangentInclusion_toCompletion,
    I.tropicalTangentInclusion_tangentInitialFunction c Q j]

/-- **Wall-function formula.** The unsplit label of the line `j` acts on `z^p` by
multiplication by `f_j^{⟨ν_j, π(p)⟩}`. Negative pairings use inverse unit powers. -/
theorem completedBCHAction_initialLabel (j : ι) (p : Q) (r : R) :
    (G).completedBCHAction d ℒ (I.initialLabel c j) ((G).toCompletion (single p r)) =
      (I.completedInitialFunction c Q j ^ I.wallNormal j p.val : (G).completionˣ) *
        (G).toCompletion (single p r) := by
  exact completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
      d ρ Q (I.wallNormal j) (I.toCompletion_tangentInitialFunction_sub_one_mem c j) p r

end Action

end Mei.RankTwoPolynomialInput
