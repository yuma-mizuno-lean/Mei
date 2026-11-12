/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Sweep
public import Mei.Geometry.Toric.Algebraic.Lattice
public import Mei.Algebra.Order.Field.Ray
public import Mei.LinearAlgebra.Dual.Kernel

/-!
# Two hyperplanes with square-zero coefficients

Let `x₀ ∈ h_{n₀,m₀}` and `x₁ ∈ h_{n₁,m₁}` be elements of directed wall spaces and let
`t₀, t₁` be scalars with `t₀² = t₁² = 0`; for instance `t₀, t₁` generate
`ℚ[t₀, t₁]/(t₀², t₁²)`, acting on the scalar extension of the wall spaces
(`DirectedWallSpaces.baseChange`). The full affine hyperplanes `{m₀ = m₀(θ₀)}` and
`{m₁ = m₁(θ₀)}` through a point `θ₀`, labelled `exp (t₀ x₀)` and `exp (t₁ x₁)`, form the
incoming diagram `SquareZeroPair.input`.

The bracket `t₀ t₁ ⁅x₀, x₁⁆` lies in the wall space of degree `n₀ + n₁` and normal
`μ = m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀` (`SquareZeroPair.bracketNormal`). For `μ ≠ 0`, the wall
`SquareZeroPair.correction` has normal `μ`, label `exp (t₀ t₁ ⁅x₀, x₁⁆)`, and support the
joint of the two hyperplanes swept by `-i(ρ(n₀ + n₁))`; it is outgoing. In the coordinates
`p_j = m_j - m_j(θ₀)` its support is the ray `-ℝ≥0 (α, β)` with `α = m₀(ρ n₁)` and
`β = m₁(ρ n₀)` (`SquareZeroPair.mem_correction_support_iff`). If `ρ(n₀ + n₁) = 0`, then
`μ = 0` and the bracket vanishes.

For `Γ = Λ = ℤ²`, `ρ = id`, `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂`, `m₁ = e₁*` and `θ₀ = 0`, the
bracket normal is `e₁* - e₂*` and the correction wall is the ray `-ℝ≥0 (1, 1)`.

Consistency of the resulting diagram is proved in
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.SquareZero.Consistency`. This is the
first-order scattering of two lines in Gross–Pandharipande–Siebert, *Quivers, curves, and
the tropical vertex*, [arXiv:0902.1260](https://arxiv.org/abs/0902.1260), §1, in the
directed setting of Travis Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), §2.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

open TauCeti (DirectedWallSpaces wallBracketNormal)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (d : PositiveDegrees Γ)
  (H : DirectedWallSpaces ρ ℒ)

/-- Two wall-space coefficients `x₀ ∈ h_{n₀,m₀}` and `x₁ ∈ h_{n₁,m₁}` on supported rays
`w₀, w₁`, with scalars `t₀, t₁` satisfying `t₀² = t₁² = 0`. Together with a point `θ₀`
they determine the incoming hyperplanes `{m₀ = m₀(θ₀)}` and `{m₁ = m₁(θ₀)}` labelled by
`exp (t₀ x₀)` and `exp (t₁ x₁)` (`SquareZeroPair.input`). -/
structure SquareZeroPair where
  /-- The integral normals `m₀, m₁`. -/
  normal : Fin 2 → Λ →+ ℤ
  /-- The normals are nonzero. -/
  normal_ne_zero (j : Fin 2) : normal j ≠ 0
  /-- The supported rays `w₀, w₁`. -/
  ray : Fin 2 → SupportedRay d
  /-- Each normal annihilates the geometric direction of its ray. -/
  normal_ray (j : Fin 2) : normal j (ρ (ray j).generator) = 0
  /-- The degrees `n₀, n₁` of the coefficients. -/
  degree : Fin 2 → Γ
  /-- Each degree is an actual degree of its ray. -/
  degree_mem (j : Fin 2) : degree j ∈ (ray j).rayDegrees
  /-- The coefficients `x₀, x₁`. -/
  coeff : Fin 2 → L
  /-- Each coefficient lies in the wall space of its degree and normal. -/
  coeff_mem (j : Fin 2) : coeff j ∈ H.wall (degree j) (normal j)
  /-- The square-zero scalars `t₀, t₁`. -/
  scalar : Fin 2 → R
  /-- The scalars square to zero. -/
  scalar_mul_self (j : Fin 2) : scalar j * scalar j = 0

namespace SquareZeroPair

variable {d H} (P : SquareZeroPair d H)

/-- The normal of a coefficient annihilates its degree. -/
theorem normal_degree (j : Fin 2) : P.normal j (ρ (P.degree j)) = 0 := by
  obtain ⟨-, a, -, ha⟩ := SupportedRay.mem_rayDegrees.mp (P.degree_mem j)
  rw [ha, map_zsmul, map_zsmul, P.normal_ray j, smul_zero]

/-- The normal `μ = m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀` of the bracket `⁅x₀, x₁⁆`. -/
def bracketNormal : Λ →+ ℤ :=
  wallBracketNormal ρ (P.degree 0) (P.degree 1) (P.normal 0) (P.normal 1)

/-- The correction coefficient `t₀ t₁ ⁅x₀, x₁⁆`. -/
def commutator : L :=
  (P.scalar 0 * P.scalar 1) • ⁅P.coeff 0, P.coeff 1⁆

/-- The correction coefficient lies in the wall space of degree `n₀ + n₁` and normal `μ`. -/
theorem commutator_mem :
    P.commutator ∈ H.wall (P.degree 0 + P.degree 1) P.bracketNormal :=
  Submodule.smul_mem _ _ (H.bracket_mem (P.coeff_mem 0) (P.coeff_mem 1))

/-- The bracket of the two label logarithms is the correction coefficient. -/
theorem lie_smul_coeff :
    ⁅P.scalar 0 • P.coeff 0, P.scalar 1 • P.coeff 1⁆ = P.commutator := by
  rw [smul_lie, lie_smul, smul_smul, commutator]

/-- The correction coefficient commutes with the first label logarithm, as `t₀² = 0`. -/
theorem lie_smul_coeff_zero_commutator :
    ⁅P.scalar 0 • P.coeff 0, P.commutator⁆ = 0 := by
  rw [commutator, smul_lie, lie_smul, smul_smul, ← mul_assoc, P.scalar_mul_self 0, zero_mul,
    zero_smul]

/-- The correction coefficient commutes with the second label logarithm, as `t₁² = 0`. -/
theorem lie_smul_coeff_one_commutator :
    ⁅P.scalar 1 • P.coeff 1, P.commutator⁆ = 0 := by
  rw [commutator, smul_lie, lie_smul, smul_smul, mul_comm (P.scalar 0), ← mul_assoc,
    P.scalar_mul_self 1, zero_mul, zero_smul]

/-- The bracket normal is `m₀(ρ n₁) m₁ - m₁(ρ n₀) m₀`. -/
theorem bracketNormal_eq : P.bracketNormal =
    P.normal 0 (ρ (P.degree 1)) • P.normal 1 - P.normal 1 (ρ (P.degree 0)) • P.normal 0 := by
  ext v
  simp [bracketNormal, wallBracketNormal_apply]

/-- A nonzero bracket normal has a nonzero coefficient `m₀(ρ n₁)` or `m₁(ρ n₀)`. -/
theorem ne_zero_or_ne_zero_of_bracketNormal_ne_zero (hμ : P.bracketNormal ≠ 0) :
    P.normal 0 (ρ (P.degree 1)) ≠ 0 ∨ P.normal 1 (ρ (P.degree 0)) ≠ 0 := by
  by_contra! hαβ
  apply hμ
  rw [bracketNormal_eq, hαβ.1, hαβ.2, zero_smul, zero_smul, sub_zero]

/-- The real numbers `α = m₀(ρ n₁)` and `β = m₁(ρ n₀)`, the values of the two normals on the
geometric direction of `n₀ + n₁`. -/
def rayCoeff : Fin 2 → ℝ :=
  ![(P.normal 0 (ρ (P.degree 1)) : ℝ), (P.normal 1 (ρ (P.degree 0)) : ℝ)]

/-- A nonzero bracket normal has a nonzero coefficient `α` or `β`. -/
theorem rayCoeff_ne_zero_or_ne_zero (hμ : P.bracketNormal ≠ 0) :
    P.rayCoeff 0 ≠ 0 ∨ P.rayCoeff 1 ≠ 0 := by
  simpa [rayCoeff] using P.ne_zero_or_ne_zero_of_bracketNormal_ne_zero hμ

/-- If the bracket normal vanishes, so does the correction coefficient. -/
theorem commutator_eq_zero_of_bracketNormal_eq_zero (hμ : P.bracketNormal = 0) :
    P.commutator = 0 := by
  have hc := P.commutator_mem
  rwa [hμ, H.zero_normal, Submodule.mem_bot] at hc

/-- If the total degree has zero geometric direction, the bracket normal vanishes. -/
theorem bracketNormal_eq_zero_of_direction_eq_zero
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) : P.bracketNormal = 0 := by
  have h₀ := P.normal_degree 0
  have h₁ := P.normal_degree 1
  rw [map_add] at hρ
  have h₀₁ : ρ (P.degree 1) = -ρ (P.degree 0) := eq_neg_of_add_eq_zero_right hρ
  have h₁₀ : P.normal 1 (ρ (P.degree 0)) = 0 := by
    rw [eq_neg_of_add_eq_zero_left hρ, map_neg, h₁, neg_zero]
  have h₀₁' : P.normal 0 (ρ (P.degree 1)) = 0 := by
    rw [h₀₁, map_neg, h₀, neg_zero]
  ext v
  simp [bracketNormal, wallBracketNormal_apply, h₁₀, h₀₁']

/-- If the total degree has zero geometric direction, the correction coefficient vanishes. -/
theorem commutator_eq_zero_of_direction_eq_zero
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) : P.commutator = 0 :=
  P.commutator_eq_zero_of_bracketNormal_eq_zero (P.bracketNormal_eq_zero_of_direction_eq_zero hρ)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i) (θ₀ : V)

/-- The joint `{m₀ = m₀(θ₀)} ∩ {m₁ = m₁(θ₀)}` of the two hyperplanes. -/
def joint : Set V := {z | h.realCharacter (P.normal 0) z = h.realCharacter (P.normal 0) θ₀ ∧
  h.realCharacter (P.normal 1) z = h.realCharacter (P.normal 1) θ₀}

/-- The base point lies on the joint. -/
theorem self_mem_joint : θ₀ ∈ P.joint h θ₀ := ⟨rfl, rfl⟩

/-- The joint is nonempty. -/
theorem joint_nonempty : (P.joint h θ₀).Nonempty := ⟨θ₀, P.self_mem_joint h θ₀⟩

/-- The joint is the affine subspace through `θ₀` with direction `ker ℓ₀ ⊓ ker ℓ₁`. -/
theorem joint_eq_mk' : P.joint h θ₀ = (AffineSubspace.mk' θ₀
    (LinearMap.ker (h.realCharacter (P.normal 0)) ⊓
      LinearMap.ker (h.realCharacter (P.normal 1))) : Set V) := by
  ext z
  simp [joint, AffineSubspace.mem_mk', sub_eq_zero]

/-- The direction of the joint is `ker ℓ₀ ⊓ ker ℓ₁`. -/
theorem direction_affineSpan_joint : (affineSpan ℝ (P.joint h θ₀)).direction =
    LinearMap.ker (h.realCharacter (P.normal 0)) ⊓
      LinearMap.ker (h.realCharacter (P.normal 1)) := by
  rw [joint_eq_mk', AffineSubspace.affineSpan_coe, AffineSubspace.direction_mk']

/-- The coordinate `p_j = m_j - m_j(θ₀)` relative to the base point. -/
def coord (j : Fin 2) (z : V) : ℝ :=
  h.realCharacter (P.normal j) z - h.realCharacter (P.normal j) θ₀

/-- The coordinates are affine along lines. -/
theorem coord_add_smul (j : Fin 2) (z v : V) (σ : ℝ) :
    P.coord h θ₀ j (z + σ • v) = P.coord h θ₀ j z + σ * h.realCharacter (P.normal j) v := by
  simp only [coord, map_add, map_smul, smul_eq_mul]
  ring

/-- The coordinates are affine along lines. -/
theorem coord_sub_smul (j : Fin 2) (z v : V) (σ : ℝ) :
    P.coord h θ₀ j (z - σ • v) = P.coord h θ₀ j z - σ * h.realCharacter (P.normal j) v := by
  simp only [coord, map_sub, map_smul, smul_eq_mul]
  ring

/-- The coordinates are continuous. -/
theorem continuous_coord (j : Fin 2) : Continuous (P.coord h θ₀ j) :=
  let := h.finiteDimensional
  (LinearMap.continuous_of_finiteDimensional _).sub continuous_const

/-- The `j`-th normal takes the value `P.rayCoeff j` on the geometric direction
`i(ρ(n₀ + n₁))` of the correction. -/
theorem realCharacter_normal_direction (j : Fin 2) :
    h.realCharacter (P.normal j) (i (ρ (P.degree 0 + P.degree 1))) = P.rayCoeff j := by
  fin_cases j <;> simp [rayCoeff, h.realCharacter_apply, P.normal_degree]

/-- The real extension of the bracket normal is `α ℓ₁ - β ℓ₀`. -/
theorem realCharacter_bracketNormal_eq : h.realCharacter P.bracketNormal =
    P.rayCoeff 0 • h.realCharacter (P.normal 1) - P.rayCoeff 1 • h.realCharacter (P.normal 0) := by
  ext z
  simp [bracketNormal_eq, rayCoeff, zsmul_eq_mul]

/-- The real extension of the bracket normal is `α ℓ₁ - β ℓ₀`. -/
theorem realCharacter_bracketNormal (z : V) :
    h.realCharacter P.bracketNormal z =
      P.rayCoeff 0 * h.realCharacter (P.normal 1) z -
        P.rayCoeff 1 * h.realCharacter (P.normal 0) z := by
  simp [realCharacter_bracketNormal_eq]

/-- The bracket normal annihilates the geometric direction of the total degree. -/
theorem realCharacter_bracketNormal_direction :
    h.realCharacter P.bracketNormal (i (ρ (P.degree 0 + P.degree 1))) = 0 := by
  rw [realCharacter_bracketNormal, realCharacter_normal_direction,
    realCharacter_normal_direction]
  ring

/-- The geometric direction of the total degree is transverse to the joint. -/
theorem direction_notMem_joint (hμ : P.bracketNormal ≠ 0) :
    i (ρ (P.degree 0 + P.degree 1)) ∉ (affineSpan ℝ (P.joint h θ₀)).direction := by
  rw [direction_affineSpan_joint]
  rintro ⟨h₀, h₁⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, realCharacter_normal_direction] at h₀ h₁
  rcases P.rayCoeff_ne_zero_or_ne_zero hμ with hα | hβ
  exacts [hα h₀, hβ h₁]

/-- The kernel of the bracket normal is spanned by the joint direction and `i(ρ(n₀ + n₁))`. -/
theorem ker_realCharacter_bracketNormal (hμ : P.bracketNormal ≠ 0) :
    LinearMap.ker (h.realCharacter P.bracketNormal) =
      (affineSpan ℝ (P.joint h θ₀)).direction ⊔ ℝ ∙ i (ρ (P.degree 0 + P.degree 1)) := by
  have hv := P.direction_notMem_joint h θ₀ hμ
  rw [direction_affineSpan_joint] at hv ⊢
  rw [realCharacter_bracketNormal_eq, ← P.realCharacter_normal_direction h 0,
    ← P.realCharacter_normal_direction h 1, LinearMap.ker_apply_smul_sub_apply_smul _ _ hv]

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The wall-group label `exp (t_j x_j)`. -/
def label (j : Fin 2) : H.wallGroup (P.ray j) (P.normal j) :=
  ⟨d.expToCompletion ℒ (P.scalar j • P.coeff j), H.expToCompletion_mem_wallGroup
    (H.wall_le_raySubmodule _ _ (P.degree_mem j) (Submodule.smul_mem _ _ (P.coeff_mem j)))⟩

/-- The label is the completed exponential of `t_j x_j`. -/
@[simp]
theorem coe_label (j : Fin 2) :
    (P.label j : d.completedBCHGroup ℒ) = d.expToCompletion ℒ (P.scalar j • P.coeff j) :=
  -- `label` is a subtype literal, whose value is this exponential.
  (rfl)

/-- The incoming hyperplane `{m_j = m_j(θ₀)}` labelled by `exp (t_j x_j)`. -/
def hyperplane (j : Fin 2) : DirectedWall (d := d) h H :=
  DirectedWall.ofAffineHyperplane h H (P.normal j) (P.normal_ne_zero j)
    (h.realCharacter (P.normal j) θ₀) (P.ray j) (P.normal_ray j) (P.label j)

/-- The normal of the `j`-th hyperplane is `m_j`. -/
@[simp]
theorem hyperplane_normal (j : Fin 2) : (P.hyperplane h θ₀ j).normal = P.normal j :=
  DirectedWall.ofAffineHyperplane_normal ..

/-- The `j`-th hyperplane is `{m_j = m_j(θ₀)}`. -/
@[simp]
theorem hyperplane_support (j : Fin 2) :
    (P.hyperplane h θ₀ j).support =
      {z | h.realCharacter (P.normal j) z = h.realCharacter (P.normal j) θ₀} :=
  DirectedWall.ofAffineHyperplane_support ..

/-- The `j`-th hyperplane is labelled by `exp (t_j x_j)`. -/
@[simp]
theorem hyperplane_label (j : Fin 2) :
    (P.hyperplane h θ₀ j).label = d.expToCompletion ℒ (P.scalar j • P.coeff j) :=
  DirectedWall.ofAffineHyperplane_label ..

/-- The two incoming hyperplanes through `θ₀`. -/
def input : DirectedDiagram (d := d) h H (Fin 2) :=
  ofFinite (P.hyperplane h θ₀)

/-- The walls of the input are the two hyperplanes. -/
@[simp]
theorem input_wall (j : Fin 2) : (P.input h θ₀).wall j = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

/-- The walls of the input are full affine hyperplanes. -/
theorem input_full (j : Fin 2) : ∃ a : ℝ,
    ((P.input h θ₀).wall j).support =
      {x | h.realCharacter ((P.input h θ₀).wall j).normal x = a} :=
  ⟨_, by rw [input_wall, hyperplane_support, hyperplane_normal]⟩

/-- The joint is the intersection of the two hyperplanes. -/
theorem joint_eq :
    P.joint h θ₀ = (P.hyperplane h θ₀ 0).support ∩ (P.hyperplane h θ₀ 1).support := by
  ext z
  simp only [joint, Set.mem_inter_iff, hyperplane_support, Set.mem_ofPred_eq]

/-- The joint is a rational-normal polyhedron. -/
theorem isRationalNormalPolyhedron_joint : IsRationalNormalPolyhedron h (P.joint h θ₀) := by
  rw [joint_eq]
  exact (P.hyperplane h θ₀ 0).rational_support.inter (P.hyperplane h θ₀ 1).rational_support

section Completion

variable {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
  (hμ : P.bracketNormal ≠ 0)

/-- The outgoing correction wall: the joint swept along `-i(ρ(n₀ + n₁))`, with normal
`μ` and label `exp (t₀ t₁ ⁅x₀, x₁⁆)`. -/
def correction : DirectedWall (d := d) h H :=
  DirectedWall.ofSweep (P.joint h θ₀) (P.joint_nonempty h θ₀)
    (P.isRationalNormalPolyhedron_joint h θ₀)
    w _ hw P.bracketNormal hμ (P.ker_realCharacter_bracketNormal h θ₀ hμ) (-P.commutator)
    (Submodule.neg_mem _ P.commutator_mem)

/-- The correction wall has normal `μ`. -/
@[simp]
theorem correction_normal : (P.correction h θ₀ hw hμ).normal = P.bracketNormal :=
  DirectedWall.ofSweep_normal ..

/-- The correction wall lies on the given supported ray of `n₀ + n₁`. -/
@[simp]
theorem correction_ray : (P.correction h θ₀ hw hμ).ray = w :=
  DirectedWall.ofSweep_ray ..

/-- The correction wall is the joint swept along `-i(ρ(n₀ + n₁))`. -/
@[simp]
theorem correction_support :
    (P.correction h θ₀ hw hμ).support =
      sweep (P.joint h θ₀) (i (ρ (P.degree 0 + P.degree 1))) :=
  DirectedWall.ofSweep_support ..

/-- The correction wall is labelled by `exp (t₀ t₁ ⁅x₀, x₁⁆)`. -/
@[simp]
theorem correction_label :
    (P.correction h θ₀ hw hμ).label = d.expToCompletion ℒ P.commutator := by
  rw [correction, DirectedWall.ofSweep_label, neg_neg]

/-- The correction wall is outgoing. -/
theorem correction_outgoing : (P.correction h θ₀ hw hμ).Outgoing :=
  DirectedWall.ofSweep_outgoing _ _ _ _ _ _ _ _ _ _ _ (P.direction_notMem_joint h θ₀ hμ)

/-- The two incoming hyperplanes together with the outgoing correction wall. -/
def completion : DirectedDiagram (d := d) h H (Fin 2 ⊕ Unit) :=
  ofFinite (Sum.elim (P.hyperplane h θ₀) fun _ => P.correction h θ₀ hw hμ)

/-- The initial walls of the completed diagram are the two hyperplanes. -/
@[simp]
theorem completion_wall_inl (j : Fin 2) :
    (P.completion h θ₀ hw hμ).wall (.inl j) = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

/-- The additional wall of the completed diagram is the correction wall. -/
@[simp]
theorem completion_wall_inr (u : Unit) :
    (P.completion h θ₀ hw hμ).wall (.inr u) = P.correction h θ₀ hw hμ :=
  ofFinite_wall ..


/-- A point lies on the `j`-th hyperplane exactly when its `j`-th coordinate vanishes. -/
theorem mem_hyperplane_support_iff (j : Fin 2) (z : V) :
    z ∈ (P.hyperplane h θ₀ j).support ↔ P.coord h θ₀ j z = 0 := by
  rw [hyperplane_support, Set.mem_ofPred_eq, coord, sub_eq_zero]

/-- In the coordinates `p_j`, the correction wall is the ray `-ℝ≥0 (α, β)`: the points with
`α p₁ - β p₀ = 0` and `α p₀ + β p₁ ≤ 0`. -/
theorem mem_correction_support_iff (z : V) :
    z ∈ (P.correction h θ₀ hw hμ).support ↔
      P.rayCoeff 0 * P.coord h θ₀ 1 z - P.rayCoeff 1 * P.coord h θ₀ 0 z = 0 ∧
        P.rayCoeff 0 * P.coord h θ₀ 0 z + P.rayCoeff 1 * P.coord h θ₀ 1 z ≤ 0 := by
  rw [← exists_nonneg_eq_neg_mul_iff (P.rayCoeff_ne_zero_or_ne_zero hμ), correction_support,
    mem_sweep_iff_exists]
  have hv (j : Fin 2) := P.realCharacter_normal_direction h j
  constructor
  · rintro ⟨x, ⟨hx₀, hx₁⟩, t, ht, rfl⟩
    refine ⟨t, ht, ?_, ?_⟩ <;> simp only [coord, map_sub, map_smul, smul_eq_mul, hv, hx₀, hx₁] <;>
      ring
  · rintro ⟨t, ht, h₀, h₁⟩
    refine ⟨z + t • i (ρ (P.degree 0 + P.degree 1)), ⟨?_, ?_⟩, t, ht, by abel⟩
    · rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, hv]
      simp only [coord] at h₀
      linarith
    · rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul, hv]
      simp only [coord] at h₁
      linarith

end Completion

/-- The two hyperplanes with no additional walls. -/
def inputWithoutCorrection : DirectedDiagram (d := d) h H (Fin 2 ⊕ Empty) :=
  ofFinite (Sum.elim (P.hyperplane h θ₀) Empty.elim)

/-- The walls of `inputWithoutCorrection` are the two hyperplanes. -/
@[simp]
theorem inputWithoutCorrection_wall_inl (j : Fin 2) :
    (P.inputWithoutCorrection h θ₀).wall (.inl j) = P.hyperplane h θ₀ j :=
  ofFinite_wall ..

end SquareZeroPair

end Mei.DirectedDiagram

/-! ### The coordinate example

For `Γ = Λ = ℤ²`, `ρ = id`, `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the two input
walls are the coordinate axes through the origin, the bracket normal is `e₁* - e₂*`, and the
correction wall is the ray `-ℝ≥0 (1, 1)`. -/

namespace Mei.DirectedDiagram.SquareZeroPair

variable {R L : Type*} [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  {ℒ : ℤ × ℤ → Submodule R L} {d : PositiveDegrees (ℤ × ℤ)}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {H : DirectedWallSpaces (AddMonoidHom.id (ℤ × ℤ)) ℒ}
  (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {P : SquareZeroPair d H} (hn₀ : P.degree 0 = (1, 0)) (hm₀ : P.normal 0 = AddMonoidHom.snd ℤ ℤ)
  (hn₁ : P.degree 1 = (0, 1)) (hm₁ : P.normal 1 = AddMonoidHom.fst ℤ ℤ)

include hn₀ hm₀ hn₁ hm₁

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] in
/-- For `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the bracket normal is `e₁* - e₂*`. -/
theorem bracketNormal_eq_fst_sub_snd :
    P.bracketNormal = AddMonoidHom.fst ℤ ℤ - AddMonoidHom.snd ℤ ℤ := by
  rw [bracketNormal_eq, hn₀, hn₁, hm₀, hm₁]
  simp

/-- For `n₀ = e₁`, `m₀ = e₂*`, `n₁ = e₂` and `m₁ = e₁*`, the correction wall through the
origin is the ray `-ℝ≥0 (1, 1)`. -/
theorem correction_support_eq {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
    (hμ : P.bracketNormal ≠ 0) :
    (P.correction h 0 hw hμ).support = {z | ∃ t : ℝ, 0 ≤ t ∧ z = -(t • ((1 : ℝ), (1 : ℝ)))} := by
  ext z
  rw [mem_correction_support_iff]
  simp only [rayCoeff, coord, hn₀, hn₁, hm₀, hm₁, TauCeti.Toric.IsIntegralLattice.realCharacter_fst,
    TauCeti.Toric.IsIntegralLattice.realCharacter_snd]
  simp only [AddMonoidHom.id_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
    LinearMap.coe_fst, LinearMap.coe_snd, Prod.fst_zero, Prod.snd_zero, sub_zero, Int.cast_one,
    one_mul, Prod.smul_mk, smul_eq_mul, mul_one, Prod.neg_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨-z.1, by linarith, Prod.ext (by simp) (by simp; linarith)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by ring, by linarith⟩

end Mei.DirectedDiagram.SquareZeroPair
