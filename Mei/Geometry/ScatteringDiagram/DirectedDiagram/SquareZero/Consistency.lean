/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.SquareZero.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalProduct
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat
public import Mei.Algebra.Lie.BCH.Commutator
public import Mei.Algebra.Order.Sign
public import Mei.Topology.Order.Sign

/-!
# Consistency of local scattering with square-zero coefficients

The two incoming hyperplanes of a `SquareZeroPair`, labelled `exp (t₀ x₀)` and
`exp (t₁ x₁)` with `t₀² = t₁² = 0`, together with the outgoing correction wall
`exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal `μ ≠ 0`, form a diagram that is consistent at every finite
order `k` (`SquareZeroPair.levelConsistent_completion`), hence consistent
(`SquareZeroPair.consistent_completion`). It is an outgoing completion of the two hyperplanes
(`SquareZeroPair.isOutgoingCompletion_completion`) and represents their scattering class
(`SquareZeroPair.scat_input_eq_toClass_completion`).

If `μ = 0`, in particular if the total degree has zero geometric direction, the two
hyperplanes alone form an outgoing completion of themselves
(`SquareZeroPair.isOutgoingCompletion_inputWithoutCorrection`) and represent their scattering
class (`SquareZeroPair.scat_input_eq_toClass_of_bracketNormal_eq_zero` and
`SquareZeroPair.scat_input_eq_toClass_of_direction_eq_zero`).

This is the first-order scattering of two lines in Gross–Pandharipande–Siebert, *Quivers,
curves, and the tropical vertex*, [arXiv:0902.1260](https://arxiv.org/abs/0902.1260), §1,
and an instance of the existence and uniqueness of outgoing completions in Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), Theorem 2.6.
-/

public section

open TauCeti (singularSupport affineSpan_eq_of_notMem_singularSupport)

open TauCeti (PositiveDegrees IsPositiveGrading SupportedRay)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (d : PositiveDegrees Γ)
  (H : DirectedWallSpaces ρ ℒ)

section LocalPotential

/-! ### Integer exponents and normal forms -/

open SignType

/-- `1` on the positive side of zero and `0` elsewhere. -/
private def side (x : ℝ) : ℤ := if 0 < x then 1 else 0

/-- The exponent of a label crossed with normal velocity `x`: positive crossings invert it. -/
private def crossSign (x : ℝ) : ℤ := if 0 < x then -1 else 1

/-- The correction exponent of the local potential at a point with coordinates `p` (first
hyperplane) and `q` (bracket normal), for the ray direction with first coordinate `α`: the
signed indicator of an open sector bounded by the correction ray and half of the first
hyperplane. Like `side`, it depends only on the signs of its arguments. -/
private def corner (α p q : ℝ) : ℤ :=
  if 0 ≤ α then side (-p) * side q else -(side p * side (-q))

private theorem side_eq (x : ℝ) : side x = if sign x = 1 then 1 else 0 := by
  simp only [side, sign_eq_one_iff]

private theorem crossSign_eq (x : ℝ) : crossSign x = if sign x = 1 then -1 else 1 := by
  simp only [crossSign, sign_eq_one_iff]

private theorem corner_eq (α p q : ℝ) : corner α p q =
    if sign α = -1 then -((if sign p = 1 then 1 else 0) * (if -sign q = 1 then 1 else 0))
    else (if -sign p = 1 then 1 else 0) * (if sign q = 1 then 1 else 0) := by
  simp only [corner, side_eq, ← Left.sign_neg, sign_eq_neg_one_iff, ← not_le]
  split_ifs <;> simp_all

private theorem crossSign_mul {σ x : ℝ} (hσ : 0 < σ) : crossSign (σ * x) = crossSign x := by
  simp only [crossSign, mul_pos_iff_of_pos_left hσ]

/-- The jump of a side across a hyperplane, for a small transverse perturbation. -/
private theorem side_sub_sub_side {P e : ℝ} (h : P ≠ 0 → |e| < |P|) (he : P = 0 → e ≠ 0) :
    side (P - e) - side (P + e) = if P = 0 then crossSign e else 0 := by
  rcases eq_or_ne P 0 with rfl | hP
  · rw [ite_eq_left rfl, zero_sub, zero_add, side_eq, side_eq, Left.sign_neg, crossSign_eq]
    have he := sign_ne_zero.mpr (he rfl)
    generalize sign e = x at *
    revert x
    decide
  · rw [ite_eq_right hP, side_eq, side_eq, sign_sub_of_abs_lt (h hP), sign_add_of_abs_lt (h hP),
      sub_self]

/-- Off the joint, a small perturbation keeps the side of one of the two hyperplanes. -/
private theorem side_add_eq_side_sub_or {P0 P1 a b : ℝ} (hreg : P0 = 0 → P1 ≠ 0)
    (h0 : P0 ≠ 0 → |a| < |P0|) (h1 : P1 ≠ 0 → |b| < |P1|) :
    side (P0 + a) = side (P0 - a) ∨ side (P1 + b) = side (P1 - b) := by
  rcases eq_or_ne P0 0 with hP0 | hP0
  · right
    rw [side_eq, side_eq, sign_add_of_abs_lt (h1 (hreg hP0)), sign_sub_of_abs_lt (h1 (hreg hP0))]
  · left
    rw [side_eq, side_eq, sign_add_of_abs_lt (h0 hP0), sign_sub_of_abs_lt (h0 hP0)]

/-! #### The jump of the correction exponent -/

/-- The jump of the correction exponent, corrected by the commutator of the hyperplane
labels. At a point with coordinates `(P0, P1)` and a small transverse perturbation `(a, b)`,
write `Q = α P1 - β P0` and `e = α b - β a` for the values of the bracket normal; the
correction ray is `{Q = 0, α P0 + β P1 ≤ 0}`. This is the change of the correction exponent
across the perturbation, together with the commutator `side (P1 + b) • (jump of s)` produced by
moving `exp (s • a)` past `exp (r • b)`; it equals `rayJump`. Both are functions of the signs
of the coordinates and of the perturbation, and a small perturbation does not change the signs
of the nonzero coordinates. -/
private def cornerJump (α P0 P1 Q a b e : ℝ) : ℤ :=
  side (P1 + b) * (side (P0 - a) - side (P0 + a)) +
    (corner α (P0 - a) (Q - e) - corner α (P0 + a) (Q + e))

/-- The exponent of the correction label crossed at the point. -/
private def rayJump (α β P0 P1 Q e : ℝ) : ℤ :=
  if Q = 0 ∧ α * P0 + β * P1 ≤ 0 then crossSign e else 0

private theorem rayJump_eq (α β P0 P1 Q e : ℝ) : rayJump α β P0 P1 Q e =
    if sign Q = 0 ∧ sign (α * P0 + β * P1) ≠ 1 then (if sign e = 1 then -1 else 1) else 0 := by
  simp only [rayJump, crossSign_eq, sign_eq_zero_iff, Ne, sign_eq_one_iff, not_lt]

/-- On the first hyperplane, when the correction ray lies in it (`α = 0`): crossing the
hyperplane on the ray side `β P1 < 0` also crosses the correction wall. -/
private theorem cornerJump_of_eq_zero_of_eq_zero {β P1 b a : ℝ} (hβ : β ≠ 0) (hP1 : P1 ≠ 0)
    (h1 : |b| < |P1|) (ha : a ≠ 0) :
    cornerJump 0 0 P1 (0 * P1 - β * 0) a b (0 * b - β * a) =
      rayJump 0 β 0 P1 (0 * P1 - β * 0) (0 * b - β * a) := by
  rw [cornerJump, rayJump_eq, corner_eq, corner_eq, side_eq, side_eq, side_eq,
    sign_add_of_abs_lt h1]
  simp only [zero_mul, mul_zero, sub_zero, zero_sub, zero_add, neg_neg, Left.sign_neg, sign_mul,
    sign_zero, sub_neg_eq_add]
  rw [← sign_ne_zero] at hβ hP1 ha
  generalize sign β = x at *
  generalize sign P1 = y at *
  generalize sign a = z at *
  revert x y z
  decide

/-- On the first hyperplane, off the correction ray (`α ≠ 0`): the sector indicator jumps
exactly by the commutator term. -/
private theorem cornerJump_of_eq_zero_of_ne_zero {α β P1 b a e : ℝ} (hα : α ≠ 0) (hP1 : P1 ≠ 0)
    (h1 : |b| < |P1|) (hq : |e| < |α * P1 - β * 0|) (ha : a ≠ 0) :
    cornerJump α 0 P1 (α * P1 - β * 0) a b e = rayJump α β 0 P1 (α * P1 - β * 0) e := by
  rw [cornerJump, rayJump_eq, corner_eq, corner_eq, side_eq, side_eq, side_eq,
    sign_add_of_abs_lt h1, sign_sub_of_abs_lt hq, sign_add_of_abs_lt hq]
  simp only [mul_zero, sub_zero, zero_sub, zero_add, Left.sign_neg, sign_mul]
  rw [← sign_ne_zero] at hα hP1 ha
  generalize sign α = x at *
  generalize sign P1 = y at *
  generalize sign a = z at *
  generalize sign β = w at *
  generalize sign e = u at *
  revert x y z w u
  decide

/-- Off the first hyperplane, on the line `{Q = 0}` of the correction: the point lies on the
correction ray exactly when `α P0 < 0`, where the sector indicator jumps by the crossing
exponent of the correction. -/
private theorem cornerJump_of_ne_zero_of_eq_zero {α β P0 P1 b a e : ℝ} (hα : α ≠ 0)
    (hP0 : P0 ≠ 0) (h0 : |a| < |P0|) (hQ : α * P1 - β * P0 = 0)
    (hdq : α * P0 + β * P1 ≤ 0 → e ≠ 0) :
    cornerJump α P0 P1 (α * P1 - β * P0) a b e = rayJump α β P0 P1 (α * P1 - β * P0) e := by
  have hS := sign_mul_add_mul_of_mul_sub_mul_eq_zero hα hQ
  have hdq' : sign (α * P0 + β * P1) ≠ 1 → sign e ≠ 0 := by
    rw [Ne, sign_eq_one_iff, not_lt, Ne, sign_eq_zero_iff]
    exact hdq
  rw [cornerJump, rayJump_eq, corner_eq, corner_eq, side_eq, side_eq, side_eq,
    sign_sub_of_abs_lt h0, sign_add_of_abs_lt h0, hQ, zero_sub, zero_add, Left.sign_neg,
    sign_zero, hS]
  rw [hS] at hdq'
  rw [← sign_ne_zero] at hα hP0
  clear hS hdq hQ h0
  generalize sign α = x at *
  generalize sign P0 = y at *
  generalize sign e = z at *
  generalize sign (P1 + b) = w at *
  revert x y z w
  decide

/-- Away from both the first hyperplane and the line `{Q = 0}`, nothing jumps. -/
private theorem cornerJump_of_ne_zero_of_ne_zero {α β P0 P1 Q b a e : ℝ} (h0 : |a| < |P0|)
    (hQ : Q ≠ 0) (hq : |e| < |Q|) :
    cornerJump α P0 P1 Q a b e = rayJump α β P0 P1 Q e := by
  rw [cornerJump, rayJump_eq, corner_eq, corner_eq, side_eq, side_eq, side_eq,
    sign_sub_of_abs_lt h0, sign_add_of_abs_lt h0, sign_sub_of_abs_lt hq, sign_add_of_abs_lt hq]
  rw [← sign_ne_zero] at hQ
  clear h0 hq
  generalize sign α = x at *
  generalize sign P0 = y at *
  generalize sign e = z at *
  generalize sign (P1 + b) = w at *
  generalize sign Q = u at *
  generalize sign (α * P0 + β * P1) = v at *
  revert x y z w u v
  decide

/-- The jump of the correction exponent along a small transverse perturbation, in all cases. -/
private theorem cornerJump_eq_rayJump (α β P0 P1 Q a b e : ℝ) (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hQ : Q = α * P1 - β * P0) (he : e = α * b - β * a)
    (h0 : P0 ≠ 0 → |a| < |P0|) (h1 : P1 ≠ 0 → |b| < |P1|) (hq : Q ≠ 0 → |e| < |Q|)
    (hreg : P0 = 0 → P1 ≠ 0) (ha : P0 = 0 → a ≠ 0)
    (hdq : Q = 0 → α * P0 + β * P1 ≤ 0 → e ≠ 0) :
    cornerJump α P0 P1 Q a b e = rayJump α β P0 P1 Q e := by
  subst hQ
  rcases eq_or_ne P0 0 with rfl | hP0
  · have hP1 := hreg rfl
    rcases eq_or_ne α 0 with rfl | hα
    · subst he
      exact cornerJump_of_eq_zero_of_eq_zero (hαβ.resolve_left (by norm_num)) hP1 (h1 hP1)
        (ha rfl)
    · exact cornerJump_of_eq_zero_of_ne_zero hα hP1 (h1 hP1)
        (hq (by rw [mul_zero, sub_zero]; exact mul_ne_zero hα hP1)) (ha rfl)
  · rcases eq_or_ne (α * P1 - β * P0) 0 with hQ0 | hQ0
    · have hα : α ≠ 0 := by
        rintro rfl
        rw [zero_mul, zero_sub, neg_eq_zero] at hQ0
        exact mul_ne_zero (hαβ.resolve_left (by norm_num)) hP0 hQ0
      exact cornerJump_of_ne_zero_of_eq_zero hα hP0 (h0 hP0) hQ0 (hdq hQ0)
    · exact cornerJump_of_ne_zero_of_ne_zero (h0 hP0) hQ0 (hq hQ0)

/-- Off the correction ray, the correction exponent depends only on the strict signs of
`p` and, when it is nonzero, of `q`. -/
private theorem corner_eq_of_sign_eq {α β P0 P1 P0' Q' : ℝ} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hP0 : P0 ≠ 0) (hW : ¬(α * P1 - β * P0 = 0 ∧ α * P0 + β * P1 ≤ 0))
    (hs : sign P0' = sign P0) (hq : α * P1 - β * P0 ≠ 0 → sign Q' = sign (α * P1 - β * P0)) :
    corner α P0' Q' = corner α P0 (α * P1 - β * P0) := by
  rw [corner_eq, corner_eq, hs]
  rcases eq_or_ne (α * P1 - β * P0) 0 with hQ0 | hQ0
  · have hα : α ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_sub, neg_eq_zero] at hQ0
      exact mul_ne_zero (hαβ.resolve_left (by norm_num)) hP0 hQ0
    -- On the line `{q = 0}` off the ray, `α P0 > 0`, and the sector indicator vanishes.
    have hpos : sign α * sign P0 = 1 := by
      rw [← sign_mul_add_mul_of_mul_sub_mul_eq_zero hα hQ0]
      exact sign_eq_one_iff.mpr (lt_of_not_ge fun hle => hW ⟨hQ0, hle⟩)
    rw [hQ0, sign_zero]
    rw [← sign_ne_zero] at hα hP0
    clear hW hq hs
    generalize sign α = x at *
    generalize sign P0 = y at *
    generalize sign Q' = z at *
    revert x y z
    decide
  · rw [hq hQ0]

variable {M : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing.IsNilpotent M]

/-- The normal form `exp (-r • b) * exp (-s • a) * exp (-u • c)`. For the truncated label
logarithms `a`, `b` and `c = ⁅a, b⁆`, with `s`, `r` the sides of the two hyperplanes and `u` the
correction exponent, its quotients give the transport of the completed diagram. -/
private def potential (a b c : M) (s r u : ℤ) : BCHGroup M :=
  BCHGroup.exp ((-r) • b) * BCHGroup.exp ((-s) • a) * BCHGroup.exp ((-u) • c)

/-- The quotient of two normal forms, after merging the central factors: if `⁅a, c⁆ = 0`, it is
the conjugate of `exp ((s₂ - s₁) • a + (u₂ - u₁) • c)` by `exp ((-r₁) • b)`, followed by
`exp ((r₂ - r₁) • b)`. -/
private theorem potential_mul_inv_eq {a b c : M} (hac : ⁅a, c⁆ = 0) (s₁ r₁ u₁ s₂ r₂ u₂ : ℤ) :
    potential a b c s₁ r₁ u₁ * (potential a b c s₂ r₂ u₂)⁻¹ =
      BCHGroup.exp ((-r₁) • b) * BCHGroup.exp ((s₂ - s₁) • a + (u₂ - u₁) • c) *
        BCHGroup.exp (r₂ • b) := by
  have hca : ⁅c, a⁆ = 0 := by rw [← lie_skew, hac, neg_zero]
  have hinv (n : ℤ) (x : M) : (BCHGroup.exp ((-n) • x))⁻¹ = BCHGroup.exp (n • x) := by
    rw [← BCHGroup.exp_neg, neg_smul, neg_neg]
  -- The central factors merge, and commute past `exp (s₂ • a)`.
  have hcomm : Commute (BCHGroup.exp ((-u₁ + u₂) • c)) (BCHGroup.exp (s₂ • a)) :=
    BCHGroup.commute_exp_of_lie_eq_zero _ _ (by simp [hca])
  simp only [potential, mul_inv_rev, hinv, mul_assoc]
  rw [← mul_assoc (BCHGroup.exp ((-u₁) • c)), BCHGroup.exp_zsmul_mul_exp_zsmul,
    ← mul_assoc (BCHGroup.exp ((-u₁ + u₂) • c)), hcomm.eq, mul_assoc,
    ← mul_assoc (BCHGroup.exp ((-s₁) • a)), BCHGroup.exp_zsmul_mul_exp_zsmul,
    ← mul_assoc (BCHGroup.exp ((-s₁ + s₂) • a)),
    ← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [hac]), neg_add_eq_sub, neg_add_eq_sub]

/-- If `⁅a, b⁆ = c` is central for `a` and `b`, two normal forms differing in only one of the
first two exponents have quotient `exp ((s₂ - s₁) a + (r₂ - r₁) b + (r₁ (s₂ - s₁) + u₂ - u₁) c)`.
The extra multiple of `c` is the commutator of `b ^ r₁` with `a ^ (s₂ - s₁)`. -/
private theorem potential_mul_inv {a b c : M} (hab : ⁅a, b⁆ = c) (hac : ⁅a, c⁆ = 0)
    (hbc : ⁅b, c⁆ = 0) {s₁ r₁ u₁ s₂ r₂ u₂ : ℤ} (h : s₁ = s₂ ∨ r₁ = r₂) :
    potential a b c s₁ r₁ u₁ * (potential a b c s₂ r₂ u₂)⁻¹ =
      BCHGroup.exp ((s₂ - s₁) • a + (r₂ - r₁) • b + (r₁ * (s₂ - s₁) + (u₂ - u₁)) • c) := by
  rw [potential_mul_inv_eq hac]
  rcases h with rfl | rfl
  · -- Only the second exponent changes: everything else is central.
    have hcb : ⁅c, b⁆ = 0 := by rw [← lie_skew, hbc, neg_zero]
    have hcomm : Commute (BCHGroup.exp ((-r₁) • b))
        (BCHGroup.exp ((s₁ - s₁) • a + (u₂ - u₁) • c)) :=
      BCHGroup.commute_exp_of_lie_eq_zero _ _ (by simp [hbc])
    rw [hcomm.eq, mul_assoc, BCHGroup.exp_zsmul_mul_exp_zsmul,
      ← BCHGroup.exp_add_of_lie_eq_zero _ _ (by simp [hcb, sub_self])]
    congr 1
    module
  · -- Only the first exponent changes: conjugate by `exp ((-r₁) • b)`.
    have hba : ⁅b, a⁆ = -c := by rw [← lie_skew, hab]
    have hlie : ⁅(-r₁) • b, (s₂ - s₁) • a + (u₂ - u₁) • c⁆ = (r₁ * (s₂ - s₁)) • c := by
      simp only [zsmul_lie, lie_add, lie_zsmul, hba, hbc, smul_neg, smul_zero, add_zero]
      module
    rw [show r₁ • b = -((-r₁) • b) by rw [neg_smul, neg_neg],
      BCHGroup.exp_mul_exp_mul_exp_neg_of_lie_lie_eq_zero (by rw [hlie]; simp [hbc]), hlie]
    congr 1
    module

end LocalPotential

namespace SquareZeroPair

variable {d H} (P : SquareZeroPair d H)
  [NormedAddCommGroup V] [NormedSpace ℝ V] {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (θ₀ : V) [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] (k : ℕ)

/-! ### Truncated logarithms of the labels -/

/-- The logarithm `t_j x_j` of the `j`-th hyperplane label at order `k`. -/
def labelLog
    (j : Fin 2) : d.lieTruncation ℒ k := (d.truncationIdeal ℒ k).mkQ (P.scalar j • P.coeff j)

/-- The logarithm `t₀ t₁ ⁅x₀, x₁⁆` of the correction label at order `k`. -/
def commutatorLog : d.lieTruncation ℒ k := (d.truncationIdeal ℒ k).mkQ P.commutator

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The bracket of the two label logarithms is the correction logarithm. -/
theorem lie_labelLog : ⁅P.labelLog k 0, P.labelLog k 1⁆ = P.commutatorLog k := by
  rw [labelLog, labelLog, commutatorLog, ← LieHom.map_lie, P.lie_smul_coeff]

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The correction logarithm is central for both label logarithms. -/
theorem lie_labelLog_commutatorLog (j : Fin 2) : ⁅P.labelLog k j, P.commutatorLog k⁆ = 0 := by
  rw [labelLog, commutatorLog, ← LieHom.map_lie]
  fin_cases j
  · rw [Fin.zero_eta, P.lie_smul_coeff_zero_commutator, map_zero]
  · rw [Fin.mk_one, P.lie_smul_coeff_one_commutator, map_zero]

/-- The label exponentials satisfy `exp a * exp b = exp b * exp c * exp a`. -/
theorem exp_labelLog_mul_exp_labelLog :
    BCHGroup.exp (P.labelLog k 0) * BCHGroup.exp (P.labelLog k 1) =
      BCHGroup.exp (P.labelLog k 1) * BCHGroup.exp (P.commutatorLog k) *
        BCHGroup.exp (P.labelLog k 0) := by
  have hbc := P.lie_labelLog_commutatorLog k 1
  exact BCHGroup.exp_mul_exp_eq_exp_mul_exp_mul (P.lie_labelLog k)
    (P.lie_labelLog_commutatorLog k 0) hbc

section Completion

variable {w : SupportedRay d} (hw : P.degree 0 + P.degree 1 ∈ w.rayDegrees)
  (hμ : P.bracketNormal ≠ 0)

/-- The order-`k` projection of a hyperplane label is the exponential of its logarithm. -/
theorem projection_completion_label_inl (j : Fin 2) :
    CompletedGroup.projection k ((P.completion h θ₀ hw hμ).wall (.inl j)).label =
      BCHGroup.exp (P.labelLog k j) := by
  rw [completion_wall_inl, hyperplane_label, PositiveDegrees.projection_expToCompletion,
    labelLog]

/-- The order-`k` projection of the correction label is the exponential of its logarithm. -/
theorem projection_completion_label_inr (u : Unit) :
    CompletedGroup.projection k ((P.completion h θ₀ hw hμ).wall (.inr u)).label =
      BCHGroup.exp (P.commutatorLog k) := by
  rw [completion_wall_inr, correction_label, PositiveDegrees.projection_expToCompletion,
    commutatorLog]

/-- If the correction label vanishes at order `k`, the two hyperplane labels commute, and the
completed diagram is consistent at order `k`. -/
theorem levelConsistent_completion_of_exp_commutatorLog_eq_one
    (hC : BCHGroup.exp (P.commutatorLog k) = 1) :
    (P.completion h θ₀ hw hμ).LevelConsistent k := by
  set D := P.completion h θ₀ hw hμ
  have hcomm : Commute (BCHGroup.exp (P.labelLog k 0)) (BCHGroup.exp (P.labelLog k 1)) := by
    have := P.exp_labelLog_mul_exp_labelLog k
    rwa [hC, mul_one] at this
  have hinl (j : D.active k) : ∃ l : Fin 2, j.1 = .inl l := by
    obtain ⟨j | u, hj⟩ := j
    · exact ⟨j, rfl⟩
    · have h1 : CompletedGroup.projection k (D.wall (.inr u)).label =
          (1 : (d.groupTower ℒ).obj (Opposite.op k)) := by
        rw [P.projection_completion_label_inr, hC]
        exact (d.groupTower_obj_one ℒ k).symm
      exact absurd h1 ((D.mem_active k _).mp hj)
  apply D.levelConsistent_of_commute_of_full k
  · intro j
    obtain ⟨l, hl⟩ := hinl j
    rw [hl, completion_wall_inl, hyperplane_support, hyperplane_normal]
    exact ⟨_, rfl⟩
  · intro j j'
    obtain ⟨l, hl⟩ := hinl j
    obtain ⟨l', hl'⟩ := hinl j'
    rw [hl, hl', P.projection_completion_label_inl, P.projection_completion_label_inl]
    fin_cases l <;> fin_cases l'
    exacts [Commute.refl _, hcomm, hcomm.symm, Commute.refl _]

/-- If the correction label does not vanish at order `k`, every wall is active at order `k`. -/
theorem mem_active_completion (hC : BCHGroup.exp (P.commutatorLog k) ≠ 1)
    (j : Fin 2 ⊕ Unit) : j ∈ (P.completion h θ₀ hw hμ).active k := by
  have hc0 : P.commutatorLog k ≠ 0 := fun h0 => hC (by rw [h0, BCHGroup.exp_zero])
  have hexp_ne {x : d.lieTruncation ℒ k} (hx : x ≠ 0) :
      BCHGroup.exp x ≠ (1 : (d.groupTower ℒ).obj (Opposite.op k)) := by
    rw [d.groupTower_obj_one]
    intro h1
    apply hx
    simpa only [BCHGroup.log_exp, BCHGroup.log_one] using congrArg BCHGroup.log h1
  rw [mem_active]
  rcases j with j | u
  · rw [P.projection_completion_label_inl]
    refine hexp_ne fun h0 => hc0 ?_
    rw [← P.lie_labelLog]
    fin_cases j
    · rw [Fin.zero_eta] at h0
      rw [h0, zero_lie]
    · rw [Fin.mk_one] at h0
      rw [h0, lie_zero]
  · rw [P.projection_completion_label_inr]
    exact hexp_ne hc0

/-! ### Walls through a regular point -/

variable {k} (hC : BCHGroup.exp (P.commutatorLog k) ≠ 1) {θ : V}
  (hθ : θ ∉ singularSupport
    (fun j : (P.completion h θ₀ hw hμ).active k => ((P.completion h θ₀ hw hμ).wall j).support))

include hC hθ in
/-- Two walls through a regular point have the same kernel. -/
theorem ker_eq_of_mem_support {j j' : Fin 2 ⊕ Unit}
    (hj : θ ∈ ((P.completion h θ₀ hw hμ).wall j).support)
    (hj' : θ ∈ ((P.completion h θ₀ hw hμ).wall j').support) :
    LinearMap.ker (h.realCharacter ((P.completion h θ₀ hw hμ).wall j).normal) =
      LinearMap.ker (h.realCharacter ((P.completion h θ₀ hw hμ).wall j').normal) := by
  rw [← DirectedWall.direction_support, ← DirectedWall.direction_support]
  exact congrArg AffineSubspace.direction
    (affineSpan_eq_of_notMem_singularSupport
      (W := fun j : (P.completion h θ₀ hw hμ).active k =>
        ((P.completion h θ₀ hw hμ).wall j).support)
      (i := ⟨j, P.mem_active_completion h θ₀ k hw hμ hC j⟩)
      (j := ⟨j', P.mem_active_completion h θ₀ k hw hμ hC j'⟩) hθ hj hj')

include hC hθ in
/-- If a regular point lies on the `j`-th hyperplane and on the correction wall, the ray of
the correction lies in that hyperplane: `P.rayCoeff j = 0`. -/
theorem rayCoeff_eq_zero_of_mem (j : Fin 2) (hj : P.coord h θ₀ j θ = 0)
    (h2 : θ ∈ (P.correction h θ₀ hw hμ).support) : P.rayCoeff j = 0 := by
  have hk := P.ker_eq_of_mem_support h θ₀ hw hμ hC hθ (j := .inl j) (j' := .inr ())
    (by rwa [completion_wall_inl, mem_hyperplane_support_iff]) (by rwa [completion_wall_inr])
  rw [completion_wall_inl, completion_wall_inr, hyperplane_normal, correction_normal] at hk
  have hv : i (ρ (P.degree 0 + P.degree 1)) ∈ LinearMap.ker (h.realCharacter (P.normal j)) := by
    rw [hk]
    exact P.realCharacter_bracketNormal_direction h
  rwa [LinearMap.mem_ker, P.realCharacter_normal_direction] at hv

include hC hθ in
/-- A regular point does not lie on both hyperplanes. -/
theorem coord_ne_zero_of_coord_eq_zero (h0 : P.coord h θ₀ 0 θ = 0) : P.coord h θ₀ 1 θ ≠ 0 := by
  intro h1
  have h2 : θ ∈ (P.correction h θ₀ hw hμ).support := by
    rw [mem_correction_support_iff, h0, h1]
    constructor <;> simp
  rcases P.rayCoeff_ne_zero_or_ne_zero hμ with hα | hβ
  exacts [hα (P.rayCoeff_eq_zero_of_mem h θ₀ hw hμ hC hθ 0 h0 h2),
    hβ (P.rayCoeff_eq_zero_of_mem h θ₀ hw hμ hC hθ 1 h1 h2)]

/-! ### Wall germs at a regular point -/

variable (k) in
/-- The potential of the completed diagram at order `k`: the transport of every path from `x`
to `y` is `F y * (F x)⁻¹` for `F = exp (-r • t₁ x₁) * exp (-s • t₀ x₀) *
exp (-u • t₀ t₁ ⁅x₀, x₁⁆)`, where `s` and `r` are the sides of the two hyperplanes and `u` is
the signed indicator of a sector bounded by the correction ray. -/
private def localPotential (z : V) : d.truncatedGroup ℒ k :=
  potential (P.labelLog k 0) (P.labelLog k 1) (P.commutatorLog k) (side (P.coord h θ₀ 0 z))
    (side (P.coord h θ₀ 1 z)) (corner (P.rayCoeff 0) (P.coord h θ₀ 0 z)
      (P.rayCoeff 0 * P.coord h θ₀ 1 z - P.rayCoeff 1 * P.coord h θ₀ 0 z))

variable (k) in
/-- Off the walls, the local potential is locally constant. -/
private theorem eventually_localPotential_eq (h₀ : P.coord h θ₀ 0 θ ≠ 0)
    (h₁ : P.coord h θ₀ 1 θ ≠ 0) (h₂ : θ ∉ (P.correction h θ₀ hw hμ).support) :
    ∀ᶠ φ in 𝓝 θ, P.localPotential h θ₀ k φ = P.localPotential h θ₀ k θ := by
  rw [mem_correction_support_iff] at h₂
  set α := P.rayCoeff 0
  set β := P.rayCoeff 1
  have hq : Continuous fun z => α * P.coord h θ₀ 1 z - β * P.coord h θ₀ 0 z :=
    (continuous_const.mul (P.continuous_coord h θ₀ 1)).sub
      (continuous_const.mul (P.continuous_coord h θ₀ 0))
  have evq : ∀ᶠ φ in 𝓝 θ, α * P.coord h θ₀ 1 θ - β * P.coord h θ₀ 0 θ ≠ 0 →
      SignType.sign (α * P.coord h θ₀ 1 φ - β * P.coord h θ₀ 0 φ) =
        SignType.sign (α * P.coord h θ₀ 1 θ - β * P.coord h θ₀ 0 θ) := by
    by_cases hq0 : α * P.coord h θ₀ 1 θ - β * P.coord h θ₀ 0 θ = 0
    · exact Eventually.of_forall fun _ hne => absurd hq0 hne
    · filter_upwards [hq.continuousAt.eventually_sign_eq hq0] with φ hφ _ using hφ
  filter_upwards [(P.continuous_coord h θ₀ 0).continuousAt.eventually_sign_eq h₀,
    (P.continuous_coord h θ₀ 1).continuousAt.eventually_sign_eq h₁, evq] with φ hφ₀ hφ₁ hφq
  rw [localPotential, localPotential, side_eq (P.coord h θ₀ 0 φ), side_eq (P.coord h θ₀ 0 θ), hφ₀,
    side_eq (P.coord h θ₀ 1 φ), side_eq (P.coord h θ₀ 1 θ), hφ₁,
    corner_eq_of_sign_eq (P.rayCoeff_ne_zero_or_ne_zero hμ) h₀ h₂ hφ₀ hφq]

include hC in
/-- The logarithm of a combined label of the completed diagram at a regular point is the signed
sum of the logarithms of the walls through the point. -/
theorem log_combinedLabel_completion (v : V) :
    BCHGroup.log ((P.completion h θ₀ hw hμ).combinedLabel k θ v hθ) =
      ((if P.coord h θ₀ 0 θ = 0 then
          (if 0 < h.realCharacter (P.normal 0) v then -1 else 1 : ℤ) • P.labelLog k 0 else 0) +
        if P.coord h θ₀ 1 θ = 0 then
          (if 0 < h.realCharacter (P.normal 1) v then -1 else 1 : ℤ) • P.labelLog k 1 else 0) +
      if P.rayCoeff 0 * P.coord h θ₀ 1 θ - P.rayCoeff 1 * P.coord h θ₀ 0 θ = 0 ∧
          P.rayCoeff 0 * P.coord h θ₀ 0 θ + P.rayCoeff 1 * P.coord h θ₀ 1 θ ≤ 0 then
        (if 0 < P.rayCoeff 0 * h.realCharacter (P.normal 1) v -
            P.rayCoeff 1 * h.realCharacter (P.normal 0) v then -1 else 1 : ℤ) • P.commutatorLog k
      else 0 := by
  classical
  set D := P.completion h θ₀ hw hμ
  let G : Fin 2 ⊕ Unit → d.lieTruncation ℒ k := fun j =>
    if θ ∈ (D.wall j).support then
      (if 0 < h.realCharacter (D.wall j).normal v then -1 else 1 : ℤ) •
        BCHGroup.log (L := d.lieTruncation ℒ k) (CompletedGroup.projection k (D.wall j).label)
    else 0
  have hsum : BCHGroup.log (D.combinedLabel k θ v hθ) = ∑ j, G j := by
    let := Fintype.ofFinite (D.active k)
    rw [D.log_combinedLabel_eq_sum k θ v hθ]
    -- `Equiv.subtypeUnivEquiv` sends an active index to its underlying index.
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv (P.mem_active_completion h θ₀ k hw hμ hC)) _
      G (fun _ => rfl)
  rw [hsum, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_unique]
  simp only [G, D, P.projection_completion_label_inl, P.projection_completion_label_inr,
    BCHGroup.log_exp]
  simp only [completion_wall_inl, completion_wall_inr, hyperplane_normal, correction_normal,
    mem_hyperplane_support_iff, mem_correction_support_iff, P.realCharacter_bracketNormal]

variable (v : V) (hv : ∀ j : (P.completion h θ₀ hw hμ).active k,
  θ ∈ ((P.completion h θ₀ hw hμ).wall j).support →
    h.realCharacter ((P.completion h θ₀ hw hμ).wall j).normal v ≠ 0)

include hC hv in
/-- A velocity transverse to the walls through `θ` is transverse to each hyperplane through
`θ`. -/
theorem realCharacter_normal_ne_zero_of_coord_eq_zero (j : Fin 2)
    (hj : P.coord h θ₀ j θ = 0) : h.realCharacter (P.normal j) v ≠ 0 := by
  simpa only [completion_wall_inl, hyperplane_normal] using
    hv ⟨_, P.mem_active_completion h θ₀ k hw hμ hC (.inl j)⟩
      (by rwa [completion_wall_inl, mem_hyperplane_support_iff])

include hC hv in
/-- A velocity transverse to the walls through `θ` is transverse to the correction wall when
`θ` lies on it. -/
theorem rayCoeff_mul_sub_ne_zero_of_mem
    (h2 : P.rayCoeff 0 * P.coord h θ₀ 1 θ - P.rayCoeff 1 * P.coord h θ₀ 0 θ = 0)
    (h2' : P.rayCoeff 0 * P.coord h θ₀ 0 θ + P.rayCoeff 1 * P.coord h θ₀ 1 θ ≤ 0) :
    P.rayCoeff 0 * h.realCharacter (P.normal 1) v -
      P.rayCoeff 1 * h.realCharacter (P.normal 0) v ≠ 0 := by
  simpa only [completion_wall_inr, correction_normal, P.realCharacter_bracketNormal] using
    hv ⟨_, P.mem_active_completion h θ₀ k hw hμ hC (.inr ())⟩
      (by rw [completion_wall_inr, mem_correction_support_iff]; exact ⟨h2, h2'⟩)

include hC hv in
/-- At a regular wall germ, the local potential jumps by the combined label. -/
private theorem eventually_localPotential_mul_inv :
    ∀ᶠ σ in 𝓝[>] (0 : ℝ), P.localPotential h θ₀ k (θ + σ • v) *
      (P.localPotential h θ₀ k (θ - σ • v))⁻¹ =
        (P.completion h θ₀ hw hμ).combinedLabel k θ v hθ := by
  set α := P.rayCoeff 0 with hα_def
  set β := P.rayCoeff 1 with hβ_def
  set ℓ₀ := h.realCharacter (P.normal 0) with hℓ₀_def
  set ℓ₁ := h.realCharacter (P.normal 1) with hℓ₁_def
  set p₀ := P.coord h θ₀ 0 θ with hp₀_def
  set p₁ := P.coord h θ₀ 1 θ with hp₁_def
  have hreg := P.coord_ne_zero_of_coord_eq_zero h θ₀ hw hμ hC hθ
  have ht := P.realCharacter_normal_ne_zero_of_coord_eq_zero h θ₀ hw hμ hC v hv
  have ht₂ := P.rayCoeff_mul_sub_ne_zero_of_mem h θ₀ hw hμ hC v hv
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_imp_abs_mul_lt p₀ (ℓ₀ v),
    eventually_nhdsGT_imp_abs_mul_lt p₁ (ℓ₁ v),
    eventually_nhdsGT_imp_abs_mul_lt (α * p₁ - β * p₀) (α * ℓ₁ v - β * ℓ₀ v)]
    with σ hσ hs₀ hs₁ hsq
  have hσ : 0 < σ := hσ
  have hne {x : ℝ} (hx : x ≠ 0) : σ * x ≠ 0 := mul_ne_zero hσ.ne' hx
  rw [localPotential, localPotential, P.coord_add_smul, P.coord_sub_smul, P.coord_add_smul,
    P.coord_sub_smul,
    show α * (p₁ + σ * ℓ₁ v) - β * (p₀ + σ * ℓ₀ v) =
      (α * p₁ - β * p₀) + σ * (α * ℓ₁ v - β * ℓ₀ v) by ring,
    show α * (p₁ - σ * ℓ₁ v) - β * (p₀ - σ * ℓ₀ v) =
      (α * p₁ - β * p₀) - σ * (α * ℓ₁ v - β * ℓ₀ v) by ring,
    potential_mul_inv (P.lie_labelLog k) (P.lie_labelLog_commutatorLog k 0)
      (P.lie_labelLog_commutatorLog k 1) (side_add_eq_side_sub_or hreg hs₀ hs₁)]
  -- Compare logarithms: the three integer coefficients are the jumps of the potential.
  apply BCHGroup.log_injective
  rw [BCHGroup.log_exp, P.log_combinedLabel_completion h θ₀ hw hμ hC hθ v]
  have hjump := cornerJump_eq_rayJump α β p₀ p₁ _ (σ * ℓ₀ v) (σ * ℓ₁ v)
    (σ * (α * ℓ₁ v - β * ℓ₀ v)) (P.rayCoeff_ne_zero_or_ne_zero hμ) rfl (by ring) hs₀ hs₁ hsq hreg
    (fun h0 => hne (ht 0 h0)) (fun h2 h2' => hne (ht₂ h2 h2'))
  rw [cornerJump, rayJump] at hjump
  rw [hjump, side_sub_sub_side hs₀ (fun h0 => hne (ht 0 h0)),
    side_sub_sub_side hs₁ (fun h1 => hne (ht 1 h1)),
    crossSign_mul hσ, crossSign_mul hσ, crossSign_mul hσ]
  simp only [crossSign, ite_smul, zero_smul, ← hℓ₀_def, ← hℓ₁_def, ← hα_def, ← hβ_def,
    ← hp₀_def, ← hp₁_def]

variable (k) in
/-- The completed diagram is consistent at order `k`. -/
theorem levelConsistent_completion : (P.completion h θ₀ hw hμ).LevelConsistent k := by
  by_cases hC : BCHGroup.exp (P.commutatorLog k) = 1
  · exact P.levelConsistent_completion_of_exp_commutatorLog_eq_one h θ₀ k hw hμ hC
  have hall := P.mem_active_completion h θ₀ k hw hμ hC
  refine (P.completion h θ₀ hw hμ).levelConsistent_of_local k
    (F := P.localPotential h θ₀ k) (fun θ hθ => ?_)
    (fun θ hθ v hv => P.eventually_localPotential_mul_inv h θ₀ hw hμ hC hθ v hv)
  have hoff (j : Fin 2 ⊕ Unit) : θ ∉ ((P.completion h θ₀ hw hμ).wall j).support :=
    hθ ⟨j, hall j⟩
  refine P.eventually_localPotential_eq h θ₀ k hw hμ (fun h0 => hoff (.inl 0) ?_)
    (fun h1 => hoff (.inl 1) ?_) (fun h2 => hoff (.inr ()) ?_)
  · rwa [completion_wall_inl, mem_hyperplane_support_iff]
  · rwa [completion_wall_inl, mem_hyperplane_support_iff]
  · rwa [completion_wall_inr]

/-- The two hyperplanes together with the correction wall form a consistent diagram. -/
theorem consistent_completion : (P.completion h θ₀ hw hμ).Consistent :=
  (consistent_iff _).mpr fun k => P.levelConsistent_completion h θ₀ k hw hμ

/-- **Local scattering with square-zero coefficients.** For a nonzero bracket normal `μ`, the
outgoing completion of the hyperplanes `{m₀ = m₀(θ₀)}` and `{m₁ = m₁(θ₀)}` labelled by
`exp (t₀ x₀)` and `exp (t₁ x₁)` adds the single wall `exp (t₀ t₁ ⁅x₀, x₁⁆)` with normal `μ`,
supported on the joint swept by `-i(ρ(n₀ + n₁))`. -/
theorem isOutgoingCompletion_completion :
    IsOutgoingCompletion (P.input h θ₀).wall (P.completion h θ₀ hw hμ) where
  wall_inl j := by rw [completion_wall_inl, input_wall]
  outgoing_inr u := by
    rw [completion_wall_inr]
    exact P.correction_outgoing h θ₀ hw hμ
  consistent := P.consistent_completion h θ₀ hw hμ

/-- The scattering class of the two hyperplanes is represented by the diagram with the single
correction wall. -/
theorem scat_input_eq_toClass_completion [Module.Free ℤ Γ] :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.completion h θ₀ hw hμ).toClass :=
  scat_eq_toClass _ _ (P.isOutgoingCompletion_completion h θ₀ hw hμ)

end Completion

section Trivial

/-- If the bracket normal vanishes, the two hyperplanes form a consistent diagram with no
further walls. -/
theorem isOutgoingCompletion_inputWithoutCorrection (hμ : P.bracketNormal = 0) :
    IsOutgoingCompletion (P.input h θ₀).wall (P.inputWithoutCorrection h θ₀) where
  wall_inl j := by rw [inputWithoutCorrection_wall_inl, input_wall]
  outgoing_inr u := u.elim
  consistent := by
    have hcomm : Commute (d.expToCompletion ℒ (P.scalar 0 • P.coeff 0))
        (d.expToCompletion ℒ (P.scalar 1 • P.coeff 1)) :=
      d.commute_expToCompletion_of_lie_eq_zero ℒ
        (by rw [P.lie_smul_coeff, P.commutator_eq_zero_of_bracketNormal_eq_zero hμ])
    apply consistent_of_commute_of_full
    · rintro (j | u)
      · rw [inputWithoutCorrection_wall_inl, hyperplane_support, hyperplane_normal]
        exact ⟨_, rfl⟩
      · exact u.elim
    · rintro (j | u) (j' | u')
      · rw [inputWithoutCorrection_wall_inl, inputWithoutCorrection_wall_inl, hyperplane_label,
          hyperplane_label]
        fin_cases j <;> fin_cases j'
        exacts [Commute.refl _, hcomm, hcomm.symm, Commute.refl _]
      all_goals first | exact u.elim | exact u'.elim

/-- If the bracket normal vanishes, the scattering class of the two hyperplanes is that of the
hyperplanes alone. -/
theorem scat_input_eq_toClass_of_bracketNormal_eq_zero [Module.Free ℤ Γ]
    (hμ : P.bracketNormal = 0) :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.inputWithoutCorrection h θ₀).toClass :=
  scat_eq_toClass _ _ (P.isOutgoingCompletion_inputWithoutCorrection h θ₀ hμ)

/-- If the total degree has zero geometric direction, the scattering class of the two
hyperplanes is that of the hyperplanes alone. -/
theorem scat_input_eq_toClass_of_direction_eq_zero [Module.Free ℤ Γ]
    (hρ : ρ (P.degree 0 + P.degree 1) = 0) :
    (P.input h θ₀).Scat (P.input_full h θ₀) = (P.inputWithoutCorrection h θ₀).toClass :=
  P.scat_input_eq_toClass_of_bracketNormal_eq_zero h θ₀
    (P.bracketNormal_eq_zero_of_direction_eq_zero hρ)

end Trivial

end SquareZeroPair

end Mei.DirectedDiagram
