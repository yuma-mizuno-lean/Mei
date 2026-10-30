/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.FocusFocus.Evaluation
public import Mei.Geometry.ScatteringDiagram.FocusFocus.Family

/-!
# Terminal slab resolution for focus-focus rays

At a nonzero point of the slab, one open neighborhood controls all binomial
branches of a fixed incoming exponent. Every possible crossing height has the
sign of that slab point. Thus no singular encounter enters this neighborhood,
and the upper or lower chart is fixed even as the encounter time tends to zero.
The closed branch path then becomes the incoming affine half-line ending on the
slab, independently of its outgoing exponent.

On the two sides of this neighborhood, the actual weighted ray evaluations
have a unique common linear lift through the nodal slab correspondence. Its
formula is the theta monomial times the incoming coefficient map. The statement
allows an arbitrary module of incoming parameters, tangential and stationary
inputs, zero coefficients, torsion and nilpotent smoothing parameters. It is the
terminal-face identity; singular-origin resolution and global gluing are separate.

We use the existing closed branch charts, decorated-fiber weighted evaluations,
their Laurent formulas and `exponentMaps_jointly_injective`. The local slab
interpretation follows Gross–Siebert, *An Invitation to Toric Degenerations*,
§2.2–2.3 (arXiv:0808.2749v2), and Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace Mei.FocusFocus

open Set Mei.NodeAlgebra _root_.LaurentPolynomial

/-- A neighborhood test at the slab point `(0,v)`: all possible binomial
crossing heights have the strict sign of `v`. It is independent of coefficients. -/
def slabTerminalDomain (n b : ℤ) (v : ℝ) : Set (ℝ × ℝ) :=
  ⋂ j : Fin (n.natAbs + 1),
    {Q | 0 < v * (Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n)}

/-- Membership controls every binomial index, including indices whose coefficient
may vanish after a change of coefficient ring or cutoff. -/
@[simp]
theorem mem_slabTerminalDomain (n b : ℤ) (v : ℝ) (Q : ℝ × ℝ) :
    Q ∈ slabTerminalDomain n b v ↔
      ∀ j : Fin (n.natAbs + 1),
        0 < v * (Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n) := by
  simp [slabTerminalDomain]

/-- The terminal domain is an ambient open neighborhood whenever its center is
a regular slab point. -/
theorem isOpen_slabTerminalDomain (n b : ℤ) (v : ℝ) :
    IsOpen (slabTerminalDomain n b v) := by
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const (by fun_prop)

/-- Throughout the neighborhood, no candidate binomial branch hits the singular
origin. No nonvanishing assumption on its decoration is needed. -/
theorem slabTerminalDomain_crossingHeight_ne_zero {n b : ℤ} {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (j : Fin (n.natAbs + 1)) :
    Q.2 - ((b + j.val : ℤ) : ℝ) * Q.1 / n ≠ 0 :=
  right_ne_zero_of_mul ((mem_slabTerminalDomain n b v Q).mp hQ j).ne'

open Classical in
/-- Locally every crossing branch uses the chart selected by the slab point's
sign. The only remaining endpoint condition is the opposite-chamber condition. -/
theorem mem_slabBranchDomain_iff_of_mem_slabTerminalDomain {n b : ℤ} {v : ℝ}
    {Q : ℝ × ℝ} (hQ : Q ∈ slabTerminalDomain n b v)
    (j : Fin (n.natAbs + 1)) (upper : Bool) :
    Q ∈ slabBranchDomain n (b + j.val) upper ↔
      Q.1 / (n : ℝ) < 0 ∧ upper = decide (0 < v) := by
  have hs := (mem_slabTerminalDomain n b v Q).mp hQ j
  rw [mem_slabBranchDomain]
  simp only [Int.cast_add, Int.cast_natCast] at hs ⊢
  rcases mul_pos_iff.mp hs with ⟨hv, hh⟩ | ⟨hv, hh⟩
  all_goals cases upper <;> grind

/-- The closed crossing path at a terminal slab point is the incoming affine
half-line. Its outgoing degree has disappeared because the final segment has
length zero. This includes unchanged-direction crossings. -/
@[simp↓]
theorem slabBranchPath_terminal (n b q : ℤ) (v s : ℝ) (hs : s ≤ 0) :
    slabBranchPath n b q (0, v) s = (-(s * n), v - s * b) := by
  rw [slabBranchPath_apply]
  simp only [zero_div, zero_sub, max_eq_left (neg_nonneg.mpr hs)]
  congr 1
  ring

private theorem slabTerminalDomain_meets_chambers (n b : ℤ) {v : ℝ} (hv : v ≠ 0) :
    ∃ L U : ℝ × ℝ, L ∈ slabTerminalDomain n b v ∧
      U ∈ slabTerminalDomain n b v ∧ L.1 < 0 ∧ 0 < U.1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_slabTerminalDomain n b v)
    (0, v) (by simpa using hv)
  refine ⟨(-ε / 2, v), (ε / 2, v), hball ?_, hball ?_, by linarith, by linarith⟩
  all_goals
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, sub_self, abs_zero]
    rw [max_lt_iff]
    constructor
    · rw [abs_lt]
      constructor <;> linarith
    · exact hε

section Coefficients

variable {R H : Type*} [CommRing R] [AddCommMonoid H] [Module R H]

/-- The terminal-face resolution identity for whole weighted ray sums.
A linear map into the slab node lifts the evaluations at every nearby left and
right endpoint exactly when it is the theta-monomial lift of the incoming
coefficient map. Thus a common linear lift exists and is unique, including for
tangential degrees and the constant incoming section.

There are no endpoint-genericity hypotheses: the explicit open terminal domain
avoids every crossing-height exception uniformly for all incoming parameters. -/
theorem slabTerminal_commonLift_iff (t : R) (n b : ℤ) {v : ℝ} (hv : v ≠ 0)
    (α : H →ₗ[R] R)
    (ℓ : H →ₗ[R] TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    ((∀ Q ∈ slabTerminalDomain n b v, Q.1 < 0 → ∀ a,
        exponentLeftMap (C t * (1 + T 1)) (ℓ a) =
          slabThetaEvaluation t (α a) n b Q) ∧
      (∀ Q ∈ slabTerminalDomain n b v, 0 < Q.1 → ∀ a,
        exponentRightMap (C t * (1 + T 1)) (ℓ a) =
          slabThetaEvaluation t (α a) n b Q)) ↔
      ℓ = (LinearMap.toSpanSingleton R _ (theta t n b)).comp α := by
  have hleft (Q : ℝ × ℝ) (hQ : Q ∈ slabTerminalDomain n b v) (hside : Q.1 < 0)
      (a : H) :=
    slabThetaEvaluation_eq_exponentLeftMap t (α a) n b Q hside
      (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero hQ j)
  have hright (Q : ℝ × ℝ) (hQ : Q ∈ slabTerminalDomain n b v) (hside : 0 < Q.1)
      (a : H) :=
    slabThetaEvaluation_eq_exponentRightMap t (α a) n b Q hside
      (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero hQ j)
  constructor
  · rintro ⟨hL, hU⟩
    obtain ⟨L, U, hLD, hUD, hLside, hUside⟩ := slabTerminalDomain_meets_chambers n b hv
    ext a
    apply exponentMaps_jointly_injective (C t * (1 + T 1))
    apply Prod.ext
    · simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using
        (hL L hLD hLside a).trans (hleft L hLD hLside a)
    · simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using
        (hU U hUD hUside a).trans (hright U hUD hUside a)
  · rintro rfl
    constructor
    · intro Q hQ hside a
      simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using
        (hleft Q hQ hside a).symm
    · intro Q hQ hside a
      simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply] using
        (hright Q hQ hside a).symm

end Coefficients

end Mei.FocusFocus
