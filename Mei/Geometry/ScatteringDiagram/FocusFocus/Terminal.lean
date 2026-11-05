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
branches of a fixed finite list of incoming exponents. Every possible crossing height has the
sign of that slab point. Thus no singular encounter enters this neighborhood,
and the upper or lower chart is fixed even as the encounter time tends to zero.
The closed branch path then becomes the incoming affine half-line ending on the
slab, independently of its outgoing exponent.

On the two sides of this neighborhood, the actual weighted ray evaluations
have a unique common linear lift through the nodal slab correspondence. Its
formula is the sum of theta monomials with their incoming coefficient maps.
The single-exponent identity is the singleton case. The statements allow an
arbitrary module of incoming parameters, tangential and stationary inputs, zero
coefficients, torsion and nilpotent smoothing parameters. All endpoint assertions
concern regular slab points.

The local slab interpretation follows Gross–Siebert, *An Invitation to Toric Degenerations*,
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

variable {ι : Type*} (s : Finset ι) (n b : ι → ℤ)

/-- One coefficient-independent terminal neighborhood for all incoming records
in a finite input list, including every candidate binomial branch. -/
def slabTerminalFiniteDomain (v : ℝ) : Set (ℝ × ℝ) :=
  ⋂ i ∈ s, slabTerminalDomain (n i) (b i) v

/-- The uniform neighborhood imposes the original terminal test on every record. -/
theorem mem_slabTerminalFiniteDomain (v : ℝ) (Q : ℝ × ℝ) :
    Q ∈ slabTerminalFiniteDomain s n b v ↔
      ∀ i ∈ s, Q ∈ slabTerminalDomain (n i) (b i) v := by
  simp [slabTerminalFiniteDomain]

/-- The common terminal domain is open, without a bound on the exponents. -/
theorem isOpen_slabTerminalFiniteDomain (v : ℝ) :
    IsOpen (slabTerminalFiniteDomain s n b v) :=
  isOpen_biInter_finset fun i _ => isOpen_slabTerminalDomain (n i) (b i) v

/-- Every regular slab point belongs to the common terminal neighborhood. -/
theorem slabPoint_mem_slabTerminalFiniteDomain {v : ℝ} (hv : v ≠ 0) :
    (0, v) ∈ slabTerminalFiniteDomain s n b v := by
  rw [mem_slabTerminalFiniteDomain]
  intro i _
  simpa using hv

/-- The uniform domain contains endpoints in both chambers, including when the
finite incoming list is empty or contains only tangential inputs. -/
theorem slabTerminalFiniteDomain_meets_chambers {v : ℝ} (hv : v ≠ 0) :
    ∃ L U : ℝ × ℝ, L ∈ slabTerminalFiniteDomain s n b v ∧
      U ∈ slabTerminalFiniteDomain s n b v ∧ L.1 < 0 ∧ 0 < U.1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_slabTerminalFiniteDomain s n b v) (0, v)
    (slabPoint_mem_slabTerminalFiniteDomain s n b hv)
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
  (t : R) (α : ι → H →ₗ[R] R)

/-- The common lift of a finite family of complete incoming records. -/
def slabTerminalFiniteLift :
    H →ₗ[R] TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1)) :=
  ∑ i ∈ s, (LinearMap.toSpanSingleton R _ (theta t (n i) (b i))).comp (α i)

/-- Evaluation of the total lift retains every incoming record and coefficient. -/
@[simp]
theorem slabTerminalFiniteLift_apply (a : H) :
    slabTerminalFiniteLift s n b t α a = ∑ i ∈ s, α i a • theta t (n i) (b i) := by
  simp only [slabTerminalFiniteLift, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]

/-- The negative chamber value of the total lift is the total actual weighted
evaluation throughout the uniform terminal neighborhood. -/
theorem exponentLeftMap_slabTerminalFiniteLift {v : ℝ} {Q : ℝ × ℝ}
    (hQ : Q ∈ slabTerminalFiniteDomain s n b v) (hside : Q.1 < 0) (a : H) :
    exponentLeftMap (C t * (1 + T 1)) (slabTerminalFiniteLift s n b t α a) =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q := by
  simp only [slabTerminalFiniteLift_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (slabThetaEvaluation_eq_exponentLeftMap t (α i a) (n i) (b i) Q hside
    (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero
      ((mem_slabTerminalFiniteDomain s n b v Q).mp hQ i hi) j)).symm

/-- The positive chamber value uses the same total lift and the same uniform
neighborhood, even for mixed normal signs or coefficients that vanish. -/
theorem exponentRightMap_slabTerminalFiniteLift {v : ℝ} {Q : ℝ × ℝ}
    (hQ : Q ∈ slabTerminalFiniteDomain s n b v) (hside : 0 < Q.1) (a : H) :
    exponentRightMap (C t * (1 + T 1)) (slabTerminalFiniteLift s n b t α a) =
      ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q := by
  simp only [slabTerminalFiniteLift_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (slabThetaEvaluation_eq_exponentRightMap t (α i a) (n i) (b i) Q hside
    (fun _ j _ => slabTerminalDomain_crossingHeight_ne_zero
      ((mem_slabTerminalFiniteDomain s n b v Q).mp hQ i hi) j)).symm

/-- The two total chamber evaluations determine one common linear face lift.
There is no requirement that the individual branches have face lifts. -/
theorem slabTerminalFinite_commonLift_iff {v : ℝ} (hv : v ≠ 0)
    (l : H →ₗ[R] TauCeti.NodeAlgebra R[T;T⁻¹] (C t * (1 + T 1))) :
    ((∀ Q ∈ slabTerminalFiniteDomain s n b v, Q.1 < 0 → ∀ a,
        exponentLeftMap (C t * (1 + T 1)) (l a) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q) ∧
      (∀ Q ∈ slabTerminalFiniteDomain s n b v, 0 < Q.1 → ∀ a,
        exponentRightMap (C t * (1 + T 1)) (l a) =
          ∑ i ∈ s, slabThetaEvaluation t (α i a) (n i) (b i) Q)) ↔
      l = slabTerminalFiniteLift s n b t α := by
  constructor
  · rintro ⟨hL, hU⟩
    obtain ⟨L, U, hLD, hUD, hLside, hUside⟩ :=
      slabTerminalFiniteDomain_meets_chambers s n b hv
    apply LinearMap.ext
    intro a
    apply exponentMaps_jointly_injective (C t * (1 + T 1))
    exact Prod.ext
      ((hL L hLD hLside a).trans
        (exponentLeftMap_slabTerminalFiniteLift s n b t α hLD hLside a).symm)
      ((hU U hUD hUside a).trans
        (exponentRightMap_slabTerminalFiniteLift s n b t α hUD hUside a).symm)
  · rintro rfl
    exact ⟨fun _ hQ hs a => exponentLeftMap_slabTerminalFiniteLift s n b t α hQ hs a,
      fun _ hQ hs a => exponentRightMap_slabTerminalFiniteLift s n b t α hQ hs a⟩

end Coefficients

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
  have hdomain : slabTerminalFiniteDomain ({()} : Finset Unit)
      (fun _ => n) (fun _ => b) v = slabTerminalDomain n b v := by
    ext Q
    simp [mem_slabTerminalFiniteDomain]
  have hlift : slabTerminalFiniteLift ({()} : Finset Unit)
      (fun _ => n) (fun _ => b) t (fun _ => α) =
        (LinearMap.toSpanSingleton R _ (theta t n b)).comp α := by
    ext a
    simp only [slabTerminalFiniteLift_apply, Finset.sum_singleton,
      LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  simpa only [hdomain, hlift, Finset.sum_singleton] using
    (slabTerminalFinite_commonLift_iff ({()} : Finset Unit)
      (fun _ => n) (fun _ => b) t (fun _ => α) hv ℓ)

end Coefficients

end Mei.FocusFocus
