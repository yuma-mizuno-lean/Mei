/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Algebra.PositiveDegrees.Examples
public import TauCeti.Algebra.PositiveDegrees.FinitelyGenerated
public import Mei.Algebra.PositiveDegrees.Ray.Basic
public import Mei.Algebra.PositiveDegrees.Scale
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Examples and counterexamples for positive degrees

Three monoids in `ℤ × ℤ` distinguish the bounds used for degree truncations and
supported primitive rays.

* `wedgeDegrees` admits projection to the second coordinate, positive on nonzero
  allowed degrees and bounded above by the source degree, but with no cutoff modulus.
* `evenOrthant` supports the horizontal primitive ray although its generator is
  excluded; the actual ray degrees are precisely the positive even multiples.
* `parabolicDegrees` has finite cutoffs but infinitely many supported primitive
  generators of degree one. Thus finite-order ray sets must be measured on actual
  allowed degrees, rather than on the degrees of ambient primitive generators.

Two further examples compute the canonical cutoff moduli of changes of degree on a fixed
monoid, `TauCeti.PositiveDegreeMap.changeDegree`, which also computes
`TauCeti.PositiveDegrees.changeDegreeEquiv` on completed BCH groups.

* On `ℕ`, the change from `δ(a) = a` to `2δ` has modulus `⌊k / 2⌋`, and the reverse change
  has modulus `2k`.
* On the quadratic wedge `P = {(a, b) | 0 ≤ b ≤ a ≤ b²}`, both coordinates are positive
  degrees. The change from `δ(a, b) = a` to `δ'(a, b) = b` has modulus `k²`, attained at
  `(k², k)`, and the reverse change has modulus `k`, attained at `(k, k)`. No linear bound
  `a ≤ c b` holds on `P`, so `P` is not finitely generated.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap SupportedRay)

namespace TauCeti.PositiveDegrees.Examples

open Mei

/-- Projection to the second coordinate, with values in the one-dimensional lattice. -/
def wedgeProjection : (ℤ × ℤ) →+ (Unit → ℤ) :=
  AddMonoidHom.pi fun _ => AddMonoidHom.snd ℤ ℤ

/-- The wedge projection evaluates to the second coordinate. -/
@[simp]
theorem wedgeProjection_apply (n : ℤ × ℤ) (u : Unit) : wedgeProjection n u = n.2 := (rfl)

/-- The projection takes allowed points into the nonnegative target monoid. -/
theorem wedgeProjection_mem {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid) :
    wedgeProjection n ∈ (PositiveDegrees.orthant Unit).monoid := by
  exact PositiveDegrees.mem_orthant_monoid.mpr fun u => by
    simpa only [wedgeProjection_apply, AddMonoidHom.coe_snd, mem_nonnegIntegers_monoid] using
      snd_mem_nonnegIntegers_monoid hn

/-- The wedge projection preserves nonzero allowed degrees. -/
theorem wedgeProjection_ne_zero {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid)
    (hne : n ≠ 0) : wedgeProjection n ≠ 0 := by
  intro hz
  apply snd_ne_zero_of_mem_wedgeDegrees hn hne
  simpa only [wedgeProjection_apply, AddMonoidHom.coe_snd, Pi.zero_apply] using congrFun hz ()

/-- Target degrees are bounded above by source degrees, with constant one. -/
theorem wedgeProjection_degree_le {n : ℤ × ℤ} (hn : n ∈ wedgeDegrees.monoid) :
    (PositiveDegrees.orthant Unit).degree (wedgeProjection n) ≤ wedgeDegrees.degree n := by
  simpa using snd_le_degree_of_mem_wedgeDegrees hn

/-- No cutoff function, even a nonmonotone one, bounds the source degrees of
points whose projected degree is one. -/
theorem wedgeProjection_no_cutoff_modulus (μ : ℕ → ℕ) :
    ∃ n ∈ wedgeDegrees.monoid, (μ 1 : ℤ) < wedgeDegrees.degree n ∧
      (PositiveDegrees.orthant Unit).degree (wedgeProjection n) ≤ 1 := by
  simpa using exists_lt_degree_snd_le_one μ

/-- The upper bound on projected degrees cannot supply a positive degree map. -/
theorem not_exists_wedgeProjection_map :
    ¬ ∃ T : PositiveDegreeMap wedgeDegrees (PositiveDegrees.orthant Unit),
      ∀ n, T n = wedgeProjection n := by
  rintro ⟨T, hT⟩
  obtain ⟨n, hn, hgt, hle⟩ := wedgeProjection_no_cutoff_modulus T.modulus
  have h := T.degree_gt 1 hn hgt
  rw [hT] at h
  omega

/-- The nonnegative quadrant with an even first coordinate. -/
def evenOrthantMonoid : AddSubmonoid (ℤ × ℤ) :=
  ((AddSubmonoid.nonneg ℤ).prod (AddSubmonoid.nonneg ℤ)) ⊓
    (AddSubgroup.zmultiples (2 : ℤ)).toAddSubmonoid.comap (AddMonoidHom.fst ℤ ℤ)

/-- The even quadrant is characterized by nonnegativity and parity. -/
@[simp]
theorem mem_evenOrthantMonoid {n : ℤ × ℤ} :
    n ∈ evenOrthantMonoid ↔ 0 ≤ n.1 ∧ 0 ≤ n.2 ∧ Even n.1 := by
  simp [evenOrthantMonoid, AddSubmonoid.mem_prod,
    AddSubmonoid.mem_nonneg, Int.mem_zmultiples_iff, even_iff_two_dvd, and_assoc]

/-- Coordinate-sum degree on the even quadrant. -/
def evenOrthant : PositiveDegrees (ℤ × ℤ) where
  monoid := evenOrthantMonoid
  degree := (AddMonoidHom.fst ℤ ℤ) + (AddMonoidHom.snd ℤ ℤ)
  degree_pos := by
    rintro ⟨a, b⟩ hn hne
    obtain ⟨ha, hb, _⟩ := mem_evenOrthantMonoid.mp hn
    have : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Prod.ext h.1 h.2)
    dsimp
    omega
  finite_le k := by
    apply ((Set.finite_Icc (a := (0 : ℤ)) (b := k)).prod
      (Set.finite_Icc (a := (0 : ℤ)) (b := k))).subset
    rintro ⟨a, b⟩ ⟨hn, hk⟩
    obtain ⟨ha, hb, _⟩ := mem_evenOrthantMonoid.mp hn
    dsimp at hk
    exact ⟨⟨ha, by omega⟩, ⟨hb, by omega⟩⟩

/-- The allowed even-quadrant degrees. -/
@[simp]
theorem evenOrthant_monoid : evenOrthant.monoid = evenOrthantMonoid := (rfl)

/-- The even-quadrant degree is the coordinate sum. -/
@[simp]
theorem evenOrthant_degree (n : ℤ × ℤ) : evenOrthant.degree n = n.1 + n.2 := (rfl)

/-- The horizontal primitive ray is supported by the allowed point `(2,0)`. -/
def evenHorizontalRay : SupportedRay evenOrthant where
  generator := (1, 0)
  isPrimitive := TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
  supported := ⟨2, by omega, by simp⟩

/-- The horizontal ray has primitive generator `(1,0)`. -/
@[simp]
theorem evenHorizontalRay_generator : evenHorizontalRay.generator = (1, 0) := (rfl)

/-- A supported primitive generator need not itself be allowed. -/
theorem evenHorizontalRay_generator_notMem :
    evenHorizontalRay.generator ∉ evenOrthant.monoid := by simp

/-- The actual horizontal ray degrees are exactly the positive even multiples. -/
@[simp]
theorem mem_evenHorizontalRay_iff {n : ℤ × ℤ} :
    n ∈ evenHorizontalRay.rayDegrees ↔ ∃ a : ℤ, 0 < a ∧ n = (2 * a, 0) := by
  rw [SupportedRay.mem_rayDegrees]
  constructor
  · rintro ⟨hn, b, hb, rfl⟩
    obtain ⟨_, _, a, ha⟩ := mem_evenOrthantMonoid.mp hn
    simp only [evenHorizontalRay_generator, Prod.smul_mk, zsmul_eq_mul, Int.cast_id, mul_one] at ha
    refine ⟨a, by omega, ?_⟩
    simp [evenHorizontalRay_generator, ha, two_mul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, 2 * a, by omega, ?_⟩
    · simp [ha.le]
    · simp

/-- The origin together with the integer points `1 ≤ a` and `|b| ≤ a²`. -/
def parabolicMonoid : AddSubmonoid (ℤ × ℤ) where
  carrier := {n | n = 0 ∨ 1 ≤ n.1 ∧ |n.2| ≤ n.1 ^ 2}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | hx) (rfl | hy)
    · exact Or.inl (by simp)
    · simpa using Or.inr hy
    · simpa using Or.inr hx
    · refine Or.inr ⟨by dsimp; omega, ?_⟩
      have hab := abs_add_le x.2 y.2
      have hxy : 0 ≤ x.1 * y.1 := mul_nonneg (by omega) (by omega)
      dsimp
      nlinarith [hx.2, hy.2]

/-- Membership in the parabolic monoid. -/
@[simp]
theorem mem_parabolicMonoid {n : ℤ × ℤ} :
    n ∈ parabolicMonoid ↔ n = 0 ∨ 1 ≤ n.1 ∧ |n.2| ≤ n.1 ^ 2 := Iff.rfl

/-- First-coordinate degree on the parabolic monoid has finite cutoffs. -/
def parabolicDegrees : PositiveDegrees (ℤ × ℤ) where
  monoid := parabolicMonoid
  degree := AddMonoidHom.fst ℤ ℤ
  degree_pos hn hne := by
    obtain h | h := mem_parabolicMonoid.mp hn
    · exact (hne h).elim
    · dsimp
      omega
  finite_le k := by
    apply ((Set.finite_Icc (a := (0 : ℤ)) (b := k)).prod
      (Set.finite_Icc (a := -((k : ℤ) ^ 2)) (b := (k : ℤ) ^ 2))).subset
    rintro ⟨a, b⟩ ⟨hn, hk⟩
    obtain h | h := mem_parabolicMonoid.mp hn
    · rw [h]
      exact ⟨⟨le_rfl, Int.natCast_nonneg k⟩,
        ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩⟩
    · dsimp at hk
      dsimp at h
      have hab := abs_le.mp h.2
      have hak : a ^ 2 ≤ (k : ℤ) ^ 2 := by nlinarith
      exact ⟨⟨by omega, hk⟩, ⟨by omega, by omega⟩⟩

/-- The allowed parabolic degrees. -/
@[simp]
theorem parabolicDegrees_monoid : parabolicDegrees.monoid = parabolicMonoid := (rfl)

/-- Parabolic degree is the first coordinate. -/
@[simp]
theorem parabolicDegrees_degree (n : ℤ × ℤ) : parabolicDegrees.degree n = n.1 := (rfl)

/-- Every `(1,b)` is primitive and has a positive multiple in the parabolic monoid. -/
def parabolicRay (b : ℤ) : SupportedRay parabolicDegrees where
  generator := (1, b)
  isPrimitive := TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
  supported := by
    let a := |b| + 1
    have ha : 0 < a := by dsimp [a]; have := abs_nonneg b; omega
    refine ⟨a, ha, ?_⟩
    apply mem_parabolicMonoid.mpr
    right
    simp only [Prod.smul_mk, zsmul_eq_mul, Int.cast_id, mul_one]
    refine ⟨by omega, ?_⟩
    rw [abs_mul, abs_of_pos ha]
    dsimp [a]
    nlinarith [abs_nonneg b]

/-- The parabolic family has primitive generator `(1,b)`. -/
@[simp]
theorem parabolicRay_generator (b : ℤ) : (parabolicRay b).generator = (1, b) := (rfl)

/-- Distinct slopes give distinct supported primitive rays. -/
theorem parabolicRay_injective : Function.Injective parabolicRay := by
  intro b c h
  simpa only [parabolicRay_generator] using
    congrArg (fun w : SupportedRay parabolicDegrees => w.generator.2) h

/-- Finite cutoffs do not imply finitely many supported primitive generators of
bounded degree: the parabolic monoid has infinitely many of degree one. -/
theorem infinite_parabolic_generators_degree_one :
    Set.Infinite {w : SupportedRay parabolicDegrees |
      parabolicDegrees.degree w.generator = 1} := by
  apply Set.infinite_of_injective_forall_mem parabolicRay_injective
  intro b
  simp

/-- The quadratic wedge is not finitely generated: on a finitely generated monoid the first
coordinate would be bounded by a multiple of the second. -/
theorem not_fg_quadraticWedgeMonoid : ¬ quadraticWedgeMonoid.FG := by
  intro hfg
  obtain ⟨c, hc⟩ := hfg.exists_degree_le_mul quadraticWedgeFst.degree quadraticWedgeSnd.degree
    fun _ hn hne => quadraticWedgeSnd.degree_pos (by rwa [quadraticWedgeSnd_monoid]) hne
  have h := hc (((c : ℤ) + 1) ^ 2, (c : ℤ) + 1)
    (mem_quadraticWedgeMonoid.mpr ⟨by dsimp only; omega, by dsimp only; nlinarith, le_rfl⟩)
  simp only [quadraticWedgeFst_degree, quadraticWedgeSnd_degree] at h
  nlinarith

end TauCeti.PositiveDegrees.Examples
