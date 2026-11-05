/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import TauCeti.Algebra.Module.Primitive
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Basic.Real.Basic

/-!
# Rank-two polynomial inputs

Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Theorem 9.9
(arXiv:2503.03719v1), prove positivity for scattering diagrams in a rank-two lattice `M` whose
incoming walls are affine lines carrying polynomial wall functions. We record such an input on
positive degree data `(L, P, δ)` (`Mei.PositiveDegrees`):

* a surjection `π : L → M` onto a lattice of rank two;
* incoming lines indexed by `j ∈ ι`, each with a primitive tangent `m_j ∈ M`, a primitive
  coorientation `ν_j ∈ M*` annihilating `m_j` and a real offset `c_j`, so that the line is
  `{y ∈ M_ℝ | ν_j(y) = c_j}`;
* for each line a finite set of exponents `n ∈ P ∖ {0}` with `π(n) ∈ ℕ_{>0} m_j`, the degrees of
  the terms `c_{j,n} z^n` of the wall function `f_j = 1 + ∑_n c_{j,n} z^n`.

The coefficients `c_{j,n}` are independent variables over `ℚ`; we index them by
`RankTwoPolynomialInput.Variable` and allow any coefficient family in a commutative ring, the
independent variables being the generators of `MvPolynomial I.Variable ℚ`. The index type of the
lines is arbitrary; for every `k`, only finitely many lines have a term of degree at most `k`
(`RankTwoPolynomialInput.finite_nontrivial`); these form the set
`RankTwoPolynomialInput.linesAtOrder k`. The wall of line `j` is the cylinder over it in `L_ℝ`,
cooriented by the primitive integral normal `ν_j ∘ π` (`RankTwoPolynomialInput.wallNormal`), and
acts by `z^q ↦ z^q f_j^{⟨ν_j, π(q)⟩}`. Reversing `ν_j` and `c_j` presents the same line.

The incoming diagram, its function-wall grouping and its positivity are in
`Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Incoming` and
`Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Grouping`; translations of the lines into
general position are in `Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Translation`.
Primitivity uses `TauCeti.IsPrimitive` and Mathlib's `Module.evalEquiv`.
-/

public section

noncomputable section

namespace Mei

/-- A rank-two polynomial input (Burcroff–Lee–Mou, Theorem 9.9) on positive degree data
`(L, P, δ)`: a surjection `π : L → M` onto a rank-two lattice and incoming affine lines
`{ν_j = c_j}` in `M_ℝ`, indexed by `ι`, with primitive tangents `m_j`, primitive coorientations
`ν_j` annihilating them, and finite sets of exponents `n ∈ P ∖ {0}` with `π(n) ∈ ℕ_{>0} m_j` for
the terms `c_{j,n} z^n` of the wall functions `f_j = 1 + ∑_n c_{j,n} z^n`. Only finitely many lines
have a term of degree at most `k`, for every `k`. -/
structure RankTwoPolynomialInput {L : Type*} [AddCommGroup L] (d : PositiveDegrees L)
    (M : Type*) [AddCommGroup M] (ι : Type*) where
  /-- The projection `π : L → M`. -/
  projection : L →+ M
  /-- The projection is surjective. -/
  projection_surjective : Function.Surjective projection
  /-- The target lattice has rank two. -/
  finrank_eq_two : Module.finrank ℤ M = 2
  /-- The primitive tangent `m_j` of the incoming line `j`. -/
  tangent : ι → M
  /-- The tangents are primitive. -/
  isPrimitive_tangent : ∀ j, TauCeti.IsPrimitive (tangent j)
  /-- The coorientation `ν_j ∈ M*` of the incoming line `j`. -/
  normal : ι → Module.Dual ℤ M
  /-- The coorientations are primitive. -/
  isPrimitive_normal : ∀ j, TauCeti.IsPrimitive (normal j)
  /-- The coorientation annihilates the tangent. -/
  normal_tangent : ∀ j, normal j (tangent j) = 0
  /-- The offset `c_j` of the incoming line `{ν_j = c_j}`. -/
  offset : ι → ℝ
  /-- The exponents `n` of the terms `c_{j,n} z^n` of the wall function of line `j`. -/
  exponents : ι → Finset L
  /-- The exponents are allowed degrees. -/
  mem_monoid_of_mem_exponents {j : ι} {n : L} : n ∈ exponents j → n ∈ d.monoid
  /-- The exponents are nonzero. -/
  ne_zero_of_mem_exponents {j : ι} {n : L} : n ∈ exponents j → n ≠ 0
  /-- The exponents project to positive multiples of the tangent. -/
  exists_projection_eq_of_mem_exponents {j : ι} {n : L} :
    n ∈ exponents j → ∃ k : ℕ, 0 < k ∧ projection n = k • tangent j
  /-- Only finitely many lines have a term of degree at most `k`. -/
  finite_nontrivial (k : ℕ) : {j | ∃ n ∈ exponents j, d.degree n ≤ k}.Finite

namespace RankTwoPolynomialInput

variable {L M ι : Type*} [AddCommGroup L] [AddCommGroup M] {d : PositiveDegrees L}
  (I : RankTwoPolynomialInput d M ι)

/-- The independent coefficient variables `c_{j,n}`, one for each line `j` and exponent
`n` of its wall function. -/
abbrev Variable : Type _ := Σ j : ι, I.exponents j

/-- The lines with a term of degree at most `k`, the only lines whose walls are active at
order `k`. -/
def linesAtOrder (k : ℕ) : Set ι :=
  {j | ∃ n ∈ I.exponents j, d.degree n ≤ k}

/-- A line belongs to `linesAtOrder k` when it has a term of degree at most `k`. -/
@[simp]
theorem mem_linesAtOrder {k : ℕ} {j : ι} :
    j ∈ I.linesAtOrder k ↔ ∃ n ∈ I.exponents j, d.degree n ≤ k :=
  Iff.rfl

/-- Only finitely many lines have a term of degree at most `k`. -/
theorem finite_linesAtOrder (k : ℕ) : (I.linesAtOrder k).Finite :=
  I.finite_nontrivial k

/-- A line active at some order stays active at every higher order. -/
theorem linesAtOrder_mono : Monotone I.linesAtOrder := fun _ _ hkl _ ⟨n, hn, hnk⟩ =>
  ⟨n, hn, hnk.trans (by exact_mod_cast hkl)⟩

/-- The primitive integral normal `ν_j ∘ π` of the cylinder over the incoming line `j`. -/
def wallNormal (j : ι) : L →+ ℤ :=
  (I.normal j).toAddMonoidHom.comp I.projection

/-- The cylinder normal pairs a degree `q` with `ν_j(π(q))`. -/
theorem wallNormal_apply (j : ι) (q : L) : I.wallNormal j q = I.normal j (I.projection q) :=
  (rfl)

/-- The cylinder normal is nonzero, since `ν_j ≠ 0` and `π` is surjective. -/
theorem wallNormal_ne_zero (j : ι) : I.wallNormal j ≠ 0 := by
  intro he
  apply (I.isPrimitive_normal j).ne_zero
  ext m
  obtain ⟨q, rfl⟩ := I.projection_surjective m
  simpa [wallNormal_apply] using DFunLike.congr_fun he q

/-- The exponents of a line are tangent to its cylinder. -/
theorem wallNormal_eq_zero_of_mem_exponents {j : ι} {n : L} (hn : n ∈ I.exponents j) :
    I.wallNormal j n = 0 := by
  obtain ⟨k, -, hk⟩ := I.exists_projection_eq_of_mem_exponents hn
  simp [wallNormal_apply, hk, I.normal_tangent j]

variable [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Some degree has cylinder-normal pairing one: a primitive covector of the lattice `M`
takes the value one, and `π` is surjective. -/
theorem exists_wallNormal_eq_one (j : ι) : ∃ q : L, I.wallNormal j q = 1 := by
  obtain ⟨g, hg⟩ := TauCeti.isPrimitive_def.mp (I.isPrimitive_normal j)
  obtain ⟨q, hq⟩ := I.projection_surjective ((Module.evalEquiv ℤ M).symm g)
  exact ⟨q, by rw [wallNormal_apply, hq, Module.apply_evalEquiv_symm_apply, hg]⟩

/-- The cylinder normal is primitive. -/
theorem isPrimitive_wallNormal (j : ι) : TauCeti.IsPrimitive (I.wallNormal j) := by
  obtain ⟨q, hq⟩ := I.exists_wallNormal_eq_one j
  exact TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap (AddMonoidHom.eval q), hq⟩

end RankTwoPolynomialInput

end Mei
