/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.Algebra.PositiveDegrees.Graph
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Principal exponents of a skew lattice datum

The integral restriction of the skew form gives `p₁* : N_uf → M°`, where
`M°` is the integer dual of `N°`. The principal exponent map
`r(n) = (p₁*(n), n)` is injective even for a degenerate or zero form.
Any positive degree data on `N_uf` induce positive degree data on its image,
with exactly the same finite cutoffs and no saturation assumption.

The normalized principal normal evaluates a character at the normalized vector
in `N°`. It annihilates the principal exponent of its own degree.
These are the lattice data for the principal coefficient realization of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and
Appendix B, arXiv:1411.1394v2. The integral lift uses Mathlib's
`LinearMap.codRestrict₂`; positivity and supported rays use the graph construction.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] (D : Mei.SkewLatticeDatum N)

/-- The integral restriction `p₁*(n) = {n,-}|N°` of the skew form to an
unfrozen exponent. -/
def principalCharacter : D.unfrozen →ₗ[ℤ] Module.Dual ℤ D.sublattice :=
  (D.form.domRestrict₁₂ D.unfrozen D.sublattice).codRestrict₂
    (Algebra.linearMap ℤ ℚ) Int.cast_injective (fun n m => by
      obtain ⟨a, ha⟩ := D.integral_unfrozen_sublattice n n.property m m.property
      exact ⟨a, ha.symm⟩)

/-- The integral character has the prescribed rational value of the skew form. -/
@[simp]
theorem cast_principalCharacter_apply (n : D.unfrozen) (m : D.sublattice) :
    (D.principalCharacter n m : ℚ) = D.form n m := by
  unfold principalCharacter
  simpa [LinearMap.domRestrict₁₂_apply] using (LinearMap.codRestrict₂_apply
    (D.form.domRestrict₁₂ D.unfrozen D.sublattice)
    (Algebra.linearMap ℤ ℚ) Int.cast_injective _ n m)

/-- The principal exponent map, retaining the unfrozen degree as a second coordinate. -/
def principalEmbedding : D.unfrozen →ₗ[ℤ] (Module.Dual ℤ D.sublattice × D.unfrozen) :=
  D.principalCharacter.prod LinearMap.id

@[simp]
theorem principalEmbedding_apply (n : D.unfrozen) :
    D.principalEmbedding n = (D.principalCharacter n, n) := (rfl)

/-- The principal lift loses no exponents, including degrees in the radical. -/
theorem principalEmbedding_injective : Function.Injective D.principalEmbedding :=
  fun _ _ h => congrArg Prod.snd h

/-- The principal positive monoid is the image of the original positive monoid;
its degree is read from the retained unfrozen exponent. -/
abbrev principalPositiveDegrees (d : PositiveDegrees D.unfrozen) :
    PositiveDegrees (Module.Dual ℤ D.sublattice × D.unfrozen) :=
  d.graph D.principalCharacter.toAddMonoidHom

variable [Module.Free ℤ N]

/-- The integral normal `κ(n)ν_n` on the principal exponent lattice. It evaluates
the character coordinate on the normalized vector `κ(n)n ∈ N°`. -/
def principalNormal (n : D.unfrozen) :
    Module.Dual ℤ (Module.Dual ℤ D.sublattice × D.unfrozen) :=
  (Module.Dual.eval ℤ D.sublattice (D.sublattice.toAddSubgroup.rayVector n)).comp
    (LinearMap.fst ℤ _ _)

@[simp]
theorem principalNormal_apply (n : D.unfrozen)
    (x : Module.Dual ℤ D.sublattice × D.unfrozen) :
    D.principalNormal n x = x.1 (D.sublattice.toAddSubgroup.rayVector n) := (rfl)

/-- Every nonzero unfrozen exponent has a nonzero principal normal, even if
the skew form vanishes on that exponent. -/
@[simp]
theorem principalNormal_eq_zero_iff (n : D.unfrozen) :
    D.principalNormal n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hv : (D.sublattice.toAddSubgroup.rayVector n : N) = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℤ _).mp
      intro φ
      have he := LinearMap.congr_fun h (φ.comp D.sublattice.subtype, 0)
      simpa only [principalNormal_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.zero_apply] using he
    by_contra hn
    have hnN : (n : N) ≠ 0 := fun h => hn (Subtype.ext h)
    have hnum := Rat.num_ne_zero.mpr
      (D.sublattice.toAddSubgroup.rayIndex_pos hnN).ne'
    have he := D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector (n : N)
    rw [hv, smul_zero] at he
    exact (smul_ne_zero hnum hnN) he.symm
  · rintro rfl
    apply LinearMap.ext
    intro x
    simp

/-- Normal evaluation on a lifted exponent is the normalized skew pairing. -/
theorem cast_principalNormal_principalEmbedding (n m : D.unfrozen) :
    (D.principalNormal n (D.principalEmbedding m) : ℚ) =
      D.sublattice.toAddSubgroup.rayIndex n * D.form m n := by
  rw [principalNormal_apply, principalEmbedding_apply, cast_principalCharacter_apply,
    D.form_rayVector]

/-- The integral skew character kills its own normalized ray vector. In
particular, the principal normal annihilates the corresponding principal exponent. -/
@[simp]
theorem principalCharacter_rayVector_self (n : D.unfrozen) :
    D.principalCharacter n (D.sublattice.toAddSubgroup.rayVector n) = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [cast_principalCharacter_apply, D.form_rayVector]
  simp

end Mei.SkewLatticeDatum
