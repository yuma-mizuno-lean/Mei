/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.LinearAlgebra.Basis.Diagonal
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Adapted bases of skew lattice data

An adapted basis of a skew lattice datum `(N, N_uf, N°, {,})` is a basis `(e_i)` of `N`
together with a finite set `I_uf` of indices and positive integers `d_i` such that the `e_i` with
`i ∈ I_uf` span the unfrozen sublattice `N_uf` and the multiples `d_i e_i` span `N°`.
This is the coordinate system in which the principal coefficients of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1 and Appendix B
(arXiv:1411.1394v2), are written: the positive monoid `P_N = ∑_{i ∈ I_uf} ℕ e_i` with
total degree `∑ n_i`, and power series in variables `t_i`, `i ∈ I_uf`.

An adapted basis is extra data on a skew lattice datum, and the multipliers and unfrozen
indices are determined by the basis (`AdaptedBasis.ext`). The unfrozen vectors are exactly
those with vanishing frozen coordinates, and `N°` consists of the vectors whose `i`-th
coordinate is divisible by `d_i`. The `e_i` with `i ∈ I_uf` form a basis of `N_uf`
(`AdaptedBasis.unfrozenBasis`) and the `d_i e_i` a basis of `N°`
(`AdaptedBasis.sublatticeBasis`). The ray index of `e_i` with respect to `N°` is
`κ(e_i) = d_i`, with normalized vector `d_i e_i`.

The positive monoid `P_N` with its total degree is `unfrozenBasis.positiveDegrees`
(`Module.Basis.positiveDegrees`). Its natural coordinates describe the completed principal
coefficient algebra as power series in the `t_i`
(`AdaptedBasis.principalCoefficientCompletionEquiv`, in
`Mei.Geometry.ScatteringDiagram.Skew.Coefficient.Completion`).

## Main declarations

* `Mei.SkewLatticeDatum.AdaptedBasis`: an adapted basis of a skew lattice datum.
* `Mei.SkewLatticeDatum.AdaptedBasis.ext`: an adapted basis is determined by its basis.
* `Mei.SkewLatticeDatum.AdaptedBasis.mem_unfrozen_iff`,
  `Mei.SkewLatticeDatum.AdaptedBasis.mem_sublattice_iff`: the two sublattices in coordinates.
* `Mei.SkewLatticeDatum.AdaptedBasis.unfrozenBasis`,
  `Mei.SkewLatticeDatum.AdaptedBasis.sublatticeBasis`: the induced bases of `N_uf` and `N°`.
* `Mei.SkewLatticeDatum.AdaptedBasis.rayIndex_basis`: `κ(e_i) = d_i`.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open Module

variable {N : Type*} [AddCommGroup N]

/-- An adapted basis of a skew lattice datum: a basis `(e_i)` of `N`, a finite set `I_uf` of
unfrozen indices whose basis vectors span `N_uf`, and positive integers `d_i` whose multiples
`d_i e_i` span `N°`. Since `(e_i)` is a basis, the vectors `e_i` with `i ∈ I_uf` then form a
basis of `N_uf` and the `d_i e_i` a basis of `N°`. -/
structure AdaptedBasis (D : SkewLatticeDatum N) (ι : Type*) where
  /-- The basis `(e_i)` of `N`. -/
  basis : Basis ι ℤ N
  /-- The unfrozen indices `I_uf`. -/
  unfrozenIndex : Finset ι
  /-- The multipliers `d_i`. -/
  multiplier : ι → ℕ
  /-- The multipliers are positive. -/
  multiplier_pos : ∀ i, 0 < multiplier i
  /-- The unfrozen basis vectors span `N_uf`. -/
  unfrozen_eq_span : D.unfrozen = Submodule.span ℤ (basis '' unfrozenIndex)
  /-- The multiples `d_i e_i` span `N°`. -/
  sublattice_eq_span : D.sublattice = Submodule.span ℤ (Set.range fun i => multiplier i • basis i)

namespace AdaptedBasis

variable {D : SkewLatticeDatum N} {ι : Type*} (B : D.AdaptedBasis ι)

/-- A vector is unfrozen exactly when its coordinates outside `I_uf` vanish. -/
theorem mem_unfrozen_iff {n : N} :
    n ∈ D.unfrozen ↔ ∀ i ∉ B.unfrozenIndex, B.basis.repr n i = 0 := by
  simp only [B.unfrozen_eq_span, Basis.mem_span_image, Finsupp.support_subset_iff, Finset.mem_coe]

/-- A basis vector is unfrozen exactly when its index is unfrozen. -/
@[simp]
theorem basis_mem_unfrozen_iff {i : ι} : B.basis i ∈ D.unfrozen ↔ i ∈ B.unfrozenIndex := by
  simp only [B.unfrozen_eq_span, Basis.self_mem_span_image, Finset.mem_coe]

/-- The multiple `d_i e_i` lies in `N°`. -/
theorem nsmul_basis_mem_sublattice (i : ι) : B.multiplier i • B.basis i ∈ D.sublattice := by
  rw [B.sublattice_eq_span]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- A vector lies in `N°` exactly when its `i`-th coordinate is divisible by `d_i` for
every `i`. -/
theorem mem_sublattice_iff {n : N} :
    n ∈ D.sublattice ↔ ∀ i, (B.multiplier i : ℤ) ∣ B.basis.repr n i := by
  constructor
  · intro hn i
    rw [B.sublattice_eq_span] at hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases eq_or_ne j i with rfl | hji
      · simp
      · simp [hji]
    | zero => simp
    | add x y _ _ hx hy => simpa using dvd_add hx hy
    | smul a x _ hx => simpa using hx.mul_left a
  · intro h
    rw [← B.basis.linearCombination_repr n, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem (R := ℤ) _ _ _ fun i _ => ?_
    obtain ⟨c, hc⟩ := h i
    rw [hc, mul_comm, mul_smul, natCast_zsmul]
    exact Submodule.smul_mem _ _ (B.nsmul_basis_mem_sublattice i)

/-- The multiple `m e_i` lies in `N°` exactly when `d_i` divides `m`. -/
@[simp]
theorem nsmul_basis_mem_sublattice_iff {m : ℕ} {i : ι} :
    m • B.basis i ∈ D.sublattice ↔ B.multiplier i ∣ m := by
  rw [B.mem_sublattice_iff]
  refine ⟨fun h => Int.natCast_dvd_natCast.mp (by simpa using h i), fun h j => ?_⟩
  rcases eq_or_ne i j with rfl | hij
  · simpa using Int.natCast_dvd_natCast.mpr h
  · simp [hij]

/-- The multipliers and the unfrozen indices of an adapted basis are determined by its
basis. -/
@[ext]
theorem ext {B B' : D.AdaptedBasis ι} (h : B.basis = B'.basis) : B = B' := by
  have hd : B.multiplier = B'.multiplier := by
    funext i
    have h₁ := B.nsmul_basis_mem_sublattice_iff.mp (h ▸ B'.nsmul_basis_mem_sublattice i)
    have h₂ := B'.nsmul_basis_mem_sublattice_iff.mp (h ▸ B.nsmul_basis_mem_sublattice i)
    exact Nat.dvd_antisymm h₁ h₂
  have hI : B.unfrozenIndex = B'.unfrozenIndex := by
    ext i
    rw [← B.basis_mem_unfrozen_iff, ← B'.basis_mem_unfrozen_iff, h]
  cases B
  cases B'
  cases h
  cases hd
  cases hI
  rfl

/-- The basis vectors `d_i e_i` are linearly independent. -/
theorem linearIndependent_nsmul_basis :
    LinearIndependent ℤ fun i => B.multiplier i • B.basis i := by
  have h := B.basis.linearIndependent.smul_of_isRightRegular
    (w := fun i => (B.multiplier i : ℤ))
    fun i => (isRegular_iff_ne_zero.mpr (by exact_mod_cast (B.multiplier_pos i).ne')).right
  convert h using 1
  funext i
  simp

/-- The basis `(e_i)_{i ∈ I_uf}` of the unfrozen sublattice `N_uf`. -/
def unfrozenBasis : Basis B.unfrozenIndex ℤ D.unfrozen :=
  (Basis.span (B.basis.linearIndependent.comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by
      rw [B.unfrozen_eq_span, Set.range_comp, Subtype.range_coe]))

/-- The unfrozen basis consists of the basis vectors `e_i` with `i ∈ I_uf`. -/
@[simp]
theorem coe_unfrozenBasis (i : B.unfrozenIndex) : (B.unfrozenBasis i : N) = B.basis i := by
  simp [unfrozenBasis]

/-- Unfrozen coordinates are the corresponding coordinates in the ambient basis. -/
@[simp]
theorem unfrozenBasis_repr (n : D.unfrozen) (i : B.unfrozenIndex) :
    B.unfrozenBasis.repr n i = B.basis.repr n i := by
  classical
  have h : (Finsupp.lapply i ∘ₗ B.unfrozenBasis.repr.toLinearMap : D.unfrozen →ₗ[ℤ] ℤ) =
      Finsupp.lapply (i : ι) ∘ₗ B.basis.repr.toLinearMap ∘ₗ D.unfrozen.subtype := by
    refine B.unfrozenBasis.ext fun j => ?_
    simp [Finsupp.single_apply]
  exact LinearMap.congr_fun h n

/-- The basis `(d_i e_i)` of the sublattice `N°`. -/
def sublatticeBasis : Basis ι ℤ D.sublattice :=
  (Basis.span B.linearIndependent_nsmul_basis).map (LinearEquiv.ofEq _ _ B.sublattice_eq_span.symm)

/-- The sublattice basis consists of the vectors `d_i e_i`. -/
@[simp]
theorem coe_sublatticeBasis (i : ι) :
    (B.sublatticeBasis i : N) = B.multiplier i • B.basis i := by
  simp [sublatticeBasis]

/-- The ambient coordinates of a vector of `N°` are its sublattice coordinates multiplied
by `d_i`. -/
theorem basis_repr_coe_sublattice (n : D.sublattice) (i : ι) :
    B.basis.repr n i = B.multiplier i * B.sublatticeBasis.repr n i := by
  exact B.sublatticeBasis.repr_apply_of_apply_eq_smul B.basis
    (g := D.sublattice.subtype) (s := fun j => (B.multiplier j : ℤ))
    (fun j => by simp [natCast_zsmul]) n i

section RayIndex

variable [Module.Free ℤ N]

/-- The ray index of a basis vector with respect to `N°` is its multiplier: `κ(e_i) = d_i`. -/
@[simp]
theorem rayIndex_basis (i : ι) :
    D.sublattice.toAddSubgroup.rayIndex (B.basis i) = B.multiplier i := by
  rw [AddSubgroup.rayIndex_of_isPrimitive _ (B.basis.isPrimitive i), Nat.cast_inj]
  refine addOrderOf_eq_iff (B.multiplier_pos i) |>.mpr ⟨?_, fun m hm hm0 => ?_⟩
  · rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact B.nsmul_basis_mem_sublattice i
  · rw [← QuotientAddGroup.mk_nsmul, Ne, QuotientAddGroup.eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd hm0 (B.nsmul_basis_mem_sublattice_iff.mp h))
      (not_le.mpr hm)

/-- The normalized vector `κ(e_i) e_i` of a basis vector is `d_i e_i`. -/
@[simp]
theorem coe_rayVector_basis (i : ι) :
    (D.sublattice.toAddSubgroup.rayVector (B.basis i) : N) = B.multiplier i • B.basis i := by
  have h := D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector (B.basis i)
  rw [B.rayIndex_basis] at h
  simpa using h

end RayIndex

end AdaptedBasis

end Mei.SkewLatticeDatum
