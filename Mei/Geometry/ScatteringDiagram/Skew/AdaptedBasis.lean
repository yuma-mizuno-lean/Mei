/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.LinearAlgebra.Basis.Diagonal
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.GroupTheory.IndexNSmul

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

Conversely, a finite basis with chosen unfrozen indices, positive multipliers and an
alternating rational form determines a skew lattice datum with that adapted basis as soon as the
two integrality conditions hold on basis vectors (`SkewLatticeDatum.ofBasis`,
`AdaptedBasis.ofBasis`).

## Main declarations

* `Mei.SkewLatticeDatum.AdaptedBasis`: an adapted basis of a skew lattice datum.
* `Mei.SkewLatticeDatum.AdaptedBasis.ext`: an adapted basis is determined by its basis.
* `Mei.SkewLatticeDatum.AdaptedBasis.mem_unfrozen_iff`,
  `Mei.SkewLatticeDatum.AdaptedBasis.mem_sublattice_iff`: the two sublattices in coordinates.
* `Mei.SkewLatticeDatum.AdaptedBasis.unfrozenBasis`,
  `Mei.SkewLatticeDatum.AdaptedBasis.sublatticeBasis`: the induced bases of `N_uf` and `N°`.
* `Mei.SkewLatticeDatum.AdaptedBasis.rayIndex_basis`: `κ(e_i) = d_i`.
* `Mei.SkewLatticeDatum.ofBasis`, `Mei.SkewLatticeDatum.AdaptedBasis.ofBasis`: the skew lattice
  datum and adapted basis defined by a finite basis, integrality being checked on basis vectors.
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

/-- An unfrozen basis vector `e_i`, `i ∈ I_uf`, lies in `N_uf`. -/
theorem basis_mem_unfrozen (i : B.unfrozenIndex) : B.basis i ∈ D.unfrozen :=
  B.basis_mem_unfrozen_iff.mpr i.2

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

section OfBasis

variable {κ : Type*} [Finite κ] (b : Basis κ ℤ N) (S : Finset κ) (m : κ → ℕ)
  (f : N →ₗ[ℤ] N →ₗ[ℤ] ℚ)

/-- The skew lattice datum written in a finite basis `(b_i)`: the unfrozen sublattice is spanned
by the `b_i` with `i ∈ S`, the finite-index sublattice by the multiples `m_i b_i`, and the form is
an alternating form whose integrality conditions are checked on basis vectors,
`{b_i, m_j b_j} ∈ ℤ` and `{b_j, m_i b_i} ∈ ℤ` for `i ∈ S` and every `j`. Its adapted basis is
`AdaptedBasis.ofBasis`. -/
def ofBasis (hm : ∀ i, 0 < m i) (hf : f.IsAlt)
    (h₁ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b i) (m j • b j) = k)
    (h₂ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b j) (m i • b i) = k) : SkewLatticeDatum N where
  unfrozen := Submodule.span ℤ (b '' S)
  unfrozen_saturated n x hx := by
    refine or_iff_not_imp_left.mpr fun hn => ?_
    rw [Submodule.mem_toAddSubmonoid, Basis.mem_span_image, Finsupp.support_subset_iff] at hx ⊢
    intro i hi
    simpa [hn] using hx i hi
  sublattice := Submodule.span ℤ (Set.range fun i => m i • b i)
  finiteIndex_sublattice := by
    have := Fintype.ofFinite κ
    have : Module.Free ℤ N := Module.Free.of_basis b
    have : Module.Finite ℤ N := Module.Finite.of_basis b
    have hP : ∀ i, m i ∣ ∏ j, m j := fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hP0 : ∏ j, m j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hm i).ne'
    have : (nsmulAddMonoidHom (α := N) (∏ j, m j)).range.FiniteIndex := by
      refine ⟨?_⟩
      rw [AddSubgroup.index_range_nsmul]
      exact pow_ne_zero _ hP0
    refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (α := N) (∏ j, m j)).range) ?_
    rintro _ ⟨x, rfl⟩
    rw [nsmulAddMonoidHom_apply, ← b.sum_repr x, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hP i
    rw [smul_comm, hc, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (nsmul_mem (Submodule.subset_span
      (Set.mem_range_self (f := fun i => m i • b i) i)) c)
  form := f
  isAlt_form := hf
  integral_unfrozen_sublattice a ha c hc := by
    have hle : Submodule.map₂ f (Submodule.span ℤ (b '' S))
        (Submodule.span ℤ (Set.range fun i => m i • b i)) ≤
          LinearMap.range (Algebra.linearMap ℤ ℚ) := by
      rw [Submodule.map₂_span_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := h₁ i hi j
      exact ⟨k, by simp [hk]⟩
    obtain ⟨k, hk⟩ := hle (Submodule.apply_mem_map₂ f ha hc)
    exact ⟨k, by simpa using hk.symm⟩
  integral_unfrozen_inf_sublattice a c hc := by
    have := Fintype.ofFinite κ
    obtain ⟨hcS, hcm⟩ := hc
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hcm
    have ht : ∀ j ∉ S, t j = 0 := by
      intro j hj
      rw [SetLike.mem_coe, Basis.mem_span_image, Finsupp.support_subset_iff] at hcS
      have h := hcS j hj
      simp only [map_sum, map_zsmul, map_nsmul, Basis.repr_self, Finsupp.smul_single,
        Finsupp.finsetSum_apply] at h
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        (fun c _ hc => Finsupp.single_eq_of_ne' hc), Finsupp.single_eq_same] at h
      simpa [(hm j).ne'] using h
    have hle : Submodule.map₂ f (Submodule.span ℤ (Set.range b))
        (Submodule.span ℤ ((fun i => m i • b i) '' S)) ≤
          LinearMap.range (Algebra.linearMap ℤ ℚ) := by
      rw [Submodule.map₂_span_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨i, hi, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := h₂ i hi j
      exact ⟨k, by simp [hk]⟩
    have hc : ∑ j, t j • m j • b j ∈ Submodule.span ℤ ((fun i => m i • b i) '' S) := by
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j ∈ S
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · simp [ht j hj]
    obtain ⟨k, hk⟩ := hle (Submodule.apply_mem_map₂ f (by simp [b.span_eq]) hc)
    exact ⟨k, by simpa using hk.symm⟩

variable {b S m f} {hm : ∀ i, 0 < m i} {hf : f.IsAlt}
  {h₁ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b i) (m j • b j) = k}
  {h₂ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b j) (m i • b i) = k}

@[simp]
theorem ofBasis_unfrozen :
    (ofBasis b S m f hm hf h₁ h₂).unfrozen = Submodule.span ℤ (b '' S) :=
  (rfl)

@[simp]
theorem ofBasis_sublattice :
    (ofBasis b S m f hm hf h₁ h₂).sublattice = Submodule.span ℤ (Set.range fun i => m i • b i) :=
  (rfl)

@[simp]
theorem ofBasis_form : (ofBasis b S m f hm hf h₁ h₂).form = f :=
  (rfl)

variable (b S m f hm hf h₁ h₂)

/-- The adapted basis `(b_i)` of `SkewLatticeDatum.ofBasis`, with unfrozen indices `S` and
multipliers `m_i`. -/
def AdaptedBasis.ofBasis (hm : ∀ i, 0 < m i) (hf : f.IsAlt)
    (h₁ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b i) (m j • b j) = k)
    (h₂ : ∀ i ∈ S, ∀ j, ∃ k : ℤ, f (b j) (m i • b i) = k) :
    (ofBasis b S m f hm hf h₁ h₂).AdaptedBasis κ where
  basis := b
  unfrozenIndex := S
  multiplier := m
  multiplier_pos := hm
  unfrozen_eq_span := rfl
  sublattice_eq_span := rfl

variable {b S m f hm hf h₁ h₂}

@[simp]
theorem AdaptedBasis.ofBasis_basis : (AdaptedBasis.ofBasis b S m f hm hf h₁ h₂).basis = b :=
  (rfl)

@[simp]
theorem AdaptedBasis.ofBasis_unfrozenIndex :
    (AdaptedBasis.ofBasis b S m f hm hf h₁ h₂).unfrozenIndex = S :=
  (rfl)

@[simp]
theorem AdaptedBasis.ofBasis_multiplier :
    (AdaptedBasis.ofBasis b S m f hm hf h₁ h₂).multiplier = m :=
  (rfl)

end OfBasis

end Mei.SkewLatticeDatum
