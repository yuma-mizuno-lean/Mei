/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mei.LinearAlgebra.Dual.Kernel
public import Mei.LinearAlgebra.FreeModule.Int

/-!
# Indices of dual lattices

Let `M₀` be a sublattice of finite index `ℓ` in a finite free `ℤ`-module `M`. Restricting
functionals identifies the dual lattice `N = Dual ℤ M` with a sublattice of `N₀ = Dual ℤ M₀`,
and this sublattice again has index `ℓ`. More generally, the transpose of any map between
lattices of equal rank has the same image index as the original map. For injective maps,
both indices are the absolute value of one determinant; for singular maps, both are zero.

For a primitive vector `m₀` of `M₀`, write `m₀ = r • m` with `m` primitive in `M` and `r > 0`.
Evaluation at `m₀` maps `N₀` onto `ℤ` and `N` onto `rℤ`, so
`ℓ = r · [m₀⊥ ∩ N₀ : m₀⊥ ∩ N]`. In rank two, for `m₀ ≠ 0`, the annihilators `m₀⊥ ∩ N₀`
and `m₀⊥ ∩ N` are lines, and the primitive normal of `ℝ m₀` in `N` is
`±[m₀⊥ ∩ N₀ : m₀⊥ ∩ N]` times the primitive normal in `N₀`.

These identities compare scattering diagrams over a lattice and over a finite-index
sublattice: in Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.5, the index `ℓ` splits into the exponent `r` of the wall function and the ratio
of primitive normals.

## Main results

* `LinearMap.dualMap_injective_of_injective`: the transpose of an injective map between finite
  free `ℤ`-modules of equal rank is injective.
* `LinearMap.index_range_dualMap`: the image of the transpose has the same index as the image
  of the map.
* `Submodule.index_range_dualRestrict`: the dual of a sublattice of finite index `ℓ` contains
  the dual of the ambient lattice with index `ℓ`.
* `Submodule.index_eq_mul_relIndex_ker_eval`: `ℓ = r · [m₀⊥ ∩ N₀ : m₀⊥ ∩ N]`.
* `Submodule.exists_dualRestrict_eq_zsmul_natAbs_eq_relIndex`: in rank two, the restricted
  primitive normal is a multiple of the primitive normal of `N₀` by `±[m₀⊥ ∩ N₀ : m₀⊥ ∩ N]`.
-/

public section

open Module

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module.Free ℤ M] [Module.Finite ℤ M]
  [Module.Free ℤ N] [Module.Finite ℤ N]

omit [Module.Free ℤ M] [Module.Finite ℤ M] in
/-- The transpose of an injective map into a finite free `ℤ`-module of the same rank is
injective. -/
theorem dualMap_injective_of_injective {f : M →ₗ[ℤ] N} (hf : Function.Injective f)
    (hrank : finrank ℤ M = finrank ℤ N) : Function.Injective f.dualMap := by
  obtain ⟨c, hc, g, hfg, -⟩ := exists_comp_eq_nsmul_id_of_injective hf hrank
  rw [← ker_eq_bot, Submodule.eq_bot_iff]
  intro φ hφ
  ext y
  have h : φ ((f ∘ₗ g) y) = 0 := by
    simpa using LinearMap.congr_fun (mem_ker.mp hφ) (g y)
  simpa [hfg, hc] using h

/-- The image of the transpose of a map between finite free `ℤ`-modules of equal rank has
the same index as the image of the map, including index zero for singular maps. -/
@[simp]
theorem index_range_dualMap {f : M →ₗ[ℤ] N}
    (hrank : finrank ℤ M = finrank ℤ N) :
    (range f.dualMap).toAddSubgroup.index = (range f).toAddSubgroup.index := by
  classical
  let b := Free.chooseBasis ℤ M
  let e : Free.ChooseBasisIndex ℤ N ≃ Free.ChooseBasisIndex ℤ M :=
    Fintype.equivOfCardEq <| by
      rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex, hrank]
  let c := (Free.chooseBasis ℤ N).reindex e
  by_cases hf : Function.Injective f
  · rw [index_range_eq_natAbs_det_toMatrix c.dualBasis b.dualBasis
        (dualMap_injective_of_injective hf hrank),
      index_range_eq_natAbs_det_toMatrix b c hf, dualMap_def, toMatrix_transpose,
      Matrix.det_transpose]
  · have hdualrank : finrank ℤ (Dual ℤ N) = finrank ℤ (Dual ℤ M) := by
      simpa only [← c.toDualEquiv.finrank_eq, ← b.toDualEquiv.finrank_eq] using hrank.symm
    have hdual : ¬Function.Injective f.dualMap := by
      intro h
      have hbidual := dualMap_injective_of_injective h hdualrank
      apply hf
      intro x y hxy
      apply (bijective_dual_eval ℤ M).injective
      apply hbidual
      ext φ
      simpa using congrArg φ hxy
    rw [(index_range_eq_zero_iff hdualrank).mpr hdual,
      (index_range_eq_zero_iff hrank).mpr hf]

end LinearMap

namespace Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- The restriction of functionals to a sublattice `M₀` of finite index identifies `Dual ℤ M`
with a sublattice of `Dual ℤ M₀` of the same index. -/
@[simp]
theorem index_range_dualRestrict (M₀ : Submodule ℤ M) [M₀.toAddSubgroup.FiniteIndex] :
    (LinearMap.range M₀.dualRestrict).toAddSubgroup.index = M₀.toAddSubgroup.index := by
  have hrank : finrank ℤ M₀ = finrank ℤ M := AddSubgroup.finrank_eq_of_finiteIndex M₀.toAddSubgroup
  rw [dualRestrict_def, LinearMap.index_range_dualMap hrank, range_subtype]

/-- Let `M₀` be a sublattice of finite index `ℓ` and `m₀` a primitive vector of `M₀` with
`m₀ = r • m` for a primitive vector `m` of `M`. Viewing `Dual ℤ M` inside `Dual ℤ M₀` by
restriction, `ℓ = r · [m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ M]`: evaluation at `m₀` maps
`Dual ℤ M₀` onto `ℤ` and `Dual ℤ M` onto `rℤ`. -/
theorem index_eq_mul_relIndex_ker_eval (M₀ : Submodule ℤ M) [M₀.toAddSubgroup.FiniteIndex]
    {m₀ : M₀} (hm₀ : TauCeti.IsPrimitive m₀) {m : M} (hm : TauCeti.IsPrimitive m) {r : ℕ}
    (hr : (m₀ : M) = r • m) :
    M₀.toAddSubgroup.index = r * (LinearMap.range M₀.dualRestrict).toAddSubgroup.relIndex
      (LinearMap.ker (Dual.eval ℤ M₀ m₀)).toAddSubgroup := by
  set H := (LinearMap.range M₀.dualRestrict).toAddSubgroup
  set K := (LinearMap.ker (Dual.eval ℤ M₀ m₀)).toAddSubgroup
  set ev := (Dual.eval ℤ M₀ m₀).toAddMonoidHom
  obtain ⟨g₀, hg₀⟩ := TauCeti.isPrimitive_def.mp hm₀
  obtain ⟨g, hg⟩ := TauCeti.isPrimitive_def.mp hm
  have hev : Function.Surjective ev := fun k => ⟨k • g₀, by simp [ev, hg₀]⟩
  have hker : ev.ker = K := by ext; simp [ev, K]
  have hmap : H.map ev = AddSubgroup.zmultiples (r : ℤ) := by
    ext k
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_zmultiples_iff, H, mem_toAddSubgroup,
      LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
      exact ⟨ψ m, by simp [ev, hr, mul_comm]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j • g, rfl⟩, by simp [ev, hr, hg]⟩
  have hsup : (H ⊔ K).index = r := by
    rw [← hker, ← mul_one (H ⊔ ev.ker).index, ← AddSubgroup.index_top (G := ℤ),
      ← ev.range_eq_top_of_surjective hev, ← AddSubgroup.index_map, hmap,
      Int.index_zmultiples, Int.natAbs_natCast]
  rw [← index_range_dualRestrict M₀, ← AddSubgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ K),
    AddSubgroup.relIndex_sup_left, hsup, mul_comm]

/-- In rank at most two, let `M₀` be a sublattice and `m₀` a nonzero vector of `M₀`. If
`n₀ ∈ Dual ℤ M₀` and `n ∈ Dual ℤ M` are primitive and vanish at `m₀`, then the restriction
of `n` to `M₀` is `k • n₀` with `|k| = [m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ M]`: the primitive
normals of the line through `m₀` differ by this index, up to sign. -/
theorem exists_dualRestrict_eq_zsmul_natAbs_eq_relIndex (hM : finrank ℤ M ≤ 2)
    (M₀ : Submodule ℤ M) {m₀ : M₀} (hm₀ : m₀ ≠ 0)
    {n₀ : Dual ℤ M₀} (hn₀ : TauCeti.IsPrimitive n₀) (hn₀m₀ : n₀ m₀ = 0)
    {n : Dual ℤ M} (hn : TauCeti.IsPrimitive n) (hnm₀ : n m₀ = 0) :
    ∃ k : ℤ, M₀.dualRestrict n = k • n₀ ∧
      k.natAbs = (LinearMap.range M₀.dualRestrict).toAddSubgroup.relIndex
        (LinearMap.ker (Dual.eval ℤ M₀ m₀)).toAddSubgroup := by
  -- the annihilators of `m₀` in both dual lattices are the lines of the primitive normals
  have hK₀ : LinearMap.ker (Dual.eval ℤ M₀ m₀) = ℤ ∙ n₀ := by
    refine LinearMap.ker_eq_span_singleton_of_isPrimitive ?_ ?_ hn₀ hn₀m₀
    · rw [← (Free.chooseBasis ℤ M₀).toDualEquiv.finrank_eq]
      exact M₀.finrank_le.trans hM
    · intro h
      exact hm₀ <| (forall_dual_apply_eq_zero_iff ℤ m₀).mp fun φ => LinearMap.congr_fun h φ
  have hm₀' : (m₀ : M) ≠ 0 := by simpa using hm₀
  have hK : LinearMap.ker (Dual.eval ℤ M (m₀ : M)) = ℤ ∙ n := by
    refine LinearMap.ker_eq_span_singleton_of_isPrimitive ?_ ?_ hn hnm₀
    · rw [← (Free.chooseBasis ℤ M).toDualEquiv.finrank_eq]
      exact hM
    · intro h
      exact hm₀' <| (forall_dual_apply_eq_zero_iff ℤ (m₀ : M)).mp fun φ => LinearMap.congr_fun h φ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k • n₀ = M₀.dualRestrict n := by
    rw [← Submodule.mem_span_singleton, ← hK₀]
    simpa using hnm₀
  refine ⟨k, hk.symm, ?_⟩
  have hinf : (LinearMap.range M₀.dualRestrict).toAddSubgroup ⊓
      (LinearMap.ker (Dual.eval ℤ M₀ m₀)).toAddSubgroup = AddSubgroup.zmultiples (k • n₀) := by
    ext φ
    simp only [AddSubgroup.mem_inf, mem_toAddSubgroup, LinearMap.mem_range, LinearMap.mem_ker,
      Dual.eval_apply, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨⟨ψ, rfl⟩, hψ⟩
      have : ψ ∈ ℤ ∙ n := hK ▸ by simpa using hψ
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp this
      exact ⟨a, by rw [map_zsmul, ← hk]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a • n, by rw [map_zsmul, ← hk]⟩, by simp [hn₀m₀]⟩
  have horder : addOrderOf n₀ = 0 :=
    addOrderOf_eq_zero_iff.mpr (injective_zsmul_iff_not_isOfFinAddOrder.mp hn₀.zsmul_left_injective)
  have hidx : (AddSubgroup.zmultiples (k • n₀)).relIndex (AddSubgroup.zmultiples n₀) =
      k.natAbs := by
    simpa [horder] using AddSubgroup.relIndex_zmultiples_zsmul_zsmul n₀ k 1
  rw [← AddSubgroup.inf_relIndex_right, hinf, hK₀, span_singleton_toAddSubgroup_eq_zmultiples,
    hidx]

end Submodule

/-! ### A sublattice of index two in `ℤ²` -/

-- `m₁ = (1, 0)` and `m₂ = (1, 2)` span a sublattice `M₀` of index `ℓ = 2`, and
-- `m₀ = m₁ + m₂ = 2 • (1, 1)` has `r = 2`, so `[m₀⊥ ∩ Dual ℤ M₀ : m₀⊥ ∩ Dual ℤ ℤ²] = 1`.
example (m₀ : Submodule.span ℤ (Set.range ![![(1 : ℤ), 0], ![1, 2]]))
    (hm₀ : (m₀ : Fin 2 → ℤ) = ![2, 2]) :
    (Submodule.span ℤ (Set.range ![![(1 : ℤ), 0], ![1, 2]])).toAddSubgroup.index = 2 ∧
      (LinearMap.range (Submodule.span ℤ (Set.range ![![(1 : ℤ), 0], ![1, 2]])).dualRestrict
        ).toAddSubgroup.relIndex (LinearMap.ker (Dual.eval ℤ _ m₀)).toAddSubgroup = 1 := by
  have hli : LinearIndependent ℤ ![![(1 : ℤ), 0], ![1, 2]] := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero (A := !![(1 : ℤ), 0; 1, 2])
      (by norm_num [Matrix.det_fin_two])
  let bN := Basis.span hli
  have h0 : (bN 0 : Fin 2 → ℤ) = ![1, 0] := by simp [bN, Basis.span_apply]
  have h1 : (bN 1 : Fin 2 → ℤ) = ![1, 2] := by simp [bN, Basis.span_apply]
  obtain rfl : m₀ = bN 0 + bN 1 := by
    ext i
    fin_cases i <;> simp [hm₀, h0, h1]
  have hidx :
      (Submodule.span ℤ (Set.range ![![(1 : ℤ), 0], ![1, 2]])).toAddSubgroup.index = 2 := by
    have hdet : (Pi.basisFun ℤ (Fin 2)).det ((↑) ∘ bN) = 2 := by
      rw [Basis.det_apply]
      simp [Matrix.det_fin_two, Basis.toMatrix_apply, h0, h1]
    -- the cardinality of the quotient module is by definition the index
    have := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin 2)) _ bN
    rw [hdet] at this
    exact this.symm
  have : (Submodule.span ℤ (Set.range ![![(1 : ℤ), 0], ![1, 2]])).toAddSubgroup.FiniteIndex :=
    ⟨by omega⟩
  have hm₀ : TauCeti.IsPrimitive (bN 0 + bN 1) := by
    simpa using bN.isPrimitive_zsmul_add_zsmul (i := 0) (j := 1) (p := 1) (q := 1) (by decide)
      isCoprime_one_left
  have hm : TauCeti.IsPrimitive (![1, 1] : Fin 2 → ℤ) :=
    TauCeti.isPrimitive_def.mpr ⟨(Pi.basisFun ℤ (Fin 2)).coord 0, by simp⟩
  have hr : ((bN 0 + bN 1 : _) : Fin 2 → ℤ) = (2 : ℕ) • ![1, 1] := by
    rw [Submodule.coe_add, h0, h1]
    ext i
    fin_cases i <;> simp
  have := Submodule.index_eq_mul_relIndex_ker_eval _ hm₀ hm hr
  refine ⟨hidx, ?_⟩
  omega
