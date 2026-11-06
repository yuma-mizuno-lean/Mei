/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Toric.Algebraic.RationalFunctional
public import Mei.LinearAlgebra.FreeModule.Int
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Rational linear maps as rational multiples of integral maps

A real-linear map `T : V → V'` between real vector spaces with integral lattices `N → V` and
`N' → V'` is rational when it pulls rational functionals back to rational functionals. Such a map
is a rational multiple of the real extension of an integral map: `d • T` extends some additive
map `u : N → N'` for a positive integer `d` (`IsRationalLinearMap.exists_nsmul_eq_extend`).

If `T` is injective on a subspace `U` cut out by finitely many integral characters, it has a
rational left inverse on `U`: a rational real-linear map `B : V' → V` with `B (T v) = v` for
`v ∈ U` (`IsRationalLinearMap.exists_leftInvOn`). The subspace may be all of `V`, and no
condition on the ranks is needed. Rational multiples and differences of rational maps are
rational.
-/

public section

namespace Mei.Toric

open TauCeti.Toric

variable {N V N' V' : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

namespace IsRationalLinearMap

/-- Rational multiples of rational linear maps are rational. -/
theorem rat_smul {T : V →ₗ[ℝ] V'} (hT : IsRationalLinearMap h h' T) (q : ℚ) :
    IsRationalLinearMap h h' ((q : ℝ) • T) :=
  (isRationalLinearMap_iff h h' _).mpr fun f hf => by
    simpa [LinearMap.comp_smul] using (hT.map_functional hf).rat_smul q

/-- Differences of rational linear maps are rational. -/
theorem sub {S T : V →ₗ[ℝ] V'} (hS : IsRationalLinearMap h h' S)
    (hT : IsRationalLinearMap h h' T) : IsRationalLinearMap h h' (S - T) :=
  (isRationalLinearMap_iff h h' _).mpr fun f hf => by
    simpa [LinearMap.comp_sub] using (hS.map_functional hf).sub (hT.map_functional hf)

/-- A rational linear map is a rational multiple of the real extension of an integral map: some
positive integer multiple `d • T` extends an additive map `N →+ N'`. -/
theorem exists_nsmul_eq_extend {T : V →ₗ[ℝ] V'} (hT : IsRationalLinearMap h h' T) :
    ∃ d : ℕ, d ≠ 0 ∧ ∃ u : N →+ N', (d : ℝ) • T = h.extend i' u := by
  classical
  let := h'.free
  let := h'.finite
  let b := Module.Free.chooseBasis ℤ N'
  let c := h'.isBaseChange.basis b
  -- The coordinate functionals of the real basis are the real extensions of integral characters,
  -- so they pull back to rational multiples `q k • m k` of integral characters.
  have hc (k) : c.coord k = h'.realCharacter (b.coord k).toAddMonoidHom :=
    h'.eq_realCharacter fun n => by
      simpa [c] using IsBaseChange.basis_repr_comp_apply b h'.isBaseChange n k
  choose q m hqm using fun k => IsRationalFunctional.iff_exists_character.mp
    (hT.map_functional (hc k ▸ IsRationalFunctional.realCharacter h' (b.coord k)))
  -- A common denominator `d` of the `q k` makes `d * q k = z k` integral.
  let d := ∏ k, (q k).den
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => (q k).den_nz
  let z (k) : ℤ := (q k).num * (d / (q k).den : ℕ)
  have hz (k) : (z k : ℝ) = d * q k := by
    have hdvd : (q k).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    have hden : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
    have hzk : (z k : ℝ) = (q k).num * ((d / (q k).den : ℕ) : ℝ) := by
      simp only [z, Int.cast_mul, Int.cast_natCast]
    rw [Rat.cast_def, hzk, Nat.cast_div hdvd hden]
    field_simp
  let u : N →ₗ[ℤ] N' := ∑ k, (z k • m k).smulRight (b k)
  -- Compare the coordinates of `d • T (i n)` and `i' (u n)` in the real basis.
  refine ⟨d, hd, u.toAddMonoidHom, h.eq_extend fun n => c.ext_elem fun k => ?_⟩
  have hT' : c.repr (T (i n)) k = q k * m k n := by
    simpa using LinearMap.congr_fun (hqm k) (i n)
  have hu : c.repr (i' (u n)) k = z k * m k n := by
    simpa [c, u, Finsupp.single_apply, mul_comm] using
      IsBaseChange.basis_repr_comp_apply b h'.isBaseChange (u n) k
  simp [hT', hu, hz, mul_assoc]

/-- A rational linear map injective on the common kernel `U` of finitely many integral characters
`m j` has a rational left inverse on `U`. -/
theorem exists_leftInvOn {T : V →ₗ[ℝ] V'} (hT : IsRationalLinearMap h h' T) {κ : Type*}
    [Finite κ] (m : κ → Module.Dual ℤ N)
    (hinj : ∀ v, (∀ j, h.realCharacter (m j).toAddMonoidHom v = 0) → T v = 0 → v = 0) :
    ∃ B : V' →ₗ[ℝ] V, IsRationalLinearMap h' h B ∧
      Set.LeftInvOn B T {v | ∀ j, h.realCharacter (m j).toAddMonoidHom v = 0} := by
  classical
  let := Fintype.ofFinite κ
  let := h.free
  let := h.finite
  let := h'.free
  let := h'.finite
  obtain ⟨d, hd, u, hu⟩ := hT.exists_nsmul_eq_extend
  have hTi (n : N) : (d : ℝ) • T (i n) = i' (u n) := by simpa using LinearMap.congr_fun hu (i n)
  -- The integral map `n ↦ (u n, (m j n)_j)` is injective, so it has a left inverse `g` up to a
  -- nonzero factor `c`; its first block, rescaled, inverts `T` on `U`.
  let Φ : N →ₗ[ℤ] N' × (κ → ℤ) := u.toIntLinearMap.prod (LinearMap.pi m)
  have hΦ : Function.Injective Φ := (injective_iff_map_eq_zero Φ).mpr fun n hn => by
    have h₁ : u n = 0 := by simpa [Φ] using congrArg Prod.fst hn
    have h₂ (j) : m j n = 0 := by simpa [Φ] using congrFun (congrArg Prod.snd hn) j
    refine h.injective ((hinj (i n) (fun j => by simpa using h₂ j) ?_).trans (map_zero i).symm)
    have := hTi n
    rw [h₁, map_zero] at this
    exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hd)
  obtain ⟨c, hc, g, hg⟩ := LinearMap.exists_comp_eq_nsmul_id_of_injective_left hΦ
  let E := h'.extend i (g ∘ₗ LinearMap.inl ℤ N' (κ → ℤ)).toAddMonoidHom
  let F : V →ₗ[ℝ] V :=
    ∑ j, (h.realCharacter (m j).toAddMonoidHom).smulRight (i (g (0, Pi.single j 1)))
  have hEF : (d : ℝ) • (E ∘ₗ T) + F = (c : ℝ) • LinearMap.id := by
    have hg' (n : N) : g (Φ n) = c • n := by simpa using LinearMap.congr_fun hg n
    refine (h.eq_extend (i' := i) (f := c • AddMonoidHom.id N) fun n => ?_).trans
      (h.eq_extend (i' := i) (f := c • AddMonoidHom.id N) fun n => ?_).symm
    · have hsplit : Φ n = (u n, 0) + ∑ j, m j n • ((0 : N'), Pi.single j (1 : ℤ)) := by
        ext j
        · simp [Φ, Prod.fst_sum]
        · simp [Φ, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
      have hn := hg' n
      rw [hsplit, map_add, map_sum] at hn
      calc ((d : ℝ) • (E ∘ₗ T) + F) (i n)
          = i (g (u n, 0)) + ∑ j, m j n • i (g (0, Pi.single j 1)) := by
            simp [E, F, ← map_smul, hTi, Int.cast_smul_eq_zsmul]
        _ = i ((c • AddMonoidHom.id N) n) := by
            simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, ← hn, map_add, map_sum,
              map_zsmul]
    · simp only [LinearMap.smul_apply, LinearMap.id_apply, AddMonoidHom.smul_apply,
        AddMonoidHom.id_apply, map_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨((d / c : ℚ) : ℝ) • E, (IsRationalLinearMap.extend h' h _).rat_smul _, fun v hv => ?_⟩
  rw [Set.mem_ofPred_eq] at hv
  have := LinearMap.congr_fun hEF v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
    F, LinearMap.sum_apply, LinearMap.smulRight_apply, hv, zero_smul, Finset.sum_const_zero,
    add_zero] at this
  simp [div_eq_inv_mul, mul_smul, this, hc]

end IsRationalLinearMap

end Mei.Toric
