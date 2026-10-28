/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Realization

/-!
# Primitive principal normals

The normalized principal normal `κ(n)νₙ` is primitive for every nonzero unfrozen
exponent, even when the skew form vanishes on that exponent. Its integral
normalization agrees with the rational evaluation character of the principal
logarithmic field. These results supply primitive coorientations and compare the
integral wall normals with their coefficient-valued logarithmic characters.

The normalization is that of Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2. We use the ray-index
membership criterion and Mathlib's dual evaluation map.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] (D : SkewLatticeDatum N)

/-- The integral principal normal is primitive for each nonzero unfrozen exponent.
The sublattice freeness assumption follows automatically from finite ambient rank. -/
theorem isPrimitive_principalNormal [Module.Free ℤ D.sublattice]
    {n : D.unfrozen} (hn : n ≠ 0) : TauCeti.IsPrimitive (D.principalNormal n) := by
  let : Module.Free ℤ D.sublattice.toAddSubgroup :=
    inferInstanceAs (Module.Free ℤ D.sublattice)
  have hnN : (n : N) ≠ 0 := fun h => hn (Subtype.ext h)
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp
    (D.sublattice.toAddSubgroup.isPrimitive_rayVector
      (D.sublattice.toAddSubgroup.rayIndex_pos hnN))
  refine TauCeti.isPrimitive_def.mpr
    ⟨Module.Dual.eval ℤ _ (f, (0 : D.unfrozen)), ?_⟩
  simpa only [Module.Dual.eval_apply, principalNormal_apply] using hf

/-- Casting the normalized integral normal to coefficients multiplies the rational
principal evaluation character by the ray index `κ(n)`. -/
theorem intCast_principalNormal_apply {R : Type*} [CommRing R] [Algebra ℚ R]
    (n : D.unfrozen) (x : Module.Dual ℤ D.sublattice × D.unfrozen) :
    (D.principalNormal n x : R) =
      algebraMap ℚ R (D.sublattice.toAddSubgroup.rayIndex n) *
        D.principalEvaluation (R := R) n x := by
  have heval : (D.principalNormal n x : ℚ) =
      D.sublattice.toAddSubgroup.rayIndex n * D.principalEvaluation (R := ℚ) n x := by
    let I := D.sublattice.toAddSubgroup.index
    let κ := D.sublattice.toAddSubgroup.rayIndex n
    have hi : (I : ℚ) ≠ 0 := by
      exact_mod_cast (AddSubgroup.index_ne_zero (H := D.sublattice.toAddSubgroup))
    have hd : (κ.den : ℚ) ≠ 0 := by positivity
    have he : (κ.den : ℤ) • (I • D.sublattice.toAddSubgroup.rayVector n) =
        κ.num • (⟨I • (n : N), D.sublattice.toAddSubgroup.nsmul_index_mem n⟩ :
          D.sublattice) := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_zsmul, AddSubgroup.coe_nsmul, Submodule.coe_smul_of_tower]
      rw [smul_comm, D.sublattice.toAddSubgroup.den_rayIndex_zsmul_rayVector,
        smul_comm]
    have hφ := congrArg x.1 he
    simp only [map_zsmul, map_nsmul, zsmul_eq_mul, nsmul_eq_mul] at hφ
    have hφQ : (κ.den : ℚ) * (I * (x.1 (D.sublattice.toAddSubgroup.rayVector n) : ℚ)) =
        κ.num * (x.1 ⟨I • (n : N), D.sublattice.toAddSubgroup.nsmul_index_mem n⟩ : ℚ) := by
      exact_mod_cast hφ
    dsimp only [κ, I] at hφQ
    rw [principalNormal_apply, principalEvaluation_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Rat.num_div_den (D.sublattice.toAddSubgroup.rayIndex n)]
    dsimp only [κ, I] at hi hd ⊢
    field_simp
    nlinarith [hφQ]
  have h := congrArg (algebraMap ℚ R) heval
  simpa only [map_intCast, map_mul, principalEvaluation_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using h

end Mei.SkewLatticeDatum
