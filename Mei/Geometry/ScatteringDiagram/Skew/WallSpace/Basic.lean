/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Embedding
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Basic

/-!
# Principal directed wall spaces

The positive skew Lie algebra has directed wall spaces with spatial map
`n ↦ r(n) = (p₁*(n), n)`. A nonzero integral normal is eligible exactly when it
has the kernel of the normalized principal normal `κ(n)νₙ`. Its wall space is
then the whole homogeneous skew line. Radical degrees are retained, including
when the skew form is zero.

We construct the spaces inside the homogeneous pieces by inverse image under the
injective principal realization. The logarithmic directed-wall laws supply the
bracket law, without a separate computation of contracted normals. The realization
preserves these spaces, so their supported-ray labels can be realized in the
tropical vertex group.

The principal realization follows Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2.
We reuse `principalGradedLieHom`, `tropicalVertexWallSpaces` and Mathlib's
singleton-span and submodule inverse-image constructions.
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum

open LogarithmicVectorField

variable {N R : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [CommRing R] [Algebra ℚ R] (D : SkewLatticeDatum N)

local notation "Lpr" => Module.Dual ℤ D.sublattice × D.unfrozen

variable (d : PositiveDegrees D.unfrozen)

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d
local notation "H" => tropicalVertexWallSpaces (R := R)
  (D.principalPositiveDegrees d) (AddMonoidHom.id Lpr)
local notation "f" => D.principalGradedLieHom (R := R) d

/-- Principal wall spaces on the positive skew algebra. Degrees retain their
unfrozen indices, and their spatial directions are the principal exponents.
The homogeneous restriction excludes the kernel at degree zero. -/
def principalWallSpaces : DirectedWallSpaces D.principalEmbedding.toAddMonoidHom ℒ where
  wall n m := ℒ n ⊓ ((H).wall (D.principalEmbedding n) m).comap (f).toLieHom.toLinearMap
  wall_le_piece _ _ := inf_le_left
  zero_normal n := by
    rw [(H).zero_normal, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (D.principalGradedLieHom_injective d), inf_bot_eq]
  nontangent n m hm := by
    have hm' : m (D.principalEmbedding n) ≠ 0 := hm
    rw [(H).nontangent (D.principalEmbedding n) m hm', Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (D.principalGradedLieHom_injective d), inf_bot_eq]
  rescale n m c hc := by rw [(H).rescale _ m c hc]
  bracket_mem := by
    intro n n' m m' x y hx hy
    refine ⟨SetLike.GradedBracket.bracket_mem hx.1 hy.1, ?_⟩
    have ht := (H).bracket_mem hx.2 hy.2
    have he : wallBracketNormal (AddMonoidHom.id Lpr)
        (D.principalEmbedding n) (D.principalEmbedding n') m m' =
        wallBracketNormal D.principalEmbedding.toAddMonoidHom n n' m m' := by
      ext v
      simp
    apply Submodule.mem_comap.mpr
    simpa only [LieHom.coe_toLinearMap, LieHom.map_lie, map_add, he] using ht

/-- Membership is homogeneous membership together with membership of the
principal realization in the corresponding tropical vertex wall space. -/
theorem mem_principalWallSpaces_iff (n : D.unfrozen) (m : Lpr →+ ℤ)
    (x : SkewLieAlgebra.positiveLieAlgebra
      (D.coefficientForm R) (D.isAlt_coefficientForm R) d) :
    x ∈ (D.principalWallSpaces d).wall n m ↔
      x ∈ ℒ n ∧ f x ∈ (H).wall (D.principalEmbedding n) m := Iff.rfl

/-- An eligible principal normal retains the whole homogeneous skew piece.
Equality of kernels allows either coorientation and any nonzero rational rescaling. -/
theorem principalWallSpaces_wall_eq_piece {n : D.unfrozen}
    {m : Lpr →+ ℤ} (hk : m.ker = (D.principalNormal n).toAddMonoidHom.ker) :
    (D.principalWallSpaces (R := R) d).wall n m = ℒ n := by
  apply le_antisymm ((D.principalWallSpaces d).wall_le_piece n m)
  intro x hx
  refine (D.mem_principalWallSpaces_iff d n m x).mpr ⟨hx, ?_⟩
  rw [(H).wall_eq_of_ker_eq (D.principalEmbedding n) hk,
    mem_tropicalVertexWallSpaces_iff,
    wallSubmodule_of_tangent _ _ _ (by simp), D.span_principalNormalField n]
  rw [coe_principalGradedLieHom_apply]
  exact D.principalLieHom_mem_span_principalField
    ((SkewLieAlgebra.mem_positiveGrading_iff _ _ d n x).mp hx)

/-- A principal wall element with nonzero coefficient determines the kernel
of its integral normal, even over coefficient algebras with zero divisors. -/
theorem ker_eq_of_mem_principalWallSpaces {n : D.unfrozen}
    {m : Lpr →+ ℤ}
    {x : SkewLieAlgebra.positiveLieAlgebra
      (D.coefficientForm R) (D.isAlt_coefficientForm R) d}
    (hx : x ∈ (D.principalWallSpaces d).wall n m) (hx0 : x ≠ 0) :
    m.ker = (D.principalNormal n).toAddMonoidHom.ker := by
  have hfx : (f x).val ≠ 0 := by
    intro h
    apply hx0
    apply D.principalGradedLieHom_injective d
    simpa using (Subtype.ext h : f x = 0)
  have ht := (H).normal_apply_eq_zero hx.2
    (fun h => hfx (congrArg Subtype.val h))
  obtain ⟨r, hr⟩ := (mem_tropicalVertexWallSpaces_iff_of_tangent
    _ _ _ m ht (f x)).mp hx.2
  have hp : (f x).val ∈ R ∙ D.principalField n := by
    rw [coe_principalGradedLieHom_apply]
    exact D.principalLieHom_mem_span_principalField
      ((SkewLieAlgebra.mem_positiveGrading_iff _ _ d n x).mp hx.1)
  rw [← D.span_principalNormalField n] at hp
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hp
  have hr0 : r ≠ 0 := by
    intro h
    exact hfx (by simpa [h] using hr.symm)
  have hs0 : s ≠ 0 := by
    intro h
    exact hfx (by simpa [h] using hs.symm)
  have he : r • (Int.castAddHom R).comp m =
      s • (Int.castAddHom R).comp (D.principalNormal n).toAddMonoidHom := by
    apply single_injective (AddMonoidHom.id Lpr) (D.principalEmbedding n)
    simpa only [map_smul] using hr.trans hs.symm
  -- Torsion-free integer scalars cancel even when R has zero divisors.
  let := HasUniqueDiv.of_module_rat R
  have cancel (a : R) (ha : a ≠ 0) (z : ℤ) (hz : a * (z : R) = 0) : z = 0 := by
    exact (IsAddTorsionFree.zsmul_eq_zero_iff_left ha).mp
      (by simpa only [zsmul_eq_mul'] using hz)
  ext v
  simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
  have hv := DFunLike.congr_fun he v
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply,
    Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul,
    LinearMap.toAddMonoidHom_coe] at hv
  constructor
  · intro hm
    apply cancel s hs0 (D.principalNormal n v)
    simpa only [hm, Int.cast_zero, mul_zero] using hv.symm
  · intro hm
    apply cancel r hr0 (m v)
    simpa only [hm, Int.cast_zero, mul_zero] using hv

/-- Normals outside the principal normal line carry no skew wall coefficients. -/
theorem principalWallSpaces_wall_eq_bot {n : D.unfrozen}
    {m : Lpr →+ ℤ} (hk : m.ker ≠ (D.principalNormal n).toAddMonoidHom.ker) :
    (D.principalWallSpaces (R := R) d).wall n m = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hx0
  exact hk (D.ker_eq_of_mem_principalWallSpaces d hx hx0)

open Classical in
/-- The complete principal wall-space formula: each eligible normal carries the
whole homogeneous skew piece, and all other normals carry zero. At degree zero
both alternatives are zero by positivity. -/
@[simp]
theorem principalWallSpaces_wall (n : D.unfrozen) (m : Lpr →+ ℤ) :
    (D.principalWallSpaces (R := R) d).wall n m =
      if m ≠ 0 ∧ m.ker = (D.principalNormal n).toAddMonoidHom.ker then ℒ n else ⊥ := by
  classical
  by_cases hn : n = 0
  · subst n
    have hpiece : ℒ (0 : D.unfrozen) = ⊥ :=
      IsPositiveGrading.eq_bot (d := d) _ (Or.inr rfl)
    have hw := (D.principalWallSpaces (R := R) d).wall_le_piece 0 m
    rw [hpiece] at hw
    simp [hpiece, eq_bot_iff.mpr hw]
  by_cases hm : m = 0
  · subst m
    simp [(D.principalWallSpaces d).zero_normal]
  by_cases hk : m.ker = (D.principalNormal n).toAddMonoidHom.ker
  · rw [ite_eq_left ⟨hm, hk⟩, D.principalWallSpaces_wall_eq_piece d hk]
  · rw [ite_eq_right (by tauto), D.principalWallSpaces_wall_eq_bot d hk]

end Mei.SkewLatticeDatum
