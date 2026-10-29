/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Basic
public import Mei.Geometry.Affine.Codimension
public import Mei.Geometry.Toric.Algebraic.DualLattice
public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Recession
public import Mathlib.Basic.Sign.Defs

/-!
# Pulling back cones along an integral skew form

An integral skew form defines a real comparison map from a lattice space to its
continuous dual. Its kernel is the real radical, described by the common kernels
of the extended integral rows. Pulling a rational cone back along this map gives
a rational-normal polyhedron. Its recession directions are detected by membership
of their images in the original cone, even when the form is degenerate.

For a set in the evaluation hyperplane of an unfrozen degree, the pulled-back
normal is the real extension of `{-, κ(n)n}`. If this normal is nonzero and the
pullback has codimension one, it cuts out exactly the affine direction of the
pullback. The normalized normal preserves evaluation signs, including tangencies.
These are the geometric support and incomingness comparisons used to
pass from conical to directed walls.

We use `LinearMap.codRestrict₂`, `IsIntegralLattice.extend`, the integral dual
lattice, `PointedCone.comap` and rational polyhedral preimages. The comparison
follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1 and Appendix B (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Remark 2.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

open Set

namespace Mei.SkewLatticeDatum

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  (D : SkewLatticeDatum N)
  (hD : ∀ a b, ∃ k : ℤ, D.form a b = k)
  {i : N →+ V} (h : TauCeti.Toric.IsIntegralLattice i)

/-- The real comparison map extending the integral skew character into the
continuous dual of the lattice space. -/
def skewComparison : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
  h.extend h.continuousRealCharacter
    (LinearMap.toAddMonoidHom'.comp (D.integralCharacter hD).toAddMonoidHom)

/-- On lattice vectors, the comparison is the extended integral character. -/
@[simp]
theorem skewComparison_lattice (n : N) :
    D.skewComparison hD h (i n) =
      h.continuousRealCharacter (D.integralCharacter hD n).toAddMonoidHom := by
  simp [skewComparison]

/-- Pulling evaluation at a lattice vector back along the comparison gives the
extended column of the integral form. -/
theorem eval_comp_skewComparison (n : N) :
    ((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap).comp
        (D.skewComparison hD h) =
      h.realCharacter ((D.integralCharacter hD).flip n).toAddMonoidHom := by
  apply h.eq_realCharacter
  intro a
  simp

/-- The kernel is the real radical: it is the common kernel of all extended
columns of the form. This includes the entire space when the form is zero. -/
theorem mem_ker_skewComparison_iff (x : V) :
    x ∈ LinearMap.ker (D.skewComparison hD h) ↔
      ∀ n : N, h.realCharacter ((D.integralCharacter hD).flip n).toAddMonoidHom x = 0 := by
  constructor
  · intro hx n
    rw [← D.eval_comp_skewComparison hD h n, LinearMap.comp_apply,
      LinearMap.mem_ker.mp hx]
    rfl
  · intro hx
    apply LinearMap.mem_ker.mpr
    have he : (D.skewComparison hD h x).toLinearMap = 0 := by
      apply h.isBaseChange.algHom_ext
      intro n
      have hn := LinearMap.congr_fun (D.eval_comp_skewComparison hD h n) x
      simpa using hn.trans (hx n)
    ext y
    exact LinearMap.congr_fun he y

/-- Comparison is skew on all real vectors, including radical vectors. -/
theorem skewComparison_swap (x y : V) :
    D.skewComparison hD h x y = -D.skewComparison hD h y x := by
  have he (n : N) :
      (D.skewComparison hD h (i n)).toLinearMap =
        -((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap.comp
          (D.skewComparison hD h)) := by
    apply h.isBaseChange.algHom_ext
    intro a
    simpa only [AddMonoidHom.coe_toIntLinearMap, ContinuousLinearMap.coe_coe,
      LinearMap.neg_apply, LinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      skewComparison_lattice, TauCeti.Toric.IsIntegralLattice.continuousRealCharacter_apply,
      TauCeti.Toric.IsIntegralLattice.realCharacter_apply, LinearMap.toAddMonoidHom_coe,
      Int.cast_neg] using
      congrArg (Int.cast (R := ℝ)) (D.integralCharacter_swap hD a n)
  have hx : (D.skewComparison hD h x).toLinearMap =
      -((ContinuousLinearMap.apply ℝ ℝ x).toLinearMap.comp (D.skewComparison hD h)) := by
    apply h.isBaseChange.algHom_ext
    intro n
    have hn := LinearMap.congr_fun (he n) x
    have hn' : D.skewComparison hD h (i n) x = -D.skewComparison hD h x (i n) := hn
    simpa using (congrArg Neg.neg hn').symm
  exact LinearMap.congr_fun hx y

/-- Every real vector annihilates its own comparison image. -/
@[simp]
theorem skewComparison_self (x : V) : D.skewComparison hD h x x = 0 := by
  have he := D.skewComparison_swap hD h x x
  linarith

/-- The comparison is rational for the integral dual lattice. -/
theorem isRationalLinearMap_skewComparison :
    Toric.IsRationalLinearMap h h.continuousDual (D.skewComparison hD h) :=
  Toric.IsRationalLinearMap.extend h h.continuousDual _

/-- Inverse images of rational-normal polyhedra under the skew comparison are
rational-normal, without a nondegeneracy hypothesis. -/
theorem isRationalNormalPolyhedron_skewComparison_preimage {P : Set (V →L[ℝ] ℝ)}
    (hP : IsRationalNormalPolyhedron h.continuousDual P) :
    IsRationalNormalPolyhedron h ((D.skewComparison hD h) ⁻¹' P) := by
  let := h.finiteDimensional
  exact hP.preimage
    (LinearMap.toContinuousLinearMap (D.skewComparison hD h)).toContinuousAffineMap
    (D.isRationalLinearMap_skewComparison hD h)

/-- A cone pullback has precisely the recession directions whose comparison
images lie in the cone. This is the KS-incoming versus directed-incoming test. -/
@[simp high] -- Compute cone preimages before the generic recession predicate unfolds.
theorem mem_recessionCone_skewComparison_preimage (σ : PointedCone ℝ (V →L[ℝ] ℝ))
    (x : V) :
    x ∈ recessionCone ((D.skewComparison hD h) ⁻¹' (σ : Set (V →L[ℝ] ℝ))) ↔
      D.skewComparison hD h x ∈ σ := by
  rw [← PointedCone.coe_comap, PointedCone.recessionCone_coe, PointedCone.mem_comap]

/-- The primitive-degree normalized normal pulls back with its ray-index factor,
which is positive when `n ≠ 0` and zero when `n = 0`. The comparison may have a
kernel and the pulled-back normal may vanish. -/
theorem realCharacter_normal_eq_smul_eval_comp_skewComparison
    {n : N} (hn : n ∈ D.unfrozen) :
    let _ := h.free
    h.realCharacter (D.normal n hn).toAddMonoidHom =
      (D.sublattice.toAddSubgroup.rayIndex n : ℝ) •
        (((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap).comp
          (D.skewComparison hD h)) := by
  let := h.free
  dsimp only
  symm
  apply h.eq_realCharacter
  intro a
  simp only [LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply,
    skewComparison_lattice, TauCeti.Toric.IsIntegralLattice.continuousRealCharacter_apply,
    TauCeti.Toric.IsIntegralLattice.realCharacter_apply, smul_eq_mul,
    LinearMap.toAddMonoidHom_coe]
  have he := D.cast_normal_apply hn a
  rw [← D.cast_integralCharacter_apply hD a n] at he
  exact_mod_cast he.symm

/-- A set in a degree evaluation hyperplane pulls back into the kernel of the
normalized integral skew normal. -/
theorem skewComparison_preimage_subset_ker_normal {n : N} (hn : n ∈ D.unfrozen)
    (σ : Set (V →L[ℝ] ℝ))
    (hσ : ∀ θ ∈ σ, θ (i n) = 0) :
    let _ := h.free
    (D.skewComparison hD h) ⁻¹' σ ⊆
      LinearMap.ker (h.realCharacter (D.normal n hn).toAddMonoidHom) := by
  let := h.free
  dsimp only
  intro x hx
  apply LinearMap.mem_ker.mpr
  rw [D.realCharacter_normal_eq_smul_eval_comp_skewComparison hD h hn]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply, smul_eq_mul]
  rw [hσ _ hx, mul_zero]

/-- If the pulled-back normal is nonzero and the set pullback has codimension
one, this normal cuts out exactly its affine direction, giving the affine-direction
condition for a directed wall. Rational-normal polyhedrality additionally requires
`IsRationalNormalPolyhedron h.continuousDual σ` and follows from
`isRationalNormalPolyhedron_skewComparison_preimage`. -/
theorem direction_skewComparison_preimage {n : N} (hn : n ∈ D.unfrozen)
    (σ : Set (V →L[ℝ] ℝ))
    (hσ : ∀ θ ∈ σ, θ (i n) = 0)
    (hnormal : let _ := h.free; D.normal n hn ≠ 0)
    (hcodim : Module.finrank ℝ (affineSpan ℝ
      ((D.skewComparison hD h) ⁻¹' σ)).direction + 1 =
        Module.finrank ℝ V) :
    let _ := h.free
    (affineSpan ℝ ((D.skewComparison hD h) ⁻¹' σ)).direction =
      LinearMap.ker (h.realCharacter (D.normal n hn).toAddMonoidHom) := by
  let := h.free
  dsimp only
  let := h.finiteDimensional
  have hne : h.realCharacter (D.normal n hn).toAddMonoidHom ≠ 0 := by
    intro hz
    apply hnormal
    apply LinearMap.toAddMonoidHom_injective
    exact h.realCharacter_injective (hz.trans (map_zero _).symm)
  exact (LinearMap.ker_eq_direction_affineSpan _ hne
    (fun _ hx => LinearMap.mem_ker.mp
      (D.skewComparison_preimage_subset_ker_normal hD h hn σ hσ hx)) hcodim).symm

/-- The normalized skew normal and the evaluation normal give the same sign
on every vector, including tangencies. Nondegeneracy is unnecessary. -/
theorem sign_realCharacter_normal_eq_sign_eval_skewComparison
    {n : N} (hn : n ∈ D.unfrozen) (hn0 : n ≠ 0) (v : V) :
    let _ := h.free
    SignType.sign (h.realCharacter (D.normal n hn).toAddMonoidHom v) =
      SignType.sign (D.skewComparison hD h v (i n)) := by
  let := h.free
  dsimp only
  rw [D.realCharacter_normal_eq_smul_eval_comp_skewComparison hD h hn]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.apply_apply, smul_eq_mul, sign_mul]
  have hp : (0 : ℝ) < D.sublattice.toAddSubgroup.rayIndex n :=
    Rat.cast_pos.mpr (D.sublattice.toAddSubgroup.rayIndex_pos hn0)
  rw [sign_pos hp, one_mul]

end Mei.SkewLatticeDatum
