/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coorientation
public import Mei.Geometry.Convex.PolyhedralCochain.Sweep.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Normal

/-!
# Matching swept orientations with integral wall normals

The contraction orientation of a swept joint determines the positive side of
the resulting wall. Choose an integral normal whose real evaluation has exactly
that sign on every one-vector frame. Replacing a previously computed normal
with this oriented normal preserves all homogeneous wall spaces, because their
integral kernels agree. Thus homogeneous coefficients can be used with the
coorientation induced by the oriented sweep, without changing the coefficient.

This combines `OrientedCell.exists_integral_coorientation`, the contraction
orientation of `OrientedCell.sweep`, and
`DirectedWallSpaces.wall_eq_of_ker_eq`. It supplies the sign compatibility
between polyhedral sweeps and directed wall labels in the geometric correction
construction of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, proof of Theorem 2.6.
-/

public section

noncomputable section

open Set Module

namespace Mei.DirectedWallSpaces

variable {Γ Λ R L V : Type*} [AddCommMonoid Γ] [AddCommGroup Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Choose a normal agreeing with an oriented wall cell, while preserving every
homogeneous wall space associated to a previously chosen equation of its direction. -/
theorem exists_cooriented_normal (σ : OrientedCell h 1) (m₀ : Λ →+ ℤ)
    (h₀ : (h.realCharacter m₀).ker = (affineSpan ℝ σ.carrier).direction) :
    ∃ m : Λ →+ ℤ, m ≠ 0 ∧
      (h.realCharacter m).ker = (affineSpan ℝ σ.carrier).direction ∧
      (∀ v : V, SignType.sign (h.realCharacter m v) =
        σ.orientation.evalSign (fun _ : Fin 1 => v)) ∧
      ∀ n : Γ, H.wall n m = H.wall n m₀ := by
  obtain ⟨m, hm, hdir, hsign⟩ := σ.exists_integral_coorientation
  refine ⟨m, hm, hdir, hsign, fun n => H.wall_eq_of_ker_eq n hm ?_⟩
  ext v
  have he := SetLike.ext_iff.mp (hdir.trans h₀.symm) (i v)
  simpa only [LinearMap.mem_ker, h.realCharacter_apply, Int.cast_eq_zero,
    AddMonoidHom.mem_ker] using he

/-- A transverse oriented joint sweep admits an integral normal inducing its
contraction orientation and preserving the wall spaces of any equation for the
swept direction. The input normal need not be primitive or have the correct sign. -/
theorem exists_cooriented_sweep_normal (σ : OrientedCell h 2) (v : Λ)
    (hv : i v ∉ (affineSpan ℝ σ.carrier).direction) (m₀ : Λ →+ ℤ)
    (h₀ : (h.realCharacter m₀).ker =
      (affineSpan ℝ σ.carrier).direction ⊔ ℝ ∙ i v) :
    ∃ m : Λ →+ ℤ, m ≠ 0 ∧
      (h.realCharacter m).ker = (affineSpan ℝ σ.carrier).direction ⊔ ℝ ∙ i v ∧
      (∀ u : V, SignType.sign (h.realCharacter m u) =
        (σ.sweep v hv).orientation.evalSign (fun _ : Fin 1 => u)) ∧
      ∀ n : Γ, H.wall n m = H.wall n m₀ := by
  have hdir : (affineSpan ℝ (σ.sweep v hv).carrier).direction =
      (affineSpan ℝ σ.carrier).direction ⊔ ℝ ∙ i v := by
    rw [OrientedCell.sweep_carrier, direction_affineSpan, direction_affineSpan,
      Convex.vectorSpan_sweep σ.nonempty]
  obtain ⟨m, hm, hker, hsign, hwall⟩ :=
    H.exists_cooriented_normal (σ.sweep v hv) m₀ (h₀.trans hdir.symm)
  exact ⟨m, hm, hker.trans hdir, hsign, hwall⟩

end Mei.DirectedWallSpaces
