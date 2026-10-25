/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep
public import Mathlib.Topology.Homeomorph.Defs

/-!
# A transverse sweep is a topological prism

The base point and ray parameter of a transverse sweep vary continuously. Thus
the bijective prism parameterization is a homeomorphism, including for unbounded
bases and bases with lineality. The base need not be closed or convex.
-/

public section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {n : V}

/-- A normalized height gives the inverse prism coordinates explicitly. -/
theorem sweepEquiv_symm_apply (hn : n ∉ vectorSpan ℝ P)
    (f : V →ₗ[ℝ] ℝ) (c : ℝ) (hfn : f n = 1) (hfP : ∀ x ∈ P, f x = c)
    (y : sweep P n) :
    (sweepEquiv P n hn).symm y =
      (⟨(y : V) + (c - f y) • n, ((mem_sweep_iff f c hfn hfP).mp y.property).2⟩,
       ⟨c - f y, sub_nonneg.mpr ((mem_sweep_iff f c hfn hfP).mp y.property).1⟩) := by
  apply (sweepEquiv P n hn).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply, sweepEquiv_apply]
  module

variable [FiniteDimensional ℝ V]

/-- The prism parameterization is a homeomorphism for every nonempty transverse base. -/
@[expose]
noncomputable def sweepHomeomorph (hP : P.Nonempty) (hn : n ∉ vectorSpan ℝ P) :
    (P × {t : ℝ // 0 ≤ t}) ≃ₜ sweep P n where
  toEquiv := sweepEquiv P n hn
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).sub
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  continuous_invFun := by
    change Continuous (sweepEquiv P n hn).symm
    obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hP hn
    have hf : Continuous (fun y : sweep P n => f (y : V)) :=
      f.continuous_of_finiteDimensional.comp continuous_subtype_val
    have he := funext (sweepEquiv_symm_apply hn f c hfn hfP)
    rw [he]
    exact (Continuous.subtype_mk
      (continuous_subtype_val.add ((continuous_const.sub hf).smul continuous_const)) _).prodMk
      (Continuous.subtype_mk (continuous_const.sub hf) _)

/-- The topological prism uses the original negative-ray parameterization. -/
@[simp]
theorem sweepHomeomorph_apply (hP : P.Nonempty) (hn : n ∉ vectorSpan ℝ P)
    (z : P × {t : ℝ // 0 ≤ t}) :
    (sweepHomeomorph hP hn z : V) = z.1.1 - z.2.1 • n := rfl

end Mei.Convex
