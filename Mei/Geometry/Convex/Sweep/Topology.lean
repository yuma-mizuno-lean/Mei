/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# A transverse sweep is a topological prism

The base point and ray parameter of a transverse sweep vary continuously. Thus
the bijective prism parameterization is a homeomorphism, including for unbounded
bases and bases with lineality. The base need not be closed, convex, or nonempty.
A normalized continuous height also gives an affine projection onto the base
hyperplane and expresses the sweep as a halfspace intersected with an affine preimage.
-/

public section

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {n : V}

/-- The affine projection recovering the base point of a transverse sweep.
When `f n = 1`, its image lies in the hyperplane `f x = c`. -/
def sweepProjection (f : V →L[ℝ] ℝ) (c : ℝ) (n : V) : V →ᴬ[ℝ] V :=
  (ContinuousLinearMap.id ℝ V - f.smulRight n).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ V (c • n)

/-- The projection adds the unique correction along the sweeping vector. -/
@[simp]
theorem sweepProjection_apply (f : V →L[ℝ] ℝ) (c : ℝ) (n y : V) :
    sweepProjection f c n y = y + (c - f y) • n := by
  simp only [sweepProjection, ContinuousAffineMap.add_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousAffineMap.coe_const, Function.const_apply]
  module

/-- The recovered base point has the required height. -/
theorem sweepProjection_height (f : V →L[ℝ] ℝ) (c : ℝ) {n : V}
    (hn : f n = 1) (y : V) :
    f (sweepProjection f c n y) = c := by
  simp [hn]

/-- The sweep projection fixes the base hyperplane. -/
theorem sweepProjection_eq_self (f : V →L[ℝ] ℝ) (c : ℝ) {n y : V}
    (hy : f y = c) : sweepProjection f c n y = y := by
  simp [hy]

/-- The explicit projection presents the sweep as a halfspace intersected with
an affine preimage, with no boundedness hypothesis on the base. -/
theorem sweep_eq_halfspace_inter_preimage {P : Set V} {n : V}
    (f : V →L[ℝ] ℝ) (c : ℝ) (hn : f n = 1)
    (hP : ∀ x ∈ P, f x = c) :
    sweep P n = {y | f y ≤ c} ∩ sweepProjection f c n ⁻¹' P := by
  ext y
  simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
    sweepProjection_apply, ContinuousLinearMap.coe_coe] using
    (mem_sweep_iff f.toLinearMap c hn hP (y := y))

/-- Sweeping an entire transverse affine hyperplane produces its closed negative
halfspace. In particular no boundedness or absence of lineality is required. -/
theorem sweep_hyperplane (f : V →L[ℝ] ℝ) (c : ℝ) {n : V} (hn : f n = 1) :
    sweep {x : V | f x = c} n = {x : V | f x ≤ c} := by
  rw [sweep_eq_halfspace_inter_preimage f c hn (fun _ hx => hx)]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_iff_left (sweepProjection_height f c hn y)

/-- An unbounded base with lineality: the horizontal axis sweeps to the closed
lower half-plane under the positive vertical sweeping vector. -/
theorem sweep_horizontal_axis :
    sweep {p : ℝ × ℝ | p.2 = 0} (0, 1) = {p : ℝ × ℝ | p.2 ≤ 0} :=
  sweep_hyperplane (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 rfl

variable [FiniteDimensional ℝ V]

/-- The prism parameterization is a homeomorphism for every transverse base. -/
noncomputable def sweepHomeomorph (hn : n ∉ vectorSpan ℝ P) :
    (P × {t : ℝ // 0 ≤ t}) ≃ₜ sweep P n where
  toEquiv := sweepEquiv P n hn
  continuous_toFun := by
    rw [Equiv.toFun_as_coe]
    apply continuous_induced_rng.mpr
    simp only [Function.comp_def, sweepEquiv_apply]
    exact (continuous_subtype_val.comp continuous_fst).sub
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  continuous_invFun := by
    rw [Equiv.invFun_as_coe]
    rcases P.eq_empty_or_nonempty with rfl | hP
    · have : IsEmpty (sweep (∅ : Set V) n) := by
        rw [sweep_empty]
        infer_instance
      exact continuous_of_discreteTopology
    · obtain ⟨f, c, hfn, hfP⟩ := exists_sweep_height hP hn
      have hf : Continuous (fun y : sweep P n => f (y : V)) :=
        f.continuous_of_finiteDimensional.comp continuous_subtype_val
      rw [funext (sweepEquiv_symm_apply hn f c hfn hfP)]
      exact (Continuous.subtype_mk
        (continuous_subtype_val.add ((continuous_const.sub hf).smul continuous_const)) _).prodMk
        (Continuous.subtype_mk (continuous_const.sub hf) _)

/-- Forgetting the topology recovers the algebraic prism equivalence. -/
@[simp]
theorem sweepHomeomorph_toEquiv (hn : n ∉ vectorSpan ℝ P) :
    (sweepHomeomorph hn).toEquiv = sweepEquiv P n hn := (rfl)

/-- The topological prism uses the original negative-ray parameterization. -/
@[simp]
theorem sweepHomeomorph_apply (hn : n ∉ vectorSpan ℝ P)
    (z : P × {t : ℝ // 0 ≤ t}) :
    (sweepHomeomorph hn z : V) = z.1.1 - z.2.1 • n := by
  exact sweepEquiv_apply P n hn z

end Mei.Convex
