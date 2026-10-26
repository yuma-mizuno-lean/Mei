/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Sum
public import Mei.Algebra.Lie.BCH.Group

/-!
# Cancellation of the linear logarithmic term

For a closed admissible path, the sum of the logarithms of its individual signed
wall factors vanishes after any additive projection for which all surviving
walls are full affine hyperplanes. In particular a homogeneous projection kills
the linear term at a correction order when initial walls are full hyperplanes
and the other walls have homogeneous logarithms of lower degrees.

This concerns the linear sum, not the logarithm of the product: nonlinear
commutator terms may survive. No commutativity of different wall labels is
assumed. The proof combines `BCHGroup.exp_zsmul` with the half-space telescoping
formula `Quiver.Path.wallCrossingSum_eq_sum_side_sub`.

The role of this cancellation in joint obstructions follows Travis Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
[arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5), proof of Theorem 2.6,
and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
[arXiv:1411.1394v2](https://arxiv.org/abs/1411.1394v2), Appendix C.3.
-/

public section

noncomputable section

open Mei.Convex WallComplement

namespace Quiver.Path

variable {V ι L E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [LieRing L] [LieAlgebra ℚ L] [LieRing.IsNilpotent L] [AddCommGroup E]
  {W : ι → Set V} {x y : WallComplement W}

/-- The linear sum of the logarithms of individual signed wall factors is the
additive crossing sum of their logarithms. Coincident indexed walls are retained. -/
theorem sum_log_signedCrossingEvents (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → Mei.BCHGroup L) :
    ((p.signedCrossingEvents ν).map
      (fun S => ∑ a ∈ S, Mei.BCHGroup.log (label a.1 ^ a.2))).sum =
        p.wallCrossingSum ν (fun j => Mei.BCHGroup.log (label j)) := by
  simp [wallCrossingSum_def]

/-- The linear logarithmic contribution around a loop vanishes under any additive
projection that kills the logarithms of all walls other than full hyperplanes.
No commutativity of the original labels or faithfulness of the projection is required. -/
theorem map_sum_log_signedCrossingEvents_loop_eq_zero (p : AdmissiblePLPath x x)
    (ν : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (label : ι → Mei.BCHGroup L) (f : L →+ E)
    (hW : ∀ j, f (Mei.BCHGroup.log (label j)) ≠ 0 → W j = {v | ν j v = b j}) :
    f (((p.signedCrossingEvents ν).map
      (fun S => ∑ a ∈ S, Mei.BCHGroup.log (label a.1 ^ a.2))).sum) = 0 := by
  rw [sum_log_signedCrossingEvents, AddMonoidHom.map_wallCrossingSum]
  exact wallCrossingSum_loop_eq_zero p ν b _ hW

end Quiver.Path
