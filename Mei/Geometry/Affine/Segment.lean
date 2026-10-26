/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Stability of segments avoiding a closed set

Pairs of endpoints whose closed segment avoids a closed obstacle form an open
set. This supplies the compact-parameter part of stability for transverse
polygonal paths. The proof uses Mathlib's closedness of projection along a
compact space, applied to the unit interval of segment parameters.
-/

public section

open Set

namespace IsClosed

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]

/-- Avoiding a closed obstacle along an entire closed segment is an open
condition on its two endpoints. -/
theorem isOpen_setOf_lineMap_notMem {S : Set P} (hS : IsClosed S) :
    IsOpen {p : P × P | ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p.1 p.2 t ∉ S} := by
  have hc : Continuous (fun q : (P × P) × Icc (0 : ℝ) 1 =>
      AffineMap.lineMap q.1.1 q.1.2 (q.2 : ℝ)) :=
    continuous_fst.fst.lineMap continuous_fst.snd
      (continuous_subtype_val.comp continuous_snd)
  have hclosed := isClosedMap_fst_of_compactSpace _ (hS.preimage hc)
  convert hclosed.isOpen_compl using 1
  ext p
  simp only [mem_ofPred_eq, mem_compl_iff, mem_image, mem_preimage, Prod.exists,
    not_exists, not_and, Subtype.forall]
  aesop

end IsClosed
