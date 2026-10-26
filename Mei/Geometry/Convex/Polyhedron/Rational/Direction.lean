/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.Direction
public import Mei.LinearAlgebra.Dual.Kernel

/-!
# Integral equations for tangent spaces of rational-normal polyhedra

A nonempty rational-normal polyhedron of codimension two has tangent space the
common kernel of two real extensions of integral characters. Thus its lattice
tangent vectors are the common integral kernel, even when its affine offsets
are irrational. This supplies equations for the normal plane at a polyhedral
joint, without requiring boundedness, pointedness or an irredundant presentation.

The construction combines `AffineMap.direction_affineSpan_setOf_forall_le`,
`Toric.IsRationalFunctional.exists_ker_eq_realCharacter` and
`LinearMap.exists_iInf_ker_eq_inf`.
-/

public section

namespace Mei.IsRationalNormalPolyhedron

open Set

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- A codimension-two rational-normal polyhedron has tangent space cut out by
two integral characters. The affine offsets need not be rational. -/
theorem exists_direction_eq_inf_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 2 = Module.finrank ℝ V) :
    ∃ m n : Module.Dual ℤ N, (affineSpan ℝ P).direction =
      (h.realCharacter m.toAddMonoidHom).ker ⊓ (h.realCharacter n.toAddMonoidHom).ker := by
  classical
  let := h.finiteDimensional
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  have hcarrier : Q.carrier = {x | ∀ j, Q.inequality j x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  let I := {j : Fin Q.numConstraints // ∀ x ∈ Q.carrier, Q.inequality j x = 0}
  have hrows (j : I) := (Q.rational_linear j.val).exists_ker_eq_realCharacter
  choose m hm using hrows
  have hdir : (affineSpan ℝ Q.carrier).direction =
      ⨅ j : I, (h.realCharacter (m j).toAddMonoidHom).ker := by
    simp_rw [← hm]
    simpa only [I, iInf_subtype, hcarrier, Set.mem_ofPred_eq,
      ContinuousAffineMap.coe_toAffineMap] using
      AffineMap.direction_affineSpan_setOf_forall_le
        (fun j => (Q.inequality j).toAffineMap) (hcarrier ▸ hne)
  obtain ⟨j, k, hjk⟩ := LinearMap.exists_iInf_ker_eq_inf
    (fun j : I => h.realCharacter (m j).toAddMonoidHom) (hdir ▸ hdim)
  exact ⟨m j, m k, hdir.trans hjk⟩

end Mei.IsRationalNormalPolyhedron
