/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.Direction
public import Mei.LinearAlgebra.Dual.Basic
public import Mei.LinearAlgebra.Dual.Kernel

/-!
# Integral equations for rational-normal polyhedral directions

The direction of a nonempty rational-normal polyhedron of codimension `k` is
the common kernel of `k` independent real extensions of integral characters.
Offsets need not be rational: only the rows vanishing on the entire polyhedron
control its affine direction. This supplies integral conormals for actual cells,
including joints, rather than requiring a choice of defining equations as input.
-/

public section

open Set

namespace Mei.IsRationalNormalPolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V}

/-- A nonempty rational-normal polyhedron of codimension `k` has exactly `k`
independent integral conormals cutting out its affine direction. Arbitrary real
offsets, redundant inequalities, unboundedness and lineality are allowed. -/
theorem exists_direction_eq_iInf_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty) {k : ℕ}
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V) :
    ∃ m : Fin k → Module.Dual ℤ N,
      LinearIndependent ℝ (fun j => h.realCharacter (m j).toAddMonoidHom) ∧
      (affineSpan ℝ P).direction =
        ⨅ j, (h.realCharacter (m j).toAddMonoidHom).ker := by
  /- The proof uses `AffineMap.direction_affineSpan_setOf_forall_le` to identify the
  active equations, then Mathlib's `Submodule.exists_fun_fin_finrank_span_eq`
  and dual-coannihilator dimension formula to extract independent equations. -/
  classical
  let := h.finiteDimensional
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp hP
  have hcarrier : Q.carrier = {x | ∀ j, Q.inequality j x ≤ 0} :=
    Set.ext fun _ => RationalAffinePolyhedron.mem_carrier
  let I := {j : Fin Q.numConstraints // ∀ x ∈ Q.carrier, Q.inequality j x = 0}
  have hrows (j : I) := (Q.rational_linear j.val).exists_ker_eq_realCharacter
  choose m hm using hrows
  let f : I → Module.Dual ℝ V := fun j => h.realCharacter (m j).toAddMonoidHom
  have hdir : (affineSpan ℝ Q.carrier).direction = ⨅ j, (f j).ker := by
    simp_rw [f, ← hm]
    simpa only [I, iInf_subtype, hcarrier, Set.mem_ofPred_eq,
      ContinuousAffineMap.coe_toAffineMap] using
      AffineMap.direction_affineSpan_setOf_forall_le
        (fun j => (Q.inequality j).toAffineMap) (hcarrier ▸ hne)
  have hcoann : (Submodule.span ℝ (range f)).dualCoannihilator =
      (affineSpan ℝ Q.carrier).direction :=
    (Submodule.dualCoannihilator_span_range f).trans hdir.symm
  have hrank : Module.finrank ℝ (Submodule.span ℝ (range f)) = k := by
    have he := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span ℝ (range f))
    rw [hcoann] at he
    omega
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℝ (range f)
  rw [hrank] at hex
  obtain ⟨b, hb, hspan, hlin⟩ := hex
  choose a ha using hb
  have heq : (fun j => h.realCharacter (m (a j)).toAddMonoidHom) = b := funext ha
  refine ⟨fun j => m (a j), heq.symm ▸ hlin, ?_⟩
  · rw [← hcoann, ← hspan, Submodule.dualCoannihilator_span_range, ← heq]

/-- A codimension-two rational-normal polyhedron has tangent space cut out by
two integral characters. The affine offsets need not be rational. -/
theorem exists_direction_eq_inf_ker (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + 2 = Module.finrank ℝ V) :
    ∃ m n : Module.Dual ℤ N, (affineSpan ℝ P).direction =
      (h.realCharacter m.toAddMonoidHom).ker ⊓ (h.realCharacter n.toAddMonoidHom).ker := by
  obtain ⟨m, _, hdir⟩ := hP.exists_direction_eq_iInf_ker hne hdim
  refine ⟨m 0, m 1, ?_⟩
  rw [hdir]
  ext v
  simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, Fin.forall_fin_two]

end Mei.IsRationalNormalPolyhedron
