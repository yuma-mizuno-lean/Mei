/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Convex.Polyhedron.Boundary
public import Mei.LinearAlgebra.Dual.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

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
  /- The proof uses `Mei.Convex.direction_affineSpan_eq_iInf_ker` to identify the
  active equations, then Mathlib's `Submodule.exists_fun_fin_finrank_span_eq`
  and dual-coannihilator dimension formula to extract independent equations. -/
  classical
  let := h.finiteDimensional
  obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp hP
  obtain ⟨p, hp⟩ := hne.intrinsicInterior (hQ ▸ Q.convex)
  let A := {j : Fin Q.numConstraints // ∀ x ∈ P, Q.inequality j x = 0}
  obtain ⟨m, hm⟩ := Classical.axiomOfChoice fun j : A =>
    (Q.rational_linear j.val).exists_ker_eq_ker_realCharacter
  let f : A → Module.Dual ℝ V := fun j => h.realCharacter (m j).toAddMonoidHom
  have hdir : (affineSpan ℝ P).direction = ⨅ j, (f j).ker := by
    have he := Convex.direction_affineSpan_eq_iInf_ker Q.inequality
      (hQ.symm.trans (Set.ext fun _ => RationalAffinePolyhedron.mem_carrier)) hp
    exact he.trans (iInf_congr fun j => hm j)
  have hcoann : (Submodule.span ℝ (range f)).dualCoannihilator =
      (affineSpan ℝ P).direction :=
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

end Mei.IsRationalNormalPolyhedron
