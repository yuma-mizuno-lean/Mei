/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Algebra.MonoidAlgebra.Filtration.Coefficient
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.EncounterBound
public import Mei.RingTheory.Node.Filtration

/-!
# Encounter bounds for slab faces with kinks in a nilpotent ideal

Let `a : R[M]` have all coefficients in an ideal `I` of `R`. The whole-component transfer of the
slab correspondence `exponentCorrespondence a` of `R[M][X,Y]/(XY - a)` sends the component of
exponent `p = (d, m)` to the component of exponent `q = (-d, m')` and multiplies by `a ^ d`.
Hence a component of normal weight `d > 0` gains `d` powers of `I`, while a component of weight
zero is carried to itself. A transfer to a different exponent therefore raises the order in the
coefficient filtration `Ideal.coeffFiltration` by at least one
(`Mei.NodeAlgebra.homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence`).

Consequently, if `I ^ r = 0`, every actual decorated ray crossing slab faces of this kind, in
either orientation, has at most `r * Nat.card J` encounters, where `J` indexes the supporting
hyperplanes of the faces
(`Mei.DecoratedAdmissibleRay.encounter_count_le_of_exponentCorrespondence`). The bound counts every
encounter, including encounters that change neither degree nor spatial velocity and encounters of
weight zero. It assumes neither positivity of the exponent grading nor any condition on the slab
parameters beyond their coefficients lying in `I`.

This is the slab-face part of the positive-kink finiteness argument of Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4). The ordinary-wall part is
`Mei.DecoratedAdmissibleRay.encounter_count_le_of_functionWallAction`.
-/

public noncomputable section

namespace Mei.NodeAlgebra

open TauCeti AddMonoidAlgebra

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [DecidableEq M] {I : Ideal R}

/-- A homogeneous input in the `k`-th term of the coefficient filtration is sent by the
whole-component transfer of a slab correspondence, in either orientation, into the `k`-th term
if the output exponent is the input exponent, and into the `(k + 1)`-st term otherwise, provided
the slab parameter has all coefficients in `I`. -/
theorem homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence {a : R[M]}
    (ha : ∀ m, a.coeff m ∈ I) {T : Module.End R R[ℤ × M]}
    (hT : T = (exponentCorrespondence a).totalTransfer ∨
      T = (exponentCorrespondence a).symm.totalTransfer)
    {p q : ℤ × M} {x : R[ℤ × M]} (hx : x ∈ grade R p) {k : ℕ}
    (hxk : x ∈ (Ideal.coeffFiltration I (ℤ × M)).submodule k) :
    homogeneousComponent (grade R : ℤ × M → _) q (T x) ∈
      (Ideal.coeffFiltration I (ℤ × M)).submodule (k + if p = q then 0 else 1) := by
  classical
  have key (C : GradedCorrespondence (B := NodeAlgebra R[M] a) (grade R : ℤ × M → _)
      (grade R : ℤ × M → _) {p | 0 ≤ p.1} {p | 0 ≤ p.1})
      (hC : ∀ (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val),
        ((C.transfer p q u : grade R q) : R[ℤ × M]) =
          single q (slabComponentMap a p q (u.val.coeff p.val))) :
      homogeneousComponent (grade R : ℤ × M → _) q (C.totalTransfer x) ∈
        (Ideal.coeffFiltration I (ℤ × M)).submodule (k + if p = q then 0 else 1) := by
    rw [homogeneousComponent_apply, GradedCorrespondence.totalTransfer_apply,
      C.decompose_right_liftLeftTotal_of_mem hx q]
    by_cases hp : p ∈ {p : ℤ × M | 0 ≤ p.1}
    · simp only [hp, ↓reduceDIte]
      rw [hC ⟨p, hp⟩ q ⟨x, hx⟩]
      exact Ideal.single_mem_coeffFiltration_submodule.2
        (Ideal.slabComponentMap_mem_pow_add_ite I ha ⟨p, hp⟩ q
          (Ideal.mem_coeffFiltration_submodule.1 hxk p))
    · simp only [hp, ↓reduceDIte]
      exact Submodule.zero_mem _
  rcases hT with rfl | rfl
  · exact key _ fun p q u => exponentCorrespondence_transfer_eq_single a p q u
  · exact key _ fun p q u => exponentCorrespondence_symm_transfer_eq_single a p q u

end Mei.NodeAlgebra

namespace Mei.DecoratedAdmissibleRay

open AddMonoidAlgebra Mei.NodeAlgebra

variable {R M V J K O : Type*} [CommRing R] [AddCommMonoid M] [DecidableEq M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  {n : ℕ} {p₀ : ℤ × M} {a₀ : grade R p₀} {v : ℤ × M → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : O → Set V} {S : K → Set V} {C : Set V} {Q : V}
  {wall : Fin n → J}

/-- Slab faces whose parameters have coefficients in a nilpotent ideal `I`, with `I ^ r = 0`,
bound the number of encounters of every actual decorated ray by `r * Nat.card J`. Each face may
be crossed in either orientation. Unchanged-degree encounters and encounters of weight zero are
counted, and no positivity of the exponent grading is assumed. -/
theorem encounter_count_le_of_exponentCorrespondence (a : J → R[M]) (I : Ideal R)
    (ha : ∀ e m, (a e).coeff m ∈ I) {r : ℕ} (hr : I ^ r = ⊥) {T : J → Module.End R R[ℤ × M]}
    (hT : ∀ e, T e = (exponentCorrespondence (a e)).totalTransfer ∨
      T e = (exponentCorrespondence (a e)).symm.totalTransfer)
    (β : DecoratedAdmissibleRay (grade R : ℤ × M → _) (fun j => T (wall j)) p₀ a₀ v
      (fun j => f (wall j)) (fun j => c (wall j)) (fun j => ε (wall j))
      (fun j => P (wall j)) W S C Q) :
    n ≤ r * Nat.card J := by
  apply encounter_count_le_of_filtration (T := T) (wall := wall) β
    (Ideal.coeffFiltration I (ℤ × M)) (fun _ i j => if i = j then 0 else 1)
  · intro e i j k x hx hxk
    exact homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence (ha e) (hT e) hx hxk
  · intro e i j h
    by_cases hij : i = j
    · exact congrArg v hij
    · simp [hij] at h
  · exact Ideal.coeffFiltration_submodule_eq_bot hr

end Mei.DecoratedAdmissibleRay
