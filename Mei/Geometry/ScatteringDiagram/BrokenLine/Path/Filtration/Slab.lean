/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Filtration
public import Mei.Algebra.MonoidAlgebra.Filtration.Coefficient
public import Mei.RingTheory.Node.Filtration

/-!
# Encounter bounds for slab faces with nilpotent kinks along quiver paths

Let `a : R[M]` have all coefficients in an ideal `I` of `R`. The whole-component
transfer of the slab correspondence `exponentCorrespondence a` of `R[M][X,Y]/(XY - a)`
sends the component of exponent `(d, m)` to a component of exponent `(-d, n)` and
multiplies by `a ^ d`. Hence a transfer to a different exponent raises the order in the
coefficient filtration `Ideal.coeffFiltration` by at least one
(`Mei.NodeAlgebra.homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence`).

Consequently, if `I ^ r = 0` and every arrow of a finite quiver crosses such a slab face
in either orientation, every actual decorated ray along any encounter path has at most
`r` times the number of arrows encounters, provided the velocity of an exponent does not
depend on the chamber. The bound counts every encounter, including encounters that change
neither degree nor spatial velocity and encounters of weight zero. It assumes neither
positivity of the exponent grading nor any condition on the slab parameters beyond their
coefficients lying in `I`.

This is the slab-face part of the positive-kink finiteness argument of
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical class*,
Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4). The ordinary-wall part is
`Mei.PathDecoratedRay.length_le_of_functionWallAction`.
-/

public noncomputable section

open Quiver AddMonoidAlgebra Mei.NodeAlgebra

namespace Mei.PathDecoratedRay

variable {Q R M V J K : Type*} [Quiver Q] [Finite (Σ b c : Q, b ⟶ c)]
  [CommRing R] [AddCommMonoid M] [DecidableEq M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {a b : Q} {i₀ : ℤ × M} {x : grade R i₀} {v : Q → ℤ × M → V}
  {ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ} {ε : ∀ {b c : Q}, (b ⟶ c) → SignType}
  {c : ∀ {b c : Q}, (b ⟶ c) → ℝ} {P : ∀ {b c : Q}, (b ⟶ c) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {p : Path a b} {X : V}

/-- Slab faces whose parameters have coefficients in a nilpotent ideal `I`, with
`I ^ r = 0`, bound the number of encounters of every actual decorated ray along any
encounter path by `r` times the number of arrows. Each face may be crossed in either
orientation; no positivity of the exponent grading is assumed. -/
theorem length_le_of_exponentCorrespondence
    (s : ∀ {b c : Q}, (b ⟶ c) → R[M]) (I : Ideal R)
    (hs : ∀ {b c : Q} (e : b ⟶ c) m, (s e).coeff m ∈ I) {r : ℕ} (hr : I ^ r = ⊥)
    {T : ∀ {b c : Q}, (b ⟶ c) → Module.End R R[ℤ × M]}
    (hT : ∀ {b c : Q} (e : b ⟶ c), T e = (exponentCorrespondence (s e)).totalTransfer ∨
      T e = (exponentCorrespondence (s e)).symm.totalTransfer)
    (hv : ∀ {b c : Q} (_ : b ⟶ c) (i : ℤ × M), v b i = v c i)
    (β : PathDecoratedRay (M := fun _ => R[ℤ × M]) (ι := fun _ => ℤ × M)
      T (fun _ => grade R) i₀ x v ν ε c P W S C p X) :
    p.length ≤ r * Nat.card (Σ b c : Q, b ⟶ c) := by
  apply β.length_le_of_filtration (F := fun _ => Ideal.coeffFiltration I (ℤ × M))
    (mark := fun _ i j => if i = j then 0 else 1)
  · rw [componentTransfersRaise_iff]
    intro b c e i j k y hy hyk
    exact homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence (hs e) (hT e) hy hyk
  · intro b c e i j h
    by_cases hij : i = j
    · rw [← hij]
      exact hv e i
    · simp [hij] at h
  · exact Ideal.coeffFiltration_submodule_eq_bot I (ℤ × M) hr

end Mei.PathDecoratedRay
