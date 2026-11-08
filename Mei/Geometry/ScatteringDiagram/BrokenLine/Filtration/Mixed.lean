/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.Geometry
public import Mei.Algebra.MonoidAlgebra.Filtration.FunctionWall
public import Mei.RingTheory.Node.Filtration

/-!
# Mixed ordinary-wall and slab encounter bounds

A propagation history in monoid chamber coordinates may cross both ordinary
function walls and slab faces. We use the coefficient filtration for both kinds
of transfer. An ordinary component changing exponent raises order; every
transverse admissible slab input has positive normal weight and raises order.
Unchanged ordinary components preserve the developed direction. The whole
encounter word therefore has length at most the nilpotency index times the
number of supporting hyperplanes.

The decorations are whole nonzero components, with no restriction on initial
ideal order. Their developed velocity maps may differ between segments, as they
do on opposite sides of a slab. At an ordinary crossing those maps agree. All
encounters are retained, including degree changes with unchanged spatial
velocity. No positive exponent grading, regular slab parameter or injectivity
of the slab legs is required.

This combines the two coefficient estimates in the finiteness argument of
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4). It gives the encounter
bound for developed monoid coordinates, rather than constructing endpoint charts
or gluing different affine charts.
-/

public noncomputable section

namespace Mei.Convex.AdmissibleRayRealization

open AddMonoidAlgebra Mei.GradedAlgebra Mei.NodeAlgebra

variable {R M V J₀ J₁ K O : Type*} [CommRing R] [AddCommMonoid M] [DecidableEq M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J₀] [Finite J₁]
  (𝒜 : J₀ → ℤ → Submodule R R[ℤ × M]) [∀ e, GradedAlgebra (𝒜 e)]
  (θ : ∀ e, (𝒜 e 0)ˣ) (weight : J₀ → ℤ × M → ℤ)
  (slab : J₁ → R[M]) (T : J₁ → Module.End R R[ℤ × M])
  (I : Ideal R)
  {n : ℕ} {f : J₀ ⊕ J₁ → V →L[ℝ] ℝ} {c : J₀ ⊕ J₁ → ℝ}
  {wall : Fin n → J₀ ⊕ J₁} {P : Fin n → Set V}
  {W : O → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (v : Fin (n + 1) → ℤ × M → V) (p : Fin (n + 1) → ℤ × M)
  (a : Fin (n + 1) → R[ℤ × M])

/-- The full encounter count of an actual ray with mixed ordinary function-wall
and slab transfers is bounded by the common nilpotency order times the total
wall alphabet. The slab input weights are strictly positive, as for admissible
transverse incoming degrees in local monoid presentations. Both slab orientations
and negative ordinary normal weights are allowed. -/
theorem encounter_count_le_of_functionWalls_and_slabs
    (β : AdmissibleRayRealization (fun j => f (wall j)) (fun j => c (wall j))
      (fun j => v j (p j)) P W S C Q)
    (ha : ∀ j, a j ∈ grade R (p j)) (hne : ∀ j, a j ≠ 0)
    (hprop : ∀ j, a j.castSucc = homogeneousComponent (grade R) (p j.castSucc)
      (Sum.elim (fun e => (functionWallAction (𝒜 e) (θ e)).toLinearMap) T
        (wall j) (a j.succ)))
    (hθ : ∀ e, algebraMap (𝒜 e 0) R[ℤ × M] (θ e) - 1 ∈
      I.map (algebraMap R R[ℤ × M]))
    (hw : ∀ e q, grade R q ≤ 𝒜 e (weight e q))
    (hslab : ∀ e m, (slab e).coeff m ∈ I)
    (hT : ∀ e, T e = (exponentCorrespondence (slab e)).totalTransfer ∨
      T e = (exponentCorrespondence (slab e)).symm.totalTransfer)
    (hcoord : ∀ j e, wall j = Sum.inl e → ∀ q, v j.castSucc q = v j.succ q)
    (htrans : ∀ j e, wall j = Sum.inr e → 0 < (p j.succ).1)
    {r : ℕ} (hr : I ^ r = ⊥) :
    n ≤ r * (Nat.card J₀ + Nat.card J₁) := by
  classical
  let F := I.coeffFiltration (ℤ × M)
  let mark (j : Fin n) : ℕ := match wall j with
    | Sum.inl _ => if p j.succ = p j.castSucc then 0 else 1
    | Sum.inr _ => 1
  have hstep (j : Fin n) (k : ℕ) (hk : a j.succ ∈ F.submodule k) :
      a j.castSucc ∈ F.submodule (k + mark j) := by
    rw [hprop j]
    cases he : wall j with
    | inl e =>
      simpa only [mark, he, Sum.elim_inl, AlgEquiv.toLinearMap_apply] using
        homogeneousComponent_functionWallAction_mem_coeffFiltration
          (𝒜 e) I (θ e) (hθ e) (ha j.succ) (hw e _ (ha j.succ)) hk
    | inr e =>
      have hm := homogeneousComponent_exponentCorrespondence_mem_coeffFiltration_add_normalWeight
        (hslab e) (hT e) (q := p j.castSucc) (ha j.succ) hk
      have hp := htrans j e he
      have hle : k + 1 ≤ k + (p j.succ).1.toNat := by omega
      have hm' := F.antitone hle hm
      simpa only [mark, he, Sum.elim_inr] using hm'
  have hstraight (j : Fin n) (hj : mark j = 0) :
      v j.castSucc (p j.castSucc) = v j.succ (p j.succ) := by
    cases he : wall j with
    | inl e =>
      have hp : p j.succ = p j.castSucc := by
        by_contra hp
        simp only [mark, he, hp, ite_false, one_ne_zero] at hj
      rw [hp, hcoord j e he]
    | inr e => simp only [mark, he, one_ne_zero] at hj
  simpa only [Nat.card_sum] using β.encounter_count_le_of_filtration
    (fun _ => F) a hne mark hstep hstraight
    (fun _ => I.coeffFiltration_submodule_eq_bot (ℤ × M) hr)

end Mei.Convex.AdmissibleRayRealization
