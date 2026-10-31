/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange
public import Mei.Algebra.Lie.Graded.Shifted.History

/-!
# Last positive changes of finite BCH-decorated rays

Every actual ray decorated by signed finite BCH actions is either unchanged
throughout or has a unique last positive degree change. The incoming coefficient
at that encounter has strictly smaller relative degree. Its selected output is
the final whole decoration, and the actual terminal path is straight.

No assumption about spatial directions detects the change: a nonzero shift
with zero spatial projection is retained. The result uses the diagonal identity
and positive support of the inherited shifted quotient grading, together with
`DecoratedAdmissibleRay.existsUnique_last_degree_change`. It supplies the
terminal decomposition for backward-ray recursions comparing probe coefficients
with broken-line sums. For the broken-line conventions and endpoint transport,
see Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Definition 2.10 and §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.PositiveDegrees

variable {Γ : Type} {R L M V J K : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ) (k : ℕ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (g : Fin n → d.truncatedGroup ℒ k)
  {r₀ : Γ} {a : (d.shiftedQuotientGrading ℳ p k).piece r₀}
  {velocity : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

local notation "G" => TauCeti.InternalGrading.piece (d.shiftedQuotientGrading ℳ p k)
local notation "T" => fun j =>
  LinearEquiv.toLinearMap
    (ModuleFiltration.truncatedBCHAction (d.shiftedLieFiltration ℒ ℳ p) d ℒ k (g j))

/-- A BCH-decorated ray is unchanged, or it has a unique last positive degree
change. The changing encounter reads a strictly lower-degree whole coefficient,
and its output persists through every remaining encounter to the endpoint.
The statement allows inverse labels and coefficient changes with zero spatial
projection, as well as cutoff zero and empty itineraries. -/
theorem decoratedAdmissibleRay_eq_input_or_existsUnique_last_degree_change
    (r : DecoratedAdmissibleRay G T r₀ a velocity f c ε P W S C Q) :
    let b := Fin.snoc (α := fun _ => Γ) r.1.val r₀
    ((∀ i, b i = r₀) ∧ r.decoration 0 = (a : (d.shiftedLieFiltration ℒ ℳ p).quotient k) ∧
      ∀ t ≤ 0, r.2.ray t = Q - t • velocity r₀) ∨
    ∃! j : Fin n, b j.succ ≠ b 0 ∧
      (∀ i ≤ j.castSucc, b i = b 0) ∧
      b 0 - b j.succ ∈ d.monoid ∧ d.degree (b j.succ) < d.degree (b 0) ∧
      r.decoration 0 = (DirectSum.decompose G (T j (r.decoration j.succ)) (b 0) :
        (d.shiftedLieFiltration ℒ ℳ p).quotient k) ∧
      ∀ t ∈ Icc (r.2.parameter j.succ) 0, r.2.ray t = Q - t • velocity (b 0) := by
  classical
  dsimp only
  let b := Fin.snoc (α := fun _ => Γ) r.1.val r₀
  have hT : ∀ j s x, x ∈ G s → (DirectSum.decompose G (T j x) s :
      (d.shiftedLieFiltration ℒ ℳ p).quotient k) = x :=
    fun j _ _ hx => d.decompose_truncatedBCHAction_same ℒ ℳ p k (g j) hx
  by_cases hc : ∀ i, b i = b 0
  · have hconst : ∀ i, b i = r₀ := by
      intro i
      exact (hc i).trans (by simpa only [b, Fin.snoc_last] using (hc (Fin.last n)).symm)
    exact Or.inl ⟨hconst, r.decoration_eq_input_and_ray_eq_of_degrees_eq hT hconst⟩
  · obtain ⟨j, ⟨hne, hp, hw, hpath⟩, hu⟩ := r.existsUnique_last_degree_change hT hc
    have hstep := d.homogeneousHistory_shiftedBCHAction_sub_mem_monoid ℒ ℳ p k g
      r.1.val r₀ a ((mem_decoratedHistorySupport ..).mp r.1.property).1 j
    have hj : r.1.val j = b 0 := by
      simpa only [b, Fin.snoc_castSucc] using hp j.castSucc le_rfl
    rw [hj] at hstep
    have hpos := d.degree_pos hstep (sub_ne_zero.mpr hne.symm)
    refine Or.inr ⟨j, ⟨hne, hp, hstep, ?_, hw, hpath⟩, ?_⟩
    · exact sub_pos.mp (by simpa only [map_sub] using hpos)
    · intro l hl
      exact hu l ⟨hl.1, hl.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2⟩

end Mei.PositiveDegrees
