/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Incoming
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Weighted attachment at generic straight incoming cuts

Refine an endpoint arrangement so that the exact straight cut used in weighted
final-encounter attachment is generic for a prescribed incoming discriminant.
The outgoing fiber sum then equals the selected component of propagation of
the entire incoming fiber sum at that generic point. This allows degree
induction to apply to the incoming sum without changing its geometric cut.

The endpoint refinement depends only on the crossing hyperplane, outgoing and
incoming velocities, and the target arrangement. It is chosen before the
endpoint, incoming coefficient, propagation maps, source and obstacles. The
eventual positive displacement bound may depend on these data. All recorded
encounters and whole decorations remain in the sums, including changes of
coefficient degree with equal spatial velocity.

We combine `DecoratedAdmissibleRay.eventually_sum_finalEncounter_eq_component_sum`
with `Convex.exists_forall_eventually_isGeneric_sweepProjection`. The
last-change recursion follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite J] [Finite K]

open Classical in
/-- At generic endpoints for one geometric refinement, weighted final-encounter
attachment reads the whole incoming sum at an actual generic straight cut.
The refinement is independent of the coefficient data and the earlier encounter
word. Normal conservation and transversality ensure the cut approaches from the
incoming side, even when the two degrees have the same velocity. -/
theorem exists_eventually_sum_finalEncounter_eq_component_sum_generic
    (E : ExceptionalArrangement V) (v : Γ → V) (p q : Γ)
    (m : V →L[ℝ] ℝ) (b : ℝ)
    (hnormal : m (v q) = m (v p)) (htrans : m (v q) ≠ 0) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
        {n : ℕ} (T : Fin n → Module.End R M) {p₀ : Γ} (a : ℳ p₀)
        (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (ε : Fin n → SignType)
        (P : Fin n → Set V) (W : J → Set V) (S : K → Set V) (C H : Set V)
        (t : ℝ), 0 < t → m (Q + t • v q) = b → Q + t • v q ∈ H →
        (∀ j, IsClosed (W j)) →
        (∀ j, Q + t • v q ∈ W j → ∀ y ∈ W j, m y = b) →
        (∀ j, IsClosed (S j)) → (∀ j, Q + t • v q ∉ S j) →
        (∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ W j) →
        (∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ S j) →
        ∀ (U : Module.End R M),
        let Out := DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a v
          (Fin.cons m f) (Fin.cons b c) (Fin.cons (SignType.sign (m (v q))) ε)
          (Fin.cons H P) W S C Q
        let := Fintype.ofFinite Out
        ∀ᶠ η : ℝ in 𝓝[>] 0, ∃ Y : V,
          E.IsGeneric Y ∧ Y = Q + t • v q + η • v p ∧
          let In := DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Y
          let := Fintype.ofFinite In
          (∑ z : Out, if z.1.val 0 = q ∧
            Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p
            then z.decoration 0 else 0) =
            (DirectSum.decompose ℳ (U (∑ r : In,
              if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = p
              then r.decoration 0 else 0)) q : M) := by
  classical
  obtain ⟨F, hF⟩ := exists_forall_eventually_isGeneric_sweepProjection E
    (fun _ : Unit => m) (fun _ => b) (fun _ => (m (v q))⁻¹ • v q)
    (fun _ => v p) (fun _ => hnormal ▸ htrans)
  refine ⟨F, fun Q hQ ℳ _ n T p₀ a f c ε P W S C H t ht hh hinc
    hclosedW hplane hclosedS hregular hW hS U => ?_⟩
  dsimp only
  have htime : (b - m Q) / m (v q) = t := by
    apply (div_eq_iff htrans).mpr
    rw [map_add, map_smul, smul_eq_mul] at hh
    linarith
  have hgeneric := hF Q hQ
  simp only [sweepProjection_apply, smul_smul, ← div_eq_mul_inv, htime] at hgeneric
  filter_upwards [hgeneric,
    eventually_sum_finalEncounter_eq_component_sum (T := T) (a := a) (v := v)
      (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (C := C)
      U p q Q t ht m b H hnormal htrans hh hinc hclosedW hplane
      hclosedS hregular hW hS] with η hgen heq
  exact ⟨Q + t • v q + η • v p, hgen (), rfl, heq⟩

end Mei.DecoratedAdmissibleRay
