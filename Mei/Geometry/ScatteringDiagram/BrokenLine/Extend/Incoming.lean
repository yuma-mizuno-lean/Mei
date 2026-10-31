/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Fiber
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut.Incoming
public import Mei.Geometry.Affine.Segment

/-!
# Weighted final encounters at incoming germs

At a transverse final encounter, sum the outgoing rays with prescribed adjacent
coefficient degrees. For every sufficiently small incoming displacement, this
sum is the selected component of the wall action on the entire incoming ray
sum. The outgoing sum has no extra incoming-domain test: cutting the finite
outgoing fiber supplies that admission uniformly. Conversely, local avoidance
and the fixed outgoing segment let every surviving incoming ray attach.

The incoming source and all wall and singular obstacles remain in both fibers.
Whole decorations, killed components and multiplicities are retained over an
arbitrary semiring. No diagonal-preservation assumption is needed.

We combine `sum_ite_decoration_finalEncounter_eq_component_sum` with
`eventually_forall_mem_admissibleBackwardDomain`. Closed nonincident obstacles
and incident walls are excluded using `eventually_incomingSegment_notMem`. This
is the final-encounter step of the backward-ray recursion in Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V}

open Classical in
/-- At every sufficiently short incoming germ, the complete outgoing fiber
with prescribed last two degrees is obtained by propagating the incoming
fiber sum and taking its whole degree-`q` component. Incident obstacles lie
in the crossing hyperplane; nonincident obstacles and singular sets are closed.
Only the fixed outgoing segment needs a separate avoidance check. -/
theorem eventually_sum_finalEncounter_eq_component_sum [Finite J] [Finite K]
    (U : Module.End R M) (p q : Γ) (Q : V) (t : ℝ) (ht : 0 < t)
    (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
    (hnormal : m (v q) = m (v p)) (htrans : m (v q) ≠ 0)
    (hheight : m (Q + t • v q) = b) (hinc : Q + t • v q ∈ H)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + t • v q ∈ W j → ∀ y ∈ W j, m y = b)
    (hclosedS : ∀ j, IsClosed (S j)) (hregular : ∀ j, Q + t • v q ∉ S j)
    (hW : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ W j)
    (hS : ∀ j u, -t < u → u ≤ 0 → Q - u • v q ∉ S j) :
    let E := DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a v
      (Fin.cons m f) (Fin.cons b c) (Fin.cons (SignType.sign (m (v q))) ε)
      (Fin.cons H P) W S C Q
    let := Fintype.ofFinite E
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      let D := DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C
        (Q + t • v q + η • v p)
      let := Fintype.ofFinite D
      (∑ z : E, if z.1.val 0 = q ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p
        then z.decoration 0 else 0) =
      (DirectSum.decompose ℳ (U (∑ r : D, if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = p
          then r.decoration 0 else 0)) q : M) := by
  classical
  dsimp only
  let x := Q + t • v q
  have htime : (b - m Q) / m (v q) = t := by
    apply (div_eq_iff htrans).mpr
    have hh := hheight
    rw [map_add, map_smul, smul_eq_mul] at hh
    linarith
  -- A common cut admits the complete earlier history of every outgoing ray.
  have hcut := eventually_forall_mem_admissibleBackwardDomain_cons (T := T) (a := a) (v := v)
    (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (C := C) U p q Q m b H
  rw [htime] at hcut
  -- Closed nonincident obstacles are avoided on a short incoming segment.
  -- Transversality excludes the incident hyperplane away from the encounter.
  have hnear := eventually_incomingSegment_notMem x (v p) m.toLinearMap b
    (hnormal ▸ htrans) hheight hclosedW hplane hclosedS hregular
  filter_upwards [hcut, hnear, self_mem_nhdsWithin] with η hcut hnear hη
  have hη : 0 < η := hη
  let Y := x + η • v p
  have hend : Y - η • v p - t • v q = Q := by simp [Y, x]
  -- Attachment accounts for every surviving incoming component. The common cut
  -- now removes the admission test from its exact weighted image formula.
  have hh := sum_ite_decoration_finalEncounter_eq_component_sum
    (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P)
    (W := W) (S := S) (C := C) U p q Y η t hη.le ht m b H hnormal htrans
    (by simpa only [Y, add_sub_cancel_right] using hheight) (by simpa [Y] using hinc) hnear.1
    (by simpa only [hend] using hW) hnear.2 (by simpa only [hend] using hS)
  rw [hend] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.1.val 0 = q ∧
      Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p
  · rw [ite_eq_left hz, ite_eq_left ⟨hz.1, hz.2, hcut z hz.1 hz.2⟩]
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz ⟨h.1, h.2.1⟩)]

end Mei.DecoratedAdmissibleRay
