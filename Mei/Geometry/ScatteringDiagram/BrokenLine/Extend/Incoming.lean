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
and incident obstacles are excluded together by
`eventually_forall_pos_le_add_smul_notMem`. This is the final-encounter step of the
backward-ray recursion in Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
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

/-- A common sufficiently short incoming cut is admitted by the entire older
history of every ray with prescribed final adjacent degrees. The newly prepended
encounter is removed; arbitrary source and obstacle conditions persist. -/
theorem eventually_forall_mem_admissibleBackwardDomain_cons (U : Module.End R M) (p q : Γ)
    (Q : V) (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V) :
    let x := Q + ((b - m Q) / m (v q)) • v q
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∀ z : DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a v
        (Fin.cons m f) (Fin.cons b c) (Fin.cons (SignType.sign (m (v q))) ε)
        (Fin.cons H P) W S C Q,
      z.1.val 0 = q →
      Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p →
      x + η • v p ∈ admissibleBackwardDomain f c
        (fun j => v (Fin.snoc (α := fun _ => Γ)
          (fun i : Fin n => z.1.val i.succ) p₀ j)) P W S C := by
  -- Transport the block-cutting theorem from `Fin (1 + n)` to the `Fin.cons`
  -- convention `Fin (n + 1)` before specializing the signed encounter data.
  have cut (N : ℕ) (hN : 1 + n = N)
      (T' : Fin N → Module.End R M) (f' : Fin N → V →L[ℝ] ℝ)
      (c' : Fin N → ℝ) (ε' : Fin N → SignType) (P' : Fin N → Set V) :
      let j := Fin.cast hN (0 : Fin (1 + n))
      let x := Q + ((c' j - f' j Q) / f' j (v q)) • v q
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∀ z : DecoratedAdmissibleRay ℳ T' p₀ a v f' c' ε' P' W S C Q,
        (∀ l ≤ j.castSucc, v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ l) = v q) →
        v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ j.succ) = v p →
        x + η • v p ∈ admissibleBackwardDomain
          (fun i => f' (Fin.cast hN (Fin.natAdd 1 i)))
          (fun i => c' (Fin.cast hN (Fin.natAdd 1 i)))
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val (Fin.cast hN (Fin.natAdd 1 i))) p₀ j))
          (fun i => P' (Fin.cast hN (Fin.natAdd 1 i))) W S C := by
    subst N
    exact eventually_forall_mem_admissibleBackwardDomain
      (m := 1) (n := n) 0 rfl p q
  have hh := cut (n + 1) (Nat.add_comm 1 n) (Fin.cons U T) (Fin.cons m f) (Fin.cons b c)
    (Fin.cons (SignType.sign (m (v q))) ε) (Fin.cons H P)
  have hind (j : Fin n) :
      Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 j) = j.succ := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
    omega
  have hzero : Fin.cast (Nat.add_comm 1 n) (0 : Fin (1 + n)) = 0 := by
    apply Fin.ext
    rfl
  simp only [hzero, hind, Fin.cons_zero, Fin.cons_succ] at hh
  filter_upwards [hh] with η hη z hq hp
  have hsnoc : Fin.snoc (α := fun _ => Γ) z.1.val p₀ (0 : Fin (n + 1)).succ =
      Fin.snoc (α := fun _ => Γ) (fun i : Fin n => z.1.val i.succ) p₀ 0 := by
    rw [← Fin.cons_self_tail z.1.val, ← Fin.cons_snoc_eq_snoc_cons]
    rfl
  exact hη z (fun l hl => by
    have hl : l = 0 := by simpa using hl
    subst l
    simpa using congrArg v hq) (by rw [hsnoc]; exact congrArg v hp)

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
  have hnearW := eventually_forall_pos_le_add_smul_notMem hclosedW x (v p) m.toLinearMap
    (hnormal ▸ htrans) (fun j hj y hy => (hplane j hj y hy).trans hheight.symm)
  have hnearS := eventually_forall_pos_le_add_smul_notMem hclosedS x (v p) m.toLinearMap
    (hnormal ▸ htrans) (fun j hj => (hregular j hj).elim)
  filter_upwards [hcut, hnearW, hnearS, self_mem_nhdsWithin] with η hcut hnearW hnearS hη
  have hη : 0 < η := hη
  let Y := x + η • v p
  have hend : Y - η • v p - t • v q = Q := by simp [Y, x]
  have hline (u : ℝ) : Y - u • v p = x + (η - u) • v p := by
    dsimp only [Y]
    module
  have hW₁ : ∀ j u, 0 < u → u < η → Y - u • v p ∉ W j := by
    intro j u hu huη
    rw [hline]
    exact hnearW j (η - u) (sub_pos.mpr huη) (by linarith)
  have hS₁ : ∀ j u, 0 < u → u ≤ η → Y - u • v p ∉ S j := by
    intro j u hu huη
    rw [hline]
    rcases huη.eq_or_lt with rfl | huη
    · simpa using hregular j
    · exact hnearS j (η - u) (sub_pos.mpr huη) (by linarith)
  -- Attachment accounts for every surviving incoming component. The common cut
  -- now removes the admission test from its exact weighted image formula.
  have hh := sum_ite_decoration_finalEncounter_eq_component_sum
    (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P)
    (W := W) (S := S) (C := C) U p q Y η t hη.le ht m b H hnormal htrans
    (by simpa only [Y, add_sub_cancel_right] using hheight) (by simpa [Y] using hinc) hW₁
    (by simpa only [hend] using hW) hS₁ (by simpa only [hend] using hS)
  rw [hend] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z.1.val 0 = q ∧
      Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p
  · rw [ite_eq_left hz, ite_eq_left ⟨hz.1, hz.2, hcut z hz.1 hz.2⟩]
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz ⟨h.1, h.2.1⟩)]

end Mei.DecoratedAdmissibleRay
