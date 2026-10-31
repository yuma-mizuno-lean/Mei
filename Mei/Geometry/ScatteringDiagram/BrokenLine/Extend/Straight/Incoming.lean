/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend.Straight.Fiber
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut.Incoming
public import Mei.Geometry.Affine.Segment

/-!
# Complete weighted fibers across unchanged terminal blocks

Cut immediately before the oldest encounter of a nonempty straight terminal
block. At every sufficiently small positive displacement, the whole outgoing
fiber with unchanged terminal degree has the same weighted sum as the incoming
fiber of that degree. An arbitrary selection on the older degree history is
retained, so the result can isolate a preceding degree-changing encounter.
The older encounter word is fixed, while all its degree histories are summed.

Unlike the exact attachment-image formula, this equality has no incoming-domain
test on outgoing rays. Uniform cuts supply that admission, while closedness of
nonincident obstacles and transversality at incident walls let all incoming
rays continue across the prescribed block. The original source, singular
avoidance, whole decorations and multiplicities remain in both fibers.

We combine `sum_ite_decoration_straightTerminal_eq_sum` with
`eventually_forall_mem_admissibleBackwardDomain` and the stability of segments
avoiding closed sets. The short incoming-segment argument follows
`eventually_sum_finalEncounter_eq_component_sum`. This is the unchanged terminal
part of the last-change recursion in Mandel, *Scattering diagrams, theta functions,
and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {m n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V}

open Classical in
/-- Across a nonempty unchanged terminal block, the complete outgoing weighted
fiber equals the incoming degree fiber at every sufficiently short straight cut.
The backward encounter times `s` increase from the endpoint toward the incoming
tail. The predicate `B` can select any older degree histories. Only the prescribed
finite outgoing segment needs a separate avoidance check. -/
theorem eventually_sum_straightTerminal_eq_sum [Finite J] [Finite K]
    (U : Fin (m + 1) → Module.End R M) (q : Γ) (Q : V)
    (hU : ∀ j x, x ∈ ℳ q → (DirectSum.decompose ℳ (U j x) q : M) = x)
    (s : Fin (m + 1) → ℝ) (hs : StrictMono s) (hpos : ∀ j, 0 < s j)
    (g : Fin (m + 1) → V →L[ℝ] ℝ) (b : Fin (m + 1) → ℝ)
    (H : Fin (m + 1) → Set V)
    (htrans : ∀ j, g j (v q) ≠ 0)
    (hheight : ∀ j, g j (Q + s j • v q) = b j)
    (hinc : ∀ j, Q + s j • v q ∈ H j)
    (hclosedW : ∀ j, IsClosed (W j))
    (hplane : ∀ j, Q + s (Fin.last m) • v q ∈ W j →
      ∀ y ∈ W j, g (Fin.last m) y = b (Fin.last m))
    (hclosedS : ∀ j, IsClosed (S j))
    (hW : ∀ j t, 0 ≤ t → t < s (Fin.last m) →
      (∀ i, t ≠ s i) → Q + t • v q ∉ W j)
    (hS : ∀ j t, 0 ≤ t → t ≤ s (Fin.last m) → Q + t • v q ∉ S j)
    (B : (Fin n → Γ) → Prop) :
    let Out := DecoratedAdmissibleRay ℳ (Fin.append U T) p₀ a v
      (Fin.append g f) (Fin.append b c)
      (Fin.append (fun j => SignType.sign (g j (v q))) ε)
      (Fin.append H P) W S C Q
    let := Fintype.ofFinite Out
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      let In := DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C
        (Q + (s (Fin.last m) + η) • v q)
      let := Fintype.ofFinite In
      (∑ z : Out,
        if (∀ j : Fin (m + 1), z.1.val (Fin.castAdd n j) = q) ∧
          Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val (Fin.natAdd (m + 1) j))
            p₀ 0 = q ∧ B (fun j => z.1.val (Fin.natAdd (m + 1) j))
        then z.decoration 0 else 0) =
      ∑ r : In, if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = q ∧ B r.1.val
        then r.decoration 0 else 0 := by
  classical
  dsimp only
  let Out := DecoratedAdmissibleRay ℳ (Fin.append U T) p₀ a v
    (Fin.append g f) (Fin.append b c)
    (Fin.append (fun j => SignType.sign (g j (v q))) ε)
    (Fin.append H P) W S C Q
  let := Fintype.ofFinite Out
  let j : Fin (m + 1 + n) := Fin.castAdd n (Fin.last m)
  let t := s (Fin.last m)
  let x := Q + t • v q
  have htime : (b (Fin.last m) - g (Fin.last m) Q) / g (Fin.last m) (v q) = t := by
    apply (div_eq_iff (htrans _)).mpr
    have hh := hheight (Fin.last m)
    rw [map_add, map_smul, smul_eq_mul] at hh
    linarith
  -- First cut every outgoing history uniformly before the oldest terminal event.
  -- The finite history inventory makes one displacement bound suffice.
  have hcut := eventually_forall_mem_admissibleBackwardDomain
    (T := Fin.append U T) (a := a) (v := v) (f := Fin.append g f)
    (c := Fin.append b c) (ε := Fin.append (fun j => SignType.sign (g j (v q))) ε)
    (P := Fin.append H P) (W := W) (S := S) (C := C) (Q := Q)
    (m := m + 1) (n := n) j (by simp [j]) q q
  simp only [j, Fin.append_left, Fin.append_right, htime] at hcut
  -- For the converse attachment, closed nonincident obstacles miss a short
  -- incoming segment; incident walls are excluded by their transverse normal.
  have hnear := eventually_add_smul_pair x (v q) 0
    ((eventually_forall_lineMap_notMem_of_notMem hclosedW x).and
      (eventually_forall_lineMap_notMem_of_notMem hclosedS x))
  filter_upwards [hcut, hnear, self_mem_nhdsWithin] with η hcut hnear hη
  have hη : 0 < η := hη
  let L := t + η
  let Y := Q + L • v q
  let τ (i : Fin (m + 1)) := L - s i
  have hend : Y - L • v q = Q := by simp [Y]
  have hpoint (u : ℝ) : Y - u • v q = Q + (L - u) • v q := by
    dsimp only [Y]
    module
  have hline (u : ℝ) :
      AffineMap.lineMap (x + η • v q) (x + η • (0 : V)) (u / η) =
        Q + (t + η - u) • v q := by
    simp only [AffineMap.lineMap_apply_module', smul_zero, add_zero, smul_sub,
      smul_add, smul_smul, div_mul_cancel₀ u hη.ne']
    dsimp only [x]
    module
  have havoidW : ∀ w u, 0 < u → u ≤ L → (∀ i, u ≠ τ i) → Y - u • v q ∉ W w := by
    intro w u hu huL huτ
    rw [hpoint]
    by_cases huη : η < u
    · apply hW w (L - u) (by linarith) (by dsimp only [L]; linarith)
      intro i he
      exact huτ i (by dsimp only [τ]; linarith)
    · have hule : u ≤ η := le_of_not_gt huη
      have hstrict : u < η := lt_of_le_of_ne hule (by
        simpa only [τ, L, t, add_sub_cancel_left] using huτ (Fin.last m))
      intro hy
      by_cases hw : x ∈ W w
      · have he := hplane w hw _ hy
        have he' : g (Fin.last m) (Q + (L - u) • v q) =
            b (Fin.last m) + (η - u) * g (Fin.last m) (v q) := by
          have hh := hheight (Fin.last m)
          simp only [map_add, map_smul, smul_eq_mul] at hh ⊢
          dsimp only [L, t]
          nlinarith
        rw [he'] at he
        exact (mul_ne_zero (sub_pos.mpr hstrict).ne' (htrans _)) (by linarith)
      · apply hnear.1 w hw (u / η)
          ⟨(div_pos hu hη).le, (div_le_one hη).mpr hule⟩
        rw [hline]
        exact hy
  have havoidS : ∀ w u, 0 < u → u ≤ L → Y - u • v q ∉ S w := by
    intro w u hu huL
    rw [hpoint]
    by_cases huη : η ≤ u
    · exact hS w (L - u) (by linarith) (by dsimp only [L]; linarith)
    · have hw : x ∉ S w := hS w t (hpos _).le le_rfl
      have hh := hnear.2 w hw (u / η)
        ⟨(div_pos hu hη).le, (div_le_one hη).mpr (le_of_lt (lt_of_not_ge huη))⟩
      rw [hline] at hh
      exact hh
  -- Apply the exact weighted-image theorem to the complete terminal block,
  -- then use the uniform cut to remove its incoming-admission condition.
  have hsum := sum_ite_decoration_straightTerminal_eq_sum
    (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P)
    (W := W) (S := S) (C := C) U q Y hU L (by dsimp only [L]; linarith [hpos (Fin.last m)])
    τ (fun i i' hi => by dsimp only [τ]; linarith [hs hi])
    (fun i => by dsimp only [τ, L]; linarith [hs.monotone (Fin.le_last i)])
    (fun i => by dsimp only [τ]; linarith [hpos i]) g b H htrans
    (fun i => by simpa only [hpoint, τ, sub_sub_cancel] using hheight i)
    (fun i => by simpa only [hpoint, τ, sub_sub_cancel] using hinc i)
    havoidW havoidS B
  rw [hend] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (∀ i : Fin (m + 1), z.1.val (Fin.castAdd n i) = q) ∧
      Fin.snoc (α := fun _ => Γ) (fun i : Fin n => z.1.val (Fin.natAdd (m + 1) i)) p₀ 0 = q ∧
      B (fun i => z.1.val (Fin.natAdd (m + 1) i))
  · have hv : ∀ l ≤ j.castSucc, v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ l) = v q := by
      intro l hl
      have hlt : l.val < m + 1 := by
        have hl' := Fin.le_iff_val_le_val.mp hl
        dsimp only [j] at hl'
        simp only [Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hl'
        omega
      have he : l = (Fin.castAdd n (⟨l.val, hlt⟩ : Fin (m + 1))).castSucc := by
        ext
        rfl
      rw [he, Fin.snoc_castSucc, hz.1]
    -- Mathlib's snoc_comp_natAdd identifies the incoming boundary degree,
    -- including when the older encounter word is empty.
    have hp : v (Fin.snoc (α := fun _ => Γ) z.1.val p₀ j.succ) = v q := by
      have he : j.succ = Fin.natAdd (m + 1) (0 : Fin (n + 1)) := by ext; simp [j]
      rw [he]
      exact congrArg v ((congrFun (Fin.snoc_comp_natAdd z.1.val p₀) 0).trans hz.2.1)
    have hd := hcut z hv hp
    have hY : x + η • v q = Y := by dsimp only [x, Y, L]; module
    rw [hY] at hd
    rw [ite_eq_left hz, ite_eq_left ⟨hz.1, hz.2.1, hd, hz.2.2⟩]
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz ⟨h.1, h.2.1, h.2.2.2⟩)]

end Mei.DecoratedAdmissibleRay
