/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Cut.Incoming

/-!
# Uniform incoming cuts across cutoff encounter words

Cut an actual cutoff ray immediately before any boundary between its encounter
blocks. The incoming ray remains in the same cutoff inventory and retains its
whole decoration, complete degree-labelled encounter suffix and entire incoming
path. No change of degree is required: unchanged terminal blocks and shifts with
unchanged spatial velocity are both allowed.

For a finite encounter alphabet, one sufficiently small positive displacement
works for every ray and every recorded encounter at a fixed endpoint. When the
terminal piece is straight, the cut endpoint is its explicit backward hyperplane
intersection plus the incoming displacement. This supplies actual incoming rays
when removing admission tests from weighted terminal-block comparisons, without
assuming that arbitrary incoming rays extend.

We use `DecoratedAdmissibleRay.eventually_exists_incoming_truncate` and
`CutoffDecoratedRay.exists_of_word`, preserving their source and obstacle
conditions, and Mathlib's `Filter.eventually_all` for the finite inventory.
The cutting convention follows Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P W : J → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

local notation "Rays" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q

/-- Cut just before any encounter-block boundary, including the endpoint or
the beginning of the unbounded incoming segment. Every sufficiently short cut
retains the complete older degree-labelled word, whole boundary coefficient and
entire incoming path in the original cutoff inventory. -/
theorem eventually_exists_incoming_truncate (r : Rays)
    (j : Fin (r.itinerary.length + 1)) :
    let p := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      ∃ s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k
          (r.realization.2.ray (r.realization.2.parameter j) + η • v p),
        s.itinerary = r.itinerary.drop j.val ∧
        s.finalDegree = p ∧ s.decoration = r.realization.decoration j ∧
        s.degreeItinerary = r.degreeItinerary.drop j.val ∧
        ∀ u ≤ 0, s.realization.2.ray u =
          r.realization.2.ray (u + (r.realization.2.parameter j - η)) := by
  -- Split the length-indexed realization at the chosen boundary before
  -- packaging the retained tuple back into the list-indexed cutoff inventory.
  have cut {N : ℕ} (word : Fin N → J)
      (z : DecoratedAdmissibleRay ℳ (fun i => T (word i)) 0 a v
        (fun i => f (word i)) (fun i => c (word i))
        (fun i => ε (word i)) (fun i => P (word i)) W S C Q)
      (hm : ∀ i, z.1.val i ∈ d.cutoff k)
      (hmono : ∀ i l, i ≤ l → z.1.val i - z.1.val l ∈ d.monoid)
      (j : Fin (N + 1)) :
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∃ s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k
            (z.2.ray (z.2.parameter j) +
              η • v (Fin.snoc (α := fun _ => Γ) z.1.val 0 j)),
          s.itinerary = (List.ofFn word).drop j.val ∧
          s.finalDegree = Fin.snoc (α := fun _ => Γ) z.1.val 0 j ∧
          s.decoration = z.decoration j ∧
          s.degreeItinerary = (List.ofFn (fun i => (z.1.val i, word i))).drop j.val ∧
          ∀ u ≤ 0, s.realization.2.ray u =
            z.2.ray (u + (z.2.parameter j - η)) := by
    obtain ⟨j, hj⟩ := j
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hj)
    let i : Fin (j + n + 1) := Fin.natAdd j (0 : Fin (n + 1))
    have hi : (⟨j, hj⟩ : Fin (j + n + 1)) = i := Fin.ext (by simp [i])
    rw [hi]
    filter_upwards [z.eventually_exists_incoming_truncate (m := j) (n := n)] with η hη
    obtain ⟨s, hs, ha, _, hr⟩ := hη
    -- Restrict the existing cutoff and monotonicity bounds to the older tuple.
    have hmem : ∀ l : Fin n, s.1.val l ∈ d.cutoff k := by
      intro l
      rw [hs]
      exact hm _
    have hsub : ∀ l l', l ≤ l' → s.1.val l - s.1.val l' ∈ d.monoid := by
      intro l l' hll'
      rw [hs]
      exact hmono _ _ (by simpa only [Fin.le_def, Fin.val_natAdd,
        Nat.add_le_add_iff_left] using hll')
    -- The packaging theorem preserves the whole path and all degree labels.
    obtain ⟨b, hw, hb, hd, hp, hword, _⟩ :=
      exists_of_word (fun l : Fin n => word (Fin.natAdd j l)) s hmem hsub
    refine ⟨b, ?_, ?_, hd.trans (ha 0), ?_, fun u hu => ?_⟩
    · rw [List.ofFn_add]
      simpa [i] using hw
    · rw [hp, hs]
      exact (congrFun (Fin.snoc_comp_natAdd z.1.val 0) 0).symm
    · rw [hs] at hword
      rw [List.ofFn_add]
      simpa [i] using hword
    · rw [hb]
      exact hr u hu
  simpa only [List.ofFn_get, ← degreeItinerary_eq] using
    cut r.itinerary.get r.realization r.degree_mem r.degree_sub_mem j

/-- One displacement cuts every cutoff ray at every straight terminal boundary.
The incoming endpoint is determined by the selected wall and the two prescribed
directions, independently of the older encounter word. Unchanged encounters may
follow the cut, and the incoming degree need not differ from the final degree.
The bound is chosen before the degrees `p` and `q`. -/
theorem eventually_exists_straightTerminal_incoming [Finite J] :
    ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ r : Rays, ∀ j : Fin r.itinerary.length, ∀ p q : Γ,
      (∀ i ≤ j.castSucc,
        v (Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 i) = v q) →
      Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ = p →
      ∃ s : CutoffDecoratedRay d ℳ T a v f c ε P W S C k
          (Q + ((c (r.itinerary.get j) - f (r.itinerary.get j) Q) /
            f (r.itinerary.get j) (v q)) • v q + η • v p),
        s.itinerary = r.itinerary.drop (j.val + 1) ∧
        s.finalDegree = p ∧ s.decoration = r.realization.decoration j.succ ∧
        s.degreeItinerary = r.degreeItinerary.drop (j.val + 1) ∧
        ∀ u ≤ 0, s.realization.2.ray u =
          r.realization.2.ray (u + (r.realization.2.parameter j.succ - η)) := by
  have hcuts := eventually_all.mpr (fun r : Rays =>
    eventually_all.mpr (fun j : Fin r.itinerary.length =>
      r.eventually_exists_incoming_truncate j.succ))
  filter_upwards [hcuts] with η hη r j p q hv hp
  have hzero := hv 0 (Fin.zero_le _)
  have ht := r.realization.2.parameter_eq_div_of_directions_eq j
    (fun i hi => (hv i hi).trans hzero.symm)
  have hx := r.realization.2.ray_eq_endpoint_sub_smul j.succ
    (fun i hi => (hv i (Fin.le_castSucc_iff.mpr hi)).trans hzero.symm)
    (t := r.realization.2.parameter j.succ)
    ⟨le_rfl, by simpa only [r.realization.2.parameter_zero] using
      r.realization.2.strictAnti_parameter.antitone (Fin.zero_le j.succ)⟩
  rw [hzero] at ht hx
  have hpoint : r.realization.2.ray (r.realization.2.parameter j.succ) =
      Q + ((c (r.itinerary.get j) - f (r.itinerary.get j) Q) /
        f (r.itinerary.get j) (v q)) • v q := by
    rw [hx, ht]
    simp only [← neg_sub (c (r.itinerary.get j)) (f (r.itinerary.get j) Q),
      neg_div, neg_smul, sub_neg_eq_add]
  have hcut := hη r j
  rw [hpoint, hp] at hcut
  simpa only [Fin.val_succ] using hcut

end Mei.CutoffDecoratedRay
