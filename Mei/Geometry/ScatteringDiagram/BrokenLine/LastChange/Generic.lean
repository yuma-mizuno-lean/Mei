/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.LastChange.Cut
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# Generic lower-degree cuts at the last changing encounter

Choose one finite arrangement of outgoing endpoints so that every actual ray's
last-change incoming cuts are generic for a prescribed incoming arrangement.
At each allowed endpoint one sufficiently small positive displacement works for
all outgoing rays and all their encounter words. The cuts are actual rays at
one lower cutoff, retaining every older encounter, the whole incoming decoration
and the entire incoming path. Their final degrees are strictly smaller.

The arrangement depends only on the cutoff, velocities, supporting hyperplanes
and incoming arrangement. Coefficients, propagation maps, sources and obstacles
are chosen afterwards. Normal-velocity conservation supplies the transversality
needed for genericity, including degree changes with equal spatial velocities.
This permits degree induction on the incoming weighted evaluations at the exact
straight cut points, without perturbing a contributing path.

We combine `CutoffDecoratedRay.eventually_exists_lastChange_incoming`,
`CutoffDecoratedRay.lastChangeIndex_localization` and
`Convex.exists_forall_eventually_isGeneric_sweepProjection`. The last-change
recursion follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Mei.Convex
open scoped Topology

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]

/-- One geometric endpoint arrangement makes all last-change incoming cuts
generic. For every sufficiently small common displacement, each outgoing ray
with nonzero final degree supplies an actual lower-cutoff incoming ray of
strictly smaller degree. Its complete older word, whole incoming decoration and
entire incoming path are preserved. The coefficient data and geometric admission
conditions do not enter the choice of arrangement. -/
theorem exists_eventually_lastChange_incoming_generic
    (d : PositiveDegrees Γ) (k : ℕ) (E : ExceptionalArrangement V)
    (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
        (T : J → Module.End R M) (a : ℳ 0) (ε : J → SignType)
        (P W : J → Set V) (S : K → Set V) (C : Set V),
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∀ r : CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q,
        ∀ hq : r.finalDegree ≠ 0,
          let j := r.lastChangeIndex hq
          let p := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ
          let x := r.realization.2.ray (r.realization.2.parameter j.succ)
          E.IsGeneric (x + η • v p) ∧
          ∃ s : CutoffDecoratedRay d ℳ T a v f c ε P W S C (k - 1) (x + η • v p),
            s.itinerary = r.itinerary.drop (j.val + 1) ∧
            s.finalDegree = p ∧ d.degree s.finalDegree < d.degree r.finalDegree ∧
            s.decoration = r.realization.decoration j.succ ∧
            ∀ u ≤ 0, s.realization.2.ray u =
              r.realization.2.ray (u + (r.realization.2.parameter j.succ - η)) := by
  classical
  -- Both adjacent degrees lie in a finite cutoff. Keep only transverse
  -- incoming directions; the actual rays satisfy this by normal conservation.
  let I := {z : J × d.cutoff k × d.cutoff k // f z.1 (v z.2.2.val) ≠ 0}
  obtain ⟨F, hF⟩ := exists_forall_eventually_isGeneric_sweepProjection E
    (fun z : I => f z.val.1) (fun z => c z.val.1)
    (fun z => (f z.val.1 (v z.val.2.1.val))⁻¹ • v z.val.2.1.val)
    (fun z => v z.val.2.2.val) (fun z => z.property)
  refine ⟨F, fun Q hQ ℳ _ T a ε P W S C => ?_⟩
  let Rays := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
  have hcut := eventually_all.mpr fun r : {r : Rays // r.finalDegree ≠ 0} =>
    r.val.eventually_exists_lastChange_incoming r.property
  filter_upwards [hF Q hQ, hcut] with η hgen hcut r hq
  dsimp only
  let j := r.lastChangeIndex hq
  let p := Fin.snoc (α := fun _ => Γ) r.realization.1.val 0 j.succ
  let w := r.itinerary.get j
  obtain ⟨htrans, _, _, hx, _, _, hlt⟩ := r.lastChangeIndex_localization hq
  have hp : p ∈ d.cutoff k := by
    dsimp only [p]
    exact Fin.lastCases (by simp [d.monoid.zero_mem])
      (fun i => by simpa only [Fin.snoc_castSucc] using r.degree_mem i) j.succ
  have hj : r.realization.1.val j = r.finalDegree := by
    simpa only [Fin.snoc_castSucc] using (r.lastChangeIndex_spec hq).2 j.castSucc le_rfl
  have hn : f w (v p) ≠ 0 := by
    rw [← r.realization.normal_velocity_eq j, hj]
    exact htrans
  let z : I := ⟨(w, ⟨r.finalDegree, r.finalDegree_mem_cutoff⟩, ⟨p, hp⟩), hn⟩
  have hgeneric := hgen z
  simp only [z, sweepProjection_apply, smul_smul, ← div_eq_mul_inv] at hgeneric
  rw [← hx] at hgeneric
  refine ⟨hgeneric, ?_⟩
  obtain ⟨s, hw, hs, ha, hpath⟩ := hcut ⟨r, hq⟩
  exact ⟨s, hw, hs, by rw [hs]; exact hlt, ha, hpath⟩

end Mei.CutoffDecoratedRay
