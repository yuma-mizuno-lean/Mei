/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Attachment.Incoming
public import Mei.Geometry.Convex.Sweep.Generic
public import Mei.Geometry.Convex.Polyhedron.WallEvent

/-!
# Complete final-encounter sums at generic incoming cuts

Choose one geometric endpoint arrangement for all encounters and pairs of
retained degrees. At each generic endpoint, one sufficiently small positive
displacement works simultaneously for the complete final-encounter fibers.
Their weighted sums are components of propagation of the entire incoming
weighted evaluation, at generic straight incoming points. The incoming sum may
use any enumeration cutoff retaining its degree, including a lower cutoff at a
positive degree change.

Every older encounter word is summed. The original source admission, wall and
singular avoidance, and whole decorations are retained, with no residual
incoming-domain test. Degrees with equal spatial velocities remain distinct.
The endpoint arrangement is chosen before coefficients, propagation, sources
and obstacles; the displacement bound can depend on these data.
For canonical signed simultaneous events of closed walls, regularity of the
crossing discharges the closure condition even though event supports are not
closed. The specialization uses `AffineMap.eqOn_affineSpan` and
`Convex.affineSpan_eq_of_notMem_singularSupport`.

We combine `CutoffDecoratedRay.eventually_sum_finalEncounter_eq_component`
with `Convex.exists_forall_eventually_isGeneric_sweepProjection`, using finite
cutoffs to make the displacement uniform. The fixed-word generic attachment
argument is `DecoratedAdmissibleRay.exists_eventually_sum_finalEncounter_eq_component_sum_generic`.
For the last-change recursion see Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite J] [Finite K]

open Classical in
/-- At generic endpoints for a single geometric arrangement, one displacement
bound gives the complete weighted final-encounter identity at generic incoming
points for every retained degree pair and encounter. The incoming enumeration
cutoff is arbitrary provided it retains the incoming degree. Only the prescribed
outgoing segment must be checked separately for avoidance. No consistency,
coefficient basis, diagonal preservation or nonzero degree-shift velocity is
required. -/
theorem exists_eventually_sum_finalEncounter_eq_component_generic
    (d : PositiveDegrees Γ) (k : ℕ) (E : ExceptionalArrangement V)
    (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
        (T : J → Module.End R M) (a : ℳ 0) (ε : J → SignType)
        (P W : J → Set V) (S : K → Set V) (C : Set V),
      (∀ j, IsClosed (S j)) →
      let Out := CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
      let := Fintype.ofFinite Out
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∀ (w : J) (p q : d.cutoff k),
          let t := (c w - f w Q) / f w (v q.val)
          q.val - p.val ∈ d.monoid → 0 < t →
          f w (v q.val) = f w (v p.val) → f w (v q.val) ≠ 0 →
          SignType.sign (f w (v q.val)) = ε w → Q + t • v q.val ∈ P w →
          (∀ j, Q + t • v q.val ∈ closure (W j) →
            ∀ y ∈ closure (W j), f w y = c w) →
          (∀ j, Q + t • v q.val ∉ S j) →
          (∀ j u, -t < u → u ≤ 0 → Q - u • v q.val ∉ W j) →
          (∀ j u, -t < u → u ≤ 0 → Q - u • v q.val ∉ S j) →
          E.IsGeneric (Q + t • v q.val + η • v p.val) ∧
          ∀ l : ℕ, d.degree p.val ≤ l →
            (∑ z : Out,
              if (match z with
                | ⟨[], _, _, _⟩ => False
                | ⟨j :: word, z, _, _⟩ => j = w ∧ z.1.val 0 = q.val ∧
                  Fin.snoc (α := fun _ => Γ)
                    (fun i : Fin word.length => z.1.val i.succ) 0 0 = p.val)
              then z.decoration else 0) =
            (DirectSum.decompose ℳ (T w (DirectSum.decompose ℳ
              (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C l
                (Q + t • v q.val + η • v p.val)) p.val)) q.val : M) := by
  classical
  -- Restrict the finite direction inventory to transverse incoming directions.
  -- Normal conservation at an actual encounter supplies this condition.
  let I := {z : J × d.cutoff k × d.cutoff k // f z.1 (v z.2.1.val) ≠ 0}
  obtain ⟨F, hF⟩ := exists_forall_eventually_isGeneric_sweepProjection E
    (fun z : I => f z.val.1) (fun z => c z.val.1)
    (fun z => (f z.val.1 (v z.val.2.2.val))⁻¹ • v z.val.2.2.val)
    (fun z => v z.val.2.1.val) (fun z => z.property)
  refine ⟨F, fun Q hQ ℳ _ T a ε P W S C hclosedS => ?_⟩
  dsimp only
  -- The indices and all their proof arguments are finite. Move them outside
  -- the eventual quantifier to obtain one bound for every admissible encounter.
  simp only [eventually_all]
  intro w p q hqp ht hnormal htrans hsign hinc hplane hregular hW hS
  let t := (c w - f w Q) / f w (v q.val)
  have hheight : f w (Q + t • v q.val) = c w := by
    rw [map_add, map_smul, smul_eq_mul]
    dsimp only [t]
    rw [div_mul_cancel₀ _ htrans]
    ring
  let z : I := ⟨(w, p, q), hnormal ▸ htrans⟩
  have hgeneric := (hF Q hQ).mono fun η hη => hη z
  simp only [z, sweepProjection_apply, smul_smul, ← div_eq_mul_inv] at hgeneric
  have hsum := eventually_sum_finalEncounter_eq_component
    (d := d) (ℳ := ℳ) (T := T) (a := a) (v := v) (f := f) (c := c)
    (ε := ε) (P := P) (W := W) (S := S) (C := C) (k := k) (Q := Q)
    w p.val q.val k (d.mem_cutoff.mp p.property).2 q.property hqp t ht
    hnormal htrans hsign hheight hinc hplane hclosedS hregular hW hS
  filter_upwards [hgeneric, hsum] with η hgen heq
  refine ⟨hgen, fun l hl => ?_⟩
  rw [← decompose_cutoffDecoratedEvaluation_eq_of_degree_le p.val
    (d.mem_cutoff.mp p.property).2 hl]
  -- The two dependent list matchers agree after exposing the encounter word.
  convert heq using 1
  apply Finset.sum_congr rfl
  rintro ⟨word, r, hm, hmono⟩ _
  cases word <;> rfl

section WallEvents

variable {ι : Type*} [Finite ι]

open Classical in
/-- For canonical signed simultaneous events of closed walls, regularity of the
crossing supplies the closure condition in the complete generic attachment
formula. Event supports themselves need not be closed. The outgoing segment
misses the walls except at the prescribed encounter and avoids singular support
including at that encounter. Every coincident wall index remains recorded. -/
theorem exists_eventually_sum_finalEncounter_eq_component_generic_wallEvents
    [FiniteDimensional ℝ V]
    (d : PositiveDegrees Γ) (k : ℕ) (E : ExceptionalArrangement V)
    (v : Γ → V) (W : ι → Set V) (hclosed : ∀ j, IsClosed (W j))
    (f : ι → V →L[ℝ] ℝ) (c : ι → ℝ)
    (hc : ∀ j x, x ∈ W j → f j x = c j) :
    ∃ F : ExceptionalArrangement V, ∀ Q, F.IsGeneric Q →
      ∀ (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
        (T : WallEvent ι → Module.End R M) (a : ℳ 0) (C : Set V),
      let P := fun e : WallEvent ι => e.support W
      let Out := CutoffDecoratedRay d ℳ T a v (fun e => e.normal f)
        (fun e => e.offset c) (fun e => e.2) P P (fun _ : Unit => singularSupport W) C k Q
      let := Fintype.ofFinite Out
      ∀ᶠ η : ℝ in 𝓝[>] 0,
        ∀ (e : WallEvent ι) (p q : d.cutoff k),
          let t := (e.offset c - e.normal f Q) / e.normal f (v q.val)
          q.val - p.val ∈ d.monoid → 0 < t →
          e.normal f (v q.val) = e.normal f (v p.val) → e.normal f (v q.val) ≠ 0 →
          SignType.sign (e.normal f (v q.val)) = e.2 → Q + t • v q.val ∈ P e →
          (∀ j u, -t < u → u ≤ 0 → Q - u • v q.val ∉ W j) →
          (∀ u, -t ≤ u → u ≤ 0 → Q - u • v q.val ∉ singularSupport W) →
          E.IsGeneric (Q + t • v q.val + η • v p.val) ∧
          ∀ l : ℕ, d.degree p.val ≤ l →
            (∑ z : Out,
              if (match z with
                | ⟨[], _, _, _⟩ => False
                | ⟨j :: word, z, _, _⟩ => j = e ∧ z.1.val 0 = q.val ∧
                  Fin.snoc (α := fun _ => Γ)
                    (fun i : Fin word.length => z.1.val i.succ) 0 0 = p.val)
              then z.decoration else 0) =
            (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
              (cutoffDecoratedEvaluation d ℳ T a v (fun e => e.normal f)
                (fun e => e.offset c) (fun e => e.2) P P
                (fun _ : Unit => singularSupport W) C l
                (Q + t • v q.val + η • v p.val)) p.val)) q.val : M) := by
  classical
  obtain ⟨F, hF⟩ := exists_eventually_sum_finalEncounter_eq_component_generic
    (R := R) (M := M) (K := Unit) d k E v (fun e : WallEvent ι => e.normal f)
    (fun e => e.offset c)
  refine ⟨F, fun Q hQ ℳ _ T a C => ?_⟩
  dsimp only
  have hsum := hF Q hQ ℳ T a (fun e => e.2) (fun e => e.support W)
    (fun e => e.support W) (fun _ : Unit => singularSupport W) C
    (fun _ => isClosed_singularSupport W hclosed)
  filter_upwards [hsum] with η hη e p q hqp ht hnormal htrans hsign hinc hW hS
  let t := (e.offset c - e.normal f Q) / e.normal f (v q.val)
  let x := Q + t • v q.val
  have hregular : x ∉ singularSupport W := by
    simpa only [x, neg_smul, sub_neg_eq_add] using hS (-t) le_rfl (by linarith)
  -- Closure of an exact incidence stratum lies in each recorded closed wall.
  -- At a regular crossing those walls share the crossing's affine span.
  have hplane (e' : WallEvent ι) (hx : x ∈ closure (e'.support W)) :
      ∀ y ∈ closure (e'.support W), e.normal f y = e.offset c := by
    have hsub : closure (e'.support W) ⊆ W e'.1.property.choose :=
      closure_minimal (e'.support_subset W e'.1.property.choose_spec) (hclosed _)
    have hspan := affineSpan_eq_of_notMem_singularSupport hregular
      (e.support_subset W e.1.property.choose_spec hinc) (hsub hx)
    have heq := AffineMap.eqOn_affineSpan
      (f := (f e.1.property.choose).toLinearMap.toAffineMap)
      (g := AffineMap.const ℝ V (c e.1.property.choose)) (hc e.1.property.choose)
    intro y hy
    rw [WallEvent.normal_def, WallEvent.offset_def]
    exact heq (hspan ▸ subset_affineSpan ℝ _ (hsub hy))
  have hh := hη e p q hqp ht hnormal htrans hsign hinc hplane
    (fun _ => hregular)
    (fun e' u hu hu0 hy => hW e'.1.property.choose u hu hu0
      (e'.support_subset W e'.1.property.choose_spec hy))
    (fun _ u hu hu0 => hS u hu.le hu0)
  refine ⟨hh.1, fun l hl => ?_⟩
  -- Expose the word to identify the dependent selection matchers.
  convert hh.2 l hl using 1
  apply Finset.sum_congr rfl
  rintro ⟨word, r, hm, hmono⟩ _
  cases word <;> rfl

end WallEvents

end Mei.CutoffDecoratedRay
