/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Extend

/-!
# Weighted attachment of a final encounter

Fix a short incoming segment, a transverse encounter, and an outgoing segment.
Attaching these segments embeds the actual incoming decorated rays whose selected
output component survives into the full decorated-ray fiber. Its image consists
exactly of the rays with the prescribed last two degrees whose earlier history
admits the incoming endpoint. The image criterion retains the complete source,
wall and singular avoidance conditions; it does not assume that every outgoing
ray can be cut at a fixed incoming endpoint.

The finite sum over this image is the sum of the selected whole components of
the incoming decorations. This preserves multiplicities and cancellation, and
is the fiberwise attachment step in the backward-ray recursion of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).

We use `DecoratedAdmissibleRay.extend`, uniqueness of fixed-history admissible
realizations, and Mathlib's `Fintype.sum_of_injective`.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V}
  (U : Module.End R M) (p q : Γ) (Y : V) (s t : ℝ)
  (hs : 0 ≤ s) (ht : 0 < t) (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)

local notation "D" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Y
local notation "E" => DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a v
  (Fin.cons m f) (Fin.cons b c) (Fin.cons (SignType.sign (m (v q))) ε)
  (Fin.cons H P) W S C (Y - s • v p - t • v q)
local notation "A" => {r : D //
  Fin.snoc (α := fun _ => Γ) (Subtype.val (Sigma.fst r)) p₀ 0 = p ∧
    DirectSum.decompose ℳ (U (decoration r 0)) q ≠ 0}

variable (hnormal : m (v q) = m (v p)) (htrans : m (v q) ≠ 0)
  (hheight : m (Y - s • v p) = b) (hinc : (Y - s • v p) ∈ H)
  (hW₁ : ∀ j u, 0 < u → u < s → Y - u • v p ∉ W j)
  (hW₂ : ∀ j u, -t < u → u ≤ 0 → (Y - s • v p - t • v q) - u • v q ∉ W j)
  (hS₁ : ∀ j u, 0 < u → u ≤ s → Y - u • v p ∉ S j)
  (hS₂ : ∀ j u, -t < u → u ≤ 0 → (Y - s • v p - t • v q) - u • v q ∉ S j)

private theorem incoming_direction (r : A) : r.val.2.ray.direction = v p := by
  have he := r.val.2.directionAt_eq 0
  rw [r.val.2.parameter_zero, FiniteAffineRay.directionAt_of_nonneg _ le_rfl,
    r.property.1] at he
  exact he

private theorem incoming_continuation (r : A) {u : ℝ} (hu : 0 ≤ u) :
    r.val.2.ray u = Y - u • v p := by
  rw [FiniteAffineRay.eval_of_nonneg _ hu, incoming_direction U p q Y r,
    r.val.2.endpoint_eq]
  simp only [neg_smul, vadd_eq_add, sub_eq_add_neg, add_comm]

private theorem attached_endpoint (r : A) :
    (r.val.2.ray.extend s t (v q) hs ht).endpoint = (Y - s • v p - t • v q) := by
  rw [FiniteAffineRay.endpoint_extend, incoming_direction U p q Y r, r.val.2.endpoint_eq]
  simp only [vadd_eq_add, neg_smul]
  abel

private def attach (r : A) : E := by
  have hc (u : ℝ) (hu : 0 ≤ u) := incoming_continuation U p q Y r hu
  have he := attached_endpoint U p q Y s t hs ht r
  let z := r.val.extend U q s t hs ht m b H r.property.2
    (by rw [r.property.1]; exact hnormal) htrans
    (by rw [hc s hs]; exact hheight) (by rw [hc s hs]; exact hinc)
    (fun j u hu hus => by rw [hc u hu.le]; exact hW₁ j u hu hus)
    (fun j u hu hu₀ => by simpa only [he, neg_smul, vadd_eq_add,
      sub_eq_add_neg, add_comm] using hW₂ j u hu hu₀)
    (fun j u hu hus => by rw [hc u hu.le]; exact hS₁ j u hu hus)
    (fun j u hu hu₀ => by simpa only [he, neg_smul, vadd_eq_add,
      sub_eq_add_neg, add_comm] using hS₂ j u hu hu₀)
  exact ⟨z.1, { z.2 with
    endpoint_eq := z.2.endpoint_eq.trans he
    off_walls := by simpa only [he] using z.2.off_walls }⟩

private theorem history_attach (r : A) :
    (attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r).1.val =
      Fin.cons (α := fun _ => Γ) q r.val.1.val := by
  simp only [attach, history_extend]

private theorem ray_attach (r : A) :
    (attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r).2.ray =
      r.val.2.ray.extend s t (v q) hs ht := by
  simp only [attach, ray_extend]

private theorem parameter_attach (r : A) :
    (attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r).2.parameter =
      Fin.cons (α := fun _ => ℝ) 0
        (Fin.cons (α := fun _ => ℝ) (-t)
          (fun j => r.val.2.parameter j.succ - (s + t))) := by
  simp only [attach, parameter_extend]

/-- Attaching fixed admissible segments is injective on the actual incoming
rays with prescribed final degree and surviving selected output component.
Different incoming histories remain distinct even if their weights coincide. -/
def finalEncounterEmbedding : A ↪ E where
  toFun := attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂
  inj' := by
    intro r r' he
    apply Subtype.ext
    apply Sigma.fst_injective
    apply Subtype.ext
    have hh := congrArg (fun z : E => z.1.val) he
    rw [history_attach, history_attach] at hh
    exact funext fun j => by simpa only [Fin.cons_succ] using congrFun hh j.succ

/-- The new history prepends the chosen output degree to the entire incoming
history. This also characterizes the inverse on the embedding's range. -/
@[simp]
theorem history_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).1.val = Fin.cons (α := fun _ => Γ) q r.val.1.val := by
  exact history_attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r

/-- The attached final weight is the whole selected component of the incoming
weight, with no splitting of coefficients into individual monomials. -/
@[simp↓]
theorem decoration_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).decoration 0 =
        (DirectSum.decompose ℳ (U (r.val.decoration 0)) q : M) := by
  simp only [decoration_zero, history_finalEncounterEmbedding,
    homogeneousHistory_succ_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

/-- Attachment retains the complete incoming path by the canonical finite-ray
extension, including all old bend increments and the incoming tail. -/
@[simp]
theorem ray_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).2.ray = r.val.2.ray.extend s t (v q) hs ht := by
  exact ray_attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r

/-- The new encounter occurs at `-t`; all earlier encounter times are
translated by `s + t`, preserving their order. -/
@[simp]
theorem parameter_finalEncounterEmbedding (r : A) :
    (finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans hheight hinc
      hW₁ hW₂ hS₁ hS₂ r).2.parameter =
        Fin.cons (α := fun _ => ℝ) 0
          (Fin.cons (α := fun _ => ℝ) (-t)
            (fun j => r.val.2.parameter j.succ - (s + t))) := by
  exact parameter_attach U p q Y s t hs ht m b H hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂ r

/-- An outgoing ray is obtained by attachment exactly when its last two
recorded degrees are `q` and `p` and its complete earlier history admits `Y`.
The latter tests all walls, singular sets and the original incoming source. -/
@[simp↓] -- Recognize the image before generic range and subtype expansion.
theorem mem_range_finalEncounterEmbedding (z : E) :
    z ∈ Set.range (finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans
      hheight hinc hW₁ hW₂ hS₁ hS₂) ↔
      z.1.val 0 = q ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p ∧
        Y ∈ admissibleBackwardDomain f c
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val i.succ) p₀ j)) P W S C := by
  constructor
  · rintro ⟨r, rfl⟩
    simp only [history_finalEncounterEmbedding, Fin.cons_zero, Fin.cons_succ]
    exact ⟨trivial, r.property.1, r.val.2.mem_admissibleBackwardDomain⟩
  · rintro ⟨hq, hp, hY⟩
    let pp : Fin n → Γ := fun j => z.1.val j.succ
    have hsnoc (j : Fin (n + 1)) :
        Fin.snoc (α := fun _ => Γ) z.1.val p₀ j.succ =
          Fin.snoc (α := fun _ => Γ) pp p₀ j := by
      rw [← Fin.cons_self_tail z.1.val, ← Fin.cons_snoc_eq_snoc_cons]
      rfl
    have hz := (mem_decoratedHistorySupport ..).mp z.1.property
    have hpp : pp ∈ decoratedHistorySupport ℳ T p₀ a v f ε := by
      apply (mem_decoratedHistorySupport ..).mpr
      refine ⟨?_, fun j => ?_⟩
      · simpa only [Fin.cons_succ] using homogeneousHistory_tail_ne_zero ℳ _ _ hz.1
      · have hn := z.normal_velocity_eq j.succ
        have he := z.crossing_sign j.succ
        rw [hsnoc j.succ] at hn
        exact ⟨hn, he⟩
    let r : D := ⟨⟨pp, hpp⟩, admissibleRayRealization _ _ _ _ _ _ _ _ hY⟩
    have hc : DirectSum.decompose ℳ (U (r.decoration 0)) q ≠ 0 := by
      have hne := hz.1
      rw [homogeneousHistory_succ_apply, Fin.cons_zero, hq] at hne
      rw [decoration_zero]
      exact Submodule.coe_eq_zero.not.mp hne
    refine ⟨⟨r, hp, hc⟩, ?_⟩
    apply Sigma.fst_injective
    apply Subtype.ext
    rw [history_finalEncounterEmbedding]
    exact funext fun j => Fin.cases hq.symm (fun _ => rfl) j

include hs ht hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂

open Classical in
/-- Sum the actual outgoing fiber over the exact attachment image. It equals
propagation of the whole incoming weights with the chosen output component.
Neither coincident weights nor cancellation identify different rays. -/
theorem sum_ite_decoration_finalEncounterEmbedding :
    (let := Fintype.ofFinite E
     ∑ z : E,
      if z.1.val 0 = q ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p ∧
        Y ∈ admissibleBackwardDomain f c
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val i.succ) p₀ j)) P W S C
      then z.decoration 0 else 0) =
    (let := Fintype.ofFinite A
     ∑ r : A, (DirectSum.decompose ℳ (U (r.val.decoration 0)) q : M)) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite A
  let e : A ↪ E := finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans
    hheight hinc hW₁ hW₂ hS₁ hS₂
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro z hz
    rw [ite_eq_right]
    exact fun h => hz ((mem_range_finalEncounterEmbedding ..).mpr h)
  · intro r
    rw [ite_eq_left ((mem_range_finalEncounterEmbedding ..).mp ⟨r, rfl⟩)]
    exact (decoration_finalEncounterEmbedding ..).symm

open Classical in
/-- The weighted attachment image is the selected component of `U` applied
to the entire incoming fiber of degree `p`. Killed components are included as
zero summands, so the formula is suitable for a linear backward recursion. -/
theorem sum_ite_decoration_finalEncounter_eq_component_sum :
    (let := Fintype.ofFinite E
     ∑ z : E,
      if z.1.val 0 = q ∧
        Fin.snoc (α := fun _ => Γ) (fun j : Fin n => z.1.val j.succ) p₀ 0 = p ∧
        Y ∈ admissibleBackwardDomain f c
          (fun j => v (Fin.snoc (α := fun _ => Γ)
            (fun i : Fin n => z.1.val i.succ) p₀ j)) P W S C
      then z.decoration 0 else 0) =
      (DirectSum.decompose ℳ (U (let := Fintype.ofFinite D
        ∑ r : D, if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = p
          then r.decoration 0 else 0)) q : M) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite D
  let := Fintype.ofFinite A
  rw [sum_ite_decoration_finalEncounterEmbedding U p q Y s t hs ht m b H hnormal htrans
    hheight hinc hW₁ hW₂ hS₁ hS₂]
  trans ∑ r : D, if Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = p
    then (DirectSum.decompose ℳ (U (r.decoration 0)) q : M) else 0
  · apply Fintype.sum_of_injective (Subtype.val : A → D) Subtype.val_injective
    · intro r hr
      by_cases hp : Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0 = p
      · rw [ite_eq_left hp]
        have hc : DirectSum.decompose ℳ (U (r.decoration 0)) q = 0 := by
          by_contra hc
          exact hr ⟨⟨r, hp, hc⟩, rfl⟩
        rw [hc, Submodule.coe_zero]
      · exact ite_eq_right hp
    · intro r
      exact (ite_eq_left r.property.1).symm
  · simp only [map_sum, DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp

end Mei.DecoratedAdmissibleRay
