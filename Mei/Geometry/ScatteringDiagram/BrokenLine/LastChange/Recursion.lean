/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.FinalEncounter

/-!
# The last-change recursion for weighted ray sums

Let the backward line `Q + s • v q` in the direction of a final degree `q ≠ 0` meet
finitely many regular transverse encounters, listed by `E` at ray parameters `s e`, and
suppose that the wall supports meet the line only at them. Suppose also that the
propagation maps fix the degree-`q` component. Then the degree-`q` component of the
full weighted cutoff evaluation at `Q` is the sum, over the encounters `e` and the
adjacent degrees `p ≠ q` preserving the normal velocity at `e`, of the degree-`q`
component of `T e` applied to the degree-`p` evaluation at an incoming germ
`Q + s e • v q + η e • v p`. The germs can be taken arbitrarily close to the
encounters, and every adjacent degree is strictly lower than `q`.

Thus the evaluation at the endpoint is expressed through evaluations of strictly lower
degree at incoming germs, with the unchanged degrees removed. All encounter words,
whole decorations, and the incoming tails and sources of the older rays are retained.
This is the
decomposition of the weighted evaluation at the last change of degree in the
backward-ray recursion of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology

namespace Mei.CutoffDecoratedRay

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : I → Set V} {S : K → Set V} {C : Set V} {k : ℕ} {Q : V}

open Classical in
/-- The degree-`q` component of the weighted evaluation at `Q` is the sum over the
encounters `e` of the backward line and the lower adjacent degrees `p` of the
degree-`q` component of `T e` applied to the degree-`p` evaluation at incoming germs.
Here `E` lists all the encounters of the line, at ray parameters `s`, and the wall supports
meet the line only at them. The germs `Q + s e • v q + η e • v p` can be taken with
incoming parameters `η e` below any prescribed bound `θ`. -/
theorem exists_decompose_cutoffDecoratedEvaluation_eq_sum_lastChange
    [Finite J] [Finite K] [Finite I] {q : Γ} (hq : q ∈ d.cutoff k) (hq0 : q ≠ 0)
    (E : Finset J) (hT : ∀ e ∈ E, ∀ x ∈ ℳ q, (DirectSum.decompose ℳ (T e x) q : M) = x)
    (hP : ∀ j, P j ⊆ ⋃ b, W b) (hclosedW : ∀ j, IsClosed (W j))
    (hclosedS : ∀ j, IsClosed (S j)) (s : J → ℝ) (hinj : Set.InjOn s E)
    (hE : ∀ e ∈ E, 0 < s e ∧ f e (v q) ≠ 0 ∧ SignType.sign (f e (v q)) = ε e ∧
      f e (Q + s e • v q) = c e ∧ Q + s e • v q ∈ P e)
    (hhit : ∀ e (u : ℝ), 0 < u → f e (v q) ≠ 0 → SignType.sign (f e (v q)) = ε e →
      f e (Q + u • v q) = c e → Q + u • v q ∈ P e → e ∈ E ∧ s e = u)
    (hplane : ∀ e ∈ E, ∀ j, Q + s e • v q ∈ W j → ∀ y ∈ W j, f e y = c e)
    (hWray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∈ W j → ∃ e ∈ E, s e = u)
    (hSray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∉ S j) :
    ∀ θ > 0, ∃ η : J → ℝ, (∀ e ∈ E, 0 < η e ∧ η e < θ) ∧
      (DirectSum.decompose ℳ
        (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) q : M) =
        ∑ e ∈ E, ∑ p ∈ (d.finite_cutoff k).toFinset with
            p ≠ q ∧ q - p ∈ d.monoid ∧ f e (v q) = f e (v p),
          (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
            (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
              (Q + s e • v q + η e • v p)) p)) q : M) := by
  classical
  intro θ hθ
  -- The contribution of an encounter `e` with incoming displacement `η`.
  let Xs : J → ℝ → M := fun e η => ∑ p ∈ (d.finite_cutoff k).toFinset with
      p ≠ q ∧ q - p ∈ d.monoid ∧ f e (v q) = f e (v p),
    (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
      (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
        (Q + s e • v q + η • v p)) p)) q : M)
  -- `key` runs over the encounters ahead of the base point `Q + δ • v q`.
  have key : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → (∀ j, Q + δ • v q ∉ W j) →
      (E.filter fun e => δ < s e).card = n → ∃ η : J → ℝ,
        (∀ e ∈ E.filter fun e => δ < s e, 0 < η e ∧ η e < θ) ∧
        (DirectSum.decompose ℳ
          (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k (Q + δ • v q)) q : M) =
          ∑ e ∈ E.filter fun e => δ < s e, Xs e (η e) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro δ hδ hδW hn
      by_cases hne : (E.filter fun e => δ < s e).Nonempty
      · obtain ⟨e₀, he₀A, hmin⟩ := Finset.exists_min_image _ s hne
        obtain ⟨he₀E, hδe₀⟩ := Finset.mem_filter.mp he₀A
        obtain ⟨hs0, htr, hsg, hhe, hme⟩ := hE e₀ he₀E
        have hpt : Q + δ • v q + (s e₀ - δ) • v q = Q + s e₀ • v q := by module
        have hev := eventually_decompose_cutoffDecoratedEvaluation_eq_sum_finalEncounter
          (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S)
          (C := C) (Q := Q + δ • v q) e₀ q (s e₀ - δ) hq hq0 hP (by linarith) htr hsg
          (by rw [hpt]; exact hhe) (by rw [hpt]; exact hme)
          (fun e htr hsg hh hm => by
            rw [hpt] at hh hm
            exact hinj (hhit e _ hs0 htr hsg hh hm).1 he₀E (hhit e _ hs0 htr hsg hh hm).2)
          hclosedW (fun j hj => by rw [hpt] at hj; exact hplane e₀ he₀E j hj) hclosedS
          (fun j hj => by rw [hpt] at hj; exact hSray j _ hs0.le hj)
          (fun j u hu hu' hj => by
            have hpt' : Q + δ • v q - u • v q = Q + (δ - u) • v q := by module
            rw [hpt'] at hj
            obtain ⟨e, heE, hes⟩ := hWray j (δ - u) (by linarith) hj
            rcases hu'.eq_or_lt with rfl | hu0
            · exact hδW j (by simpa using hj)
            · exact absurd (hmin e (Finset.mem_filter.mpr ⟨heE, by linarith⟩))
                (by linarith))
          (fun j u hu hu' hj => by
            have hpt' : Q + δ • v q - u • v q = Q + (δ - u) • v q := by module
            rw [hpt'] at hj
            exact hSray j (δ - u) (by linarith) hj)
        -- Take the incoming displacement small enough to stay before the other encounters.
        have hgap : ∀ᶠ η : ℝ in 𝓝[>] 0,
            ∀ e ∈ (E.filter fun e => δ < s e).erase e₀, η < s e - s e₀ := by
          refine (Filter.eventually_all_finset _).mpr fun e he => ?_
          obtain ⟨hne₀, heA⟩ := Finset.mem_erase.mp he
          have hlt : s e₀ < s e := (hmin e heA).lt_of_ne fun h =>
            hne₀ (hinj (Finset.mem_filter.mp heA).1 he₀E h.symm)
          exact (eventually_lt_nhds (sub_pos.mpr hlt)).filter_mono nhdsWithin_le_nhds
        obtain ⟨η₀, ⟨⟨hη₀ev, hη₀gap⟩, hη₀pos⟩, hη₀θ⟩ :=
          (((hev.and hgap).and (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0))).and
            ((eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds)).exists
        have hη₀pos : 0 < η₀ := hη₀pos
        have hAδ' : (E.filter fun e => s e₀ + η₀ < s e) =
            (E.filter fun e => δ < s e).erase e₀ := by
          ext e
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨heE, hlt⟩
            exact ⟨fun h => by subst h; linarith, heE, by linarith⟩
          · rintro ⟨hne₀, heE, heδ⟩
            have := hη₀gap e (Finset.mem_erase.mpr ⟨hne₀, Finset.mem_filter.mpr ⟨heE, heδ⟩⟩)
            exact ⟨heE, by linarith⟩
        have hδ'W : ∀ j, Q + (s e₀ + η₀) • v q ∉ W j := by
          intro j hj
          obtain ⟨e, heE, hes⟩ := hWray j _ (by linarith) hj
          by_cases hee : e = e₀
          · subst hee
            linarith
          · by_cases hδe : δ < s e
            · have := hη₀gap e (Finset.mem_erase.mpr ⟨hee, Finset.mem_filter.mpr ⟨heE, hδe⟩⟩)
              linarith
            · linarith
        have hcard : (E.filter fun e => s e₀ + η₀ < s e).card < n := by
          rw [hAδ', ← hn]
          exact Finset.card_erase_lt_of_mem he₀A
        obtain ⟨η', hη'bd, hη'eq⟩ := ih _ hcard (s e₀ + η₀) (by linarith) hδ'W rfl
        refine ⟨Function.update η' e₀ η₀, fun e he => ?_, ?_⟩
        · by_cases hee : e = e₀
          · subst hee
            simp [hη₀pos, hη₀θ]
          · rw [Function.update_of_ne hee]
            exact hη'bd e (hAδ' ▸ Finset.mem_erase.mpr ⟨hee, he⟩)
        · have hqmem : q ∈ (d.finite_cutoff k).toFinset.filter
              (fun p => q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p)) :=
            Finset.mem_filter.mpr ⟨(d.finite_cutoff k).mem_toFinset.mpr hq,
              by simpa only [sub_self] using d.monoid.zero_mem, rfl⟩
          have herase : ((d.finite_cutoff k).toFinset.filter
              (fun p => q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p))).erase q =
              (d.finite_cutoff k).toFinset.filter
                (fun p => p ≠ q ∧ q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p)) := by
            ext p
            simp only [Finset.mem_erase, Finset.mem_filter]
            tauto
          have hqterm : (DirectSum.decompose ℳ (T e₀ (DirectSum.decompose ℳ
              (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
                (Q + δ • v q + (s e₀ - δ) • v q + η₀ • v q)) q)) q : M) =
              DirectSum.decompose ℳ (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
                (Q + (s e₀ + η₀) • v q)) q := by
            have hpt₂ : Q + δ • v q + (s e₀ - δ) • v q + η₀ • v q =
                Q + (s e₀ + η₀) • v q := by module
            rw [hT e₀ he₀E _ (Submodule.coe_mem _), hpt₂]
          rw [hη₀ev, ← Finset.add_sum_erase _ _ hqmem, hqterm, herase, add_comm,
            ← Finset.add_sum_erase _ _ he₀A, Function.update_self]
          have hrest : ∑ e ∈ (E.filter fun e => δ < s e).erase e₀,
              Xs e (Function.update η' e₀ η₀ e) =
              (DirectSum.decompose ℳ (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k
                (Q + (s e₀ + η₀) • v q)) q : M) := by
            rw [hη'eq, hAδ']
            exact Finset.sum_congr rfl fun e he => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase he)]
          rw [hrest]
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hpt]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨fun _ => 1, by simp [hne], ?_⟩
        rw [hne, Finset.sum_empty]
        refine decompose_cutoffDecoratedEvaluation_eq_zero_of_forall_not_encounter q hq0 ?_
        intro e u hu htr hsg hh hm
        have hpt : Q + δ • v q + u • v q = Q + (δ + u) • v q := by module
        rw [hpt] at hh hm
        obtain ⟨heE, hes⟩ := hhit e (δ + u) (by linarith) htr hsg hh hm
        have : e ∈ E.filter fun e => δ < s e := Finset.mem_filter.mpr ⟨heE, by linarith⟩
        simp [hne] at this
  have hW₀ : ∀ j, Q + (0 : ℝ) • v q ∉ W j := fun j hj => by
    obtain ⟨e, heE, hes⟩ := hWray j 0 le_rfl (by simpa only [zero_smul, add_zero] using hj)
    linarith [(hE e heE).1]
  obtain ⟨η, hη, heq⟩ := key _ 0 le_rfl hW₀ rfl
  rw [Finset.filter_true_of_mem fun e he => (hE e he).1] at hη heq
  simp only [zero_smul, add_zero] at heq
  exact ⟨η, hη, heq⟩

end Mei.CutoffDecoratedRay
