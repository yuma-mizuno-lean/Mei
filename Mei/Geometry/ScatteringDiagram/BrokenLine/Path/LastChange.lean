/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.FinalEncounter
public import Mei.Geometry.Convex.Sweep.Generic

/-!
# The last-change recursion for path ray sums

Let the backward line `Q + u • v q` in the direction of a final degree `q ≠ 0` meet
finitely many regular transverse encounters, listed by `E` at ray parameters `s e`, and
suppose that the wall supports meet the line only at them. Suppose also that the
propagation maps fix the degree-`q` component. Then the degree-`q` component of the
weighted evaluation of decorated rays along the paths of the one-object quiver at `Q` is
the sum, over the encounters `e` and the adjacent degrees `p ≠ q` preserving the normal
velocity at `e`, of the degree-`q` component of `T e` applied to the degree-`p`
evaluation at an incoming germ `Q + s e • v q + η e • v p`. The germs can be taken
arbitrarily close to the encounters, also subject to any eventual condition at each
event. Every adjacent degree is strictly lower than `q`.

The inventory exhausts every endpoint fiber, and the finite degree set `D` contains the
degree of every nonzero homogeneous coefficient. The decomposition iterates
`eventually_decompose_pathDecoratedEvaluation_eq_sum_finalEncounter` along the line,
removing the unchanged degrees with the diagonal hypothesis. This is the decomposition at
the last change of degree in the backward-ray recursion of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open TauCeti (ExceptionalArrangement)

open TauCeti (PositiveDegrees)

open Set Filter Topology Quiver

namespace Mei

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : I → Set V} {S : K → Set V} {C : Set V} {Q : V}

local notation "PRay" => PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C
local notation "Paths" => Path (SingleObj.star J) (SingleObj.star J)
local notation "evaluation" => fun (s : Finset Paths) (X : V) =>
  pathDecoratedEvaluation (Q := SingleObj J)
    (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a s (fun _ => v)
    (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C X

open Classical in
/-- The degree-`q` component of the weighted evaluation at `Q` is the sum over the
encounters `e` of the backward line and the lower adjacent degrees `p` of the
degree-`q` component of `T e` applied to the degree-`p` evaluation at incoming germs.
Here `E` lists all the encounters of the line, at ray parameters `s`, and the wall supports
meet the line only at them. The germs `Q + s e • v q + η e • v p` can be taken with
incoming parameters `η e` below any prescribed bound `θ`, while also satisfying
any prescribed eventual condition `admit e`. -/
theorem exists_decompose_pathDecoratedEvaluation_eq_sum_lastChange_of_eventually
    [Finite K] [Finite I] (σ : Finset Paths) (hσ : ∀ X p, PRay p X → p ∈ σ)
    (D : Finset Γ) (hD : ∀ n (y : M), y ∈ ℳ n → y ≠ 0 → n ∈ D)
    (hshift : ∀ j n m (y : M), y ∈ ℳ n →
      (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)
    {q : Γ} (hq0 : q ≠ 0)
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
    ∀ (admit : J → ℝ → Prop), (∀ e ∈ E, ∀ᶠ η : ℝ in 𝓝[>] 0, admit e η) →
    ∀ θ > 0, ∃ η : J → ℝ, (∀ e ∈ E, 0 < η e ∧ η e < θ ∧ admit e (η e)) ∧
      (DirectSum.decompose ℳ (evaluation σ Q) q : M) =
        ∑ e ∈ E, ∑ p ∈ D with p ≠ q ∧ q - p ∈ d.monoid ∧ f e (v q) = f e (v p),
          (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
            (evaluation σ (Q + s e • v q + η e • v p)) p)) q : M) := by
  classical
  intro admit hadmit θ hθ
  -- The contribution of an encounter `e` with incoming displacement `η`.
  let Xs : J → ℝ → M := fun e η => ∑ p ∈ D with p ≠ q ∧ q - p ∈ d.monoid ∧
      f e (v q) = f e (v p),
    (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
      (evaluation σ (Q + s e • v q + η • v p)) p)) q : M)
  -- `key` runs over the encounters ahead of the base point `Q + δ • v q`.
  have key : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → (∀ j, Q + δ • v q ∉ W j) →
      (E.filter fun e => δ < s e).card = n → ∃ η : J → ℝ,
        (∀ e ∈ E.filter fun e => δ < s e, 0 < η e ∧ η e < θ ∧ admit e (η e)) ∧
        (DirectSum.decompose ℳ (evaluation σ (Q + δ • v q)) q : M) =
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
        have hev := eventually_decompose_pathDecoratedEvaluation_eq_sum_finalEncounter
          (d := d) (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W)
          (S := S) (C := C) (t := s e₀ - δ) (Q + δ • v q) e₀ q σ hσ D hD hshift hq0 hP
          (by linarith) htr hsg
          (by rw [hpt]; exact hhe) (by rw [hpt]; exact hme)
          (fun e htr hsg hh hm => by
            rw [hpt] at hh hm
            exact hinj (hhit e _ hs0 htr hsg hh hm).1 he₀E (hhit e _ hs0 htr hsg hh hm).2)
          hclosedW (fun j hj => by rw [hpt] at hj; exact hplane e₀ he₀E j hj) hclosedS
          (fun j hj => by rw [hpt] at hj; exact hSray j _ hs0.le hj)
          (fun j u hu hu' hj => by
            have hpt' : Q + δ • v q + u • v q = Q + (δ + u) • v q := by module
            rw [hpt'] at hj
            obtain ⟨e, heE, hes⟩ := hWray j (δ + u) (by linarith) hj
            rcases hu.eq_or_lt with rfl | hu0
            · exact hδW j (by simpa using hj)
            · exact absurd (hmin e (Finset.mem_filter.mpr ⟨heE, by linarith⟩))
                (by linarith))
          (fun j u hu _ hj => by
            have hpt' : Q + δ • v q + u • v q = Q + (δ + u) • v q := by module
            rw [hpt'] at hj
            exact hSray j (δ + u) (by linarith) hj)
        -- Take the incoming displacement small enough to stay before the other encounters.
        have hgap : ∀ᶠ η : ℝ in 𝓝[>] 0,
            ∀ e ∈ (E.filter fun e => δ < s e).erase e₀, η < s e - s e₀ := by
          refine (Filter.eventually_all_finset _).mpr fun e he => ?_
          obtain ⟨hne₀, heA⟩ := Finset.mem_erase.mp he
          have hlt : s e₀ < s e := (hmin e heA).lt_of_ne fun h =>
            hne₀ (hinj (Finset.mem_filter.mp heA).1 he₀E h.symm)
          exact (eventually_lt_nhds (sub_pos.mpr hlt)).filter_mono nhdsWithin_le_nhds
        obtain ⟨η₀, ⟨⟨⟨hη₀ev, hη₀gap⟩, hη₀pos⟩, hη₀θ⟩, hη₀admit⟩ :=
          ((((hev.and hgap).and (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0))).and
            ((eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds)).and
              (hadmit e₀ he₀E)).exists
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
            simp [hη₀pos, hη₀θ, hη₀admit]
          · rw [Function.update_of_ne hee]
            exact hη'bd e (hAδ' ▸ Finset.mem_erase.mpr ⟨hee, he⟩)
        · have hD' : ∀ p ∈ D.filter (fun p => q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p)),
              p ≠ q → p ∈ D.filter
                (fun p => p ≠ q ∧ q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p)) := by
            intro p hp hpq
            obtain ⟨hpD, hp⟩ := Finset.mem_filter.mp hp
            exact Finset.mem_filter.mpr ⟨hpD, hpq, hp⟩
          -- The unchanged degree contributes the evaluation just past the encounter.
          have hqterm : (DirectSum.decompose ℳ (T e₀ (DirectSum.decompose ℳ
              (evaluation σ (Q + δ • v q + (s e₀ - δ) • v q + η₀ • v q)) q)) q : M) =
              DirectSum.decompose ℳ (evaluation σ (Q + (s e₀ + η₀) • v q)) q := by
            have hpt₂ : Q + δ • v q + (s e₀ - δ) • v q + η₀ • v q =
                Q + (s e₀ + η₀) • v q := by module
            rw [hT e₀ he₀E _ (Submodule.coe_mem _), hpt₂]
          have hsplitq : (∑ p ∈ D with q - p ∈ d.monoid ∧ f e₀ (v q) = f e₀ (v p),
              (DirectSum.decompose ℳ (T e₀ (DirectSum.decompose ℳ
                (evaluation σ (Q + δ • v q + (s e₀ - δ) • v q + η₀ • v p)) p)) q : M)) =
              (if q ∈ D then (DirectSum.decompose ℳ (evaluation σ
                (Q + (s e₀ + η₀) • v q)) q : M) else 0) + Xs e₀ η₀ := by
            dsimp only [Xs]
            rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_ite_eq' D q
              (fun _ => (DirectSum.decompose ℳ (evaluation σ
                (Q + (s e₀ + η₀) • v q)) q : M)), ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            by_cases hpq : p = q
            · subst hpq
              simp only [sub_self, d.monoid.zero_mem, true_and, ite_true, ne_eq,
                not_true_eq_false, false_and, ite_false, add_zero]
              rw [← hqterm]
            · simp only [hpq, ite_false, zero_add, ne_eq, not_false_eq_true, true_and]
              split_ifs <;> simp [hpt]
          have hqD : (if q ∈ D then (DirectSum.decompose ℳ (evaluation σ
              (Q + (s e₀ + η₀) • v q)) q : M) else 0) =
              DirectSum.decompose ℳ (evaluation σ (Q + (s e₀ + η₀) • v q)) q := by
            split_ifs with hq
            · rfl
            · by_contra hne
              exact hq (hD q _ (Submodule.coe_mem _) (Ne.symm hne))
          rw [hη₀ev, hsplitq, hqD, add_comm, ← Finset.add_sum_erase _ _ he₀A,
            Function.update_self]
          have hrest : ∑ e ∈ (E.filter fun e => δ < s e).erase e₀,
              Xs e (Function.update η' e₀ η₀ e) =
              (DirectSum.decompose ℳ (evaluation σ (Q + (s e₀ + η₀) • v q)) q : M) := by
            rw [hη'eq, hAδ']
            exact Finset.sum_congr rfl fun e he => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase he)]
          rw [hrest]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨fun _ => 1, by simp [hne], ?_⟩
        rw [hne, Finset.sum_empty]
        refine decompose_pathDecoratedEvaluation_eq_zero_of_forall_not_encounter
          (Q + δ • v q) q σ hq0 ?_
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

open Classical in
/-- The degree-`q` component of the weighted evaluation at `Q` is the sum over the
encounters `e` of the backward line and the lower adjacent degrees `p` of the
degree-`q` component of `T e` applied to the degree-`p` evaluation at incoming germs,
with incoming parameters below any prescribed bound `θ`. -/
theorem exists_decompose_pathDecoratedEvaluation_eq_sum_lastChange
    [Finite K] [Finite I] (σ : Finset Paths) (hσ : ∀ X p, PRay p X → p ∈ σ)
    (D : Finset Γ) (hD : ∀ n (y : M), y ∈ ℳ n → y ≠ 0 → n ∈ D)
    (hshift : ∀ j n m (y : M), y ∈ ℳ n →
      (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)
    {q : Γ} (hq0 : q ≠ 0)
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
      (DirectSum.decompose ℳ (evaluation σ Q) q : M) =
        ∑ e ∈ E, ∑ p ∈ D with p ≠ q ∧ q - p ∈ d.monoid ∧ f e (v q) = f e (v p),
          (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ
            (evaluation σ (Q + s e • v q + η e • v p)) p)) q : M) := by
  intro θ hθ
  obtain ⟨η, hη, heq⟩ :=
    exists_decompose_pathDecoratedEvaluation_eq_sum_lastChange_of_eventually
      σ hσ D hD hshift hq0 E hT hP hclosedW hclosedS s hinj hE hhit hplane hWray hSray
      (fun _ _ => True) (fun _ _ => Filter.Eventually.of_forall fun _ => trivial) θ hθ
  exact ⟨η, fun e he => ⟨(hη e he).1, (hη e he).2.1⟩, heq⟩

section Generic

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J] [Finite K] [Finite I]

open Classical in
/-- Refine outgoing endpoint exceptions so the full last-change recurrence reads
its lower-degree evaluations at generic straight incoming cuts. One displacement
at each encounter works for every compatible input degree of the finite degree set `D`,
including terms whose coefficient vanishes. The refinement is uniform in the output degree
and independent of the coefficient data, the inventory and the encounter list. -/
theorem exists_decompose_pathDecoratedEvaluation_eq_sum_lastChange_generic
    (d : PositiveDegrees Γ) (D : Finset Γ) (A : ExceptionalArrangement ℝ V)
    (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) :
    ∃ F : ExceptionalArrangement ℝ V, ∀ Q, F.IsGeneric Q →
      ∀ (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
        (T : J → Module.End R M) (a : ℳ 0) (ε : J → SignType)
        (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)
        (σ : Finset (Path (SingleObj.star J) (SingleObj.star J)))
        (_hσ : ∀ X p, PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
          (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
          (fun e => ε e) (fun e => c e) (fun e => P e) W S C p X → p ∈ σ)
        (_hD : ∀ n (y : M), y ∈ ℳ n → y ≠ 0 → n ∈ D)
        (_hshift : ∀ j n m (y : M), y ∈ ℳ n →
          (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)
        (q : Γ) (_hq : q ∈ D) (_hq0 : q ≠ 0)
        (E : Finset J)
        (_hT : ∀ e ∈ E, ∀ x ∈ ℳ q, (DirectSum.decompose ℳ (T e x) q : M) = x)
        (_hP : ∀ j, P j ⊆ ⋃ b, W b) (_hclosedW : ∀ j, IsClosed (W j))
        (_hclosedS : ∀ j, IsClosed (S j)) (s : J → ℝ) (_hinj : Set.InjOn s E)
        (_hE : ∀ e ∈ E, 0 < s e ∧ f e (v q) ≠ 0 ∧ SignType.sign (f e (v q)) = ε e ∧
          f e (Q + s e • v q) = c e ∧ Q + s e • v q ∈ P e)
        (_hhit : ∀ e (u : ℝ), 0 < u → f e (v q) ≠ 0 →
          SignType.sign (f e (v q)) = ε e → f e (Q + u • v q) = c e →
          Q + u • v q ∈ P e → e ∈ E ∧ s e = u)
        (_hplane : ∀ e ∈ E, ∀ j, Q + s e • v q ∈ W j → ∀ y ∈ W j, f e y = c e)
        (_hWray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∈ W j → ∃ e ∈ E, s e = u)
        (_hSray : ∀ j (u : ℝ), 0 ≤ u → Q + u • v q ∉ S j),
      ∀ θ > 0, ∃ η : J → ℝ,
        (∀ e ∈ E, 0 < η e ∧ η e < θ ∧
          ∀ r ∈ D, f e (v q) = f e (v r) →
            A.IsGeneric (Q + s e • v q + η e • v r)) ∧
        (DirectSum.decompose ℳ (pathDecoratedEvaluation (Q := SingleObj J)
          (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a σ (fun _ => v)
          (fun e => f e) (fun e => ε e) (fun e => c e) (fun e => P e) W S C Q) q : M) =
          ∑ e ∈ E, ∑ r ∈ D with r ≠ q ∧ q - r ∈ d.monoid ∧ f e (v q) = f e (v r),
            (DirectSum.decompose ℳ (T e (DirectSum.decompose ℳ (pathDecoratedEvaluation
              (Q := SingleObj J) (M := fun _ => M) (ι := fun _ => Γ) (fun e => T e)
              (fun _ => ℳ) 0 a σ (fun _ => v) (fun e => f e) (fun e => ε e) (fun e => c e)
              (fun e => P e) W S C (Q + s e • v q + η e • v r)) r)) q : M) := by
  classical
  let Z := {z : J × D × D // f z.1 (v z.2.2.val) ≠ 0}
  obtain ⟨F, hF⟩ := Convex.exists_forall_eventually_isGeneric_sweepProjection A
    (fun z : Z => f z.val.1) (fun z => c z.val.1)
    (fun z => (f z.val.1 (v z.val.2.1.val))⁻¹ • v z.val.2.1.val)
    (fun z => v z.val.2.2.val) (fun z => z.property)
  refine ⟨F, fun Q hQ ℳ _ T a ε P W S C σ hσ hD hshift q hq hq0 E hT hP hclosedW hclosedS s
    hinj hE hhit hplane hWray hSray θ hθ => ?_⟩
  apply exists_decompose_pathDecoratedEvaluation_eq_sum_lastChange_of_eventually (d := d)
    (Q := Q) (T := T) (a := a) (v := v) (f := f) (c := c) (ε := ε) (P := P) (W := W)
    (S := S) (C := C) σ hσ D hD hshift hq0 E hT hP hclosedW hclosedS s hinj hE hhit hplane
    hWray hSray (fun e η => ∀ r ∈ D, f e (v q) = f e (v r) →
      A.IsGeneric (Q + s e • v q + η • v r)) ?_ θ hθ
  intro e he
  -- The geometric refinement simultaneously controls every transverse incoming
  -- degree, so no finiteness of coefficient supports is needed here.
  filter_upwards [hF Q hQ] with η hη r hr hnormal
  have htrans : f e (v r) ≠ 0 := hnormal ▸ (hE e he).2.1
  let z : Z := ⟨(e, ⟨q, hq⟩, ⟨r, hr⟩), htrans⟩
  have hheight := (hE e he).2.2.2.1
  simpa only [z,
    ContinuousLinearMap.sweepProjection_inv_smul_eq_add_smul _ (hE e he).2.1 hheight]
    using hη z

end Generic

end Mei
