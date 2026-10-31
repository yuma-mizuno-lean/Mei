/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic

/-!
# Erasing a propagation step that fixes its decoration

A homogeneous propagation history retains its final weight when a step with
equal incoming and outgoing decorations is omitted. The two shorter tuples are
obtained by `Fin.removeNth`, so all other maps and selected degrees retain their
order. No homogeneity or nonvanishing assumption on the incoming decoration is
needed. This is an algebraic contraction of the coefficient history, independent
of any geometric realization of its encounters.

When every map fixes the same-degree component of each homogeneous input, an
encounter with equal adjacent degrees fixes its decoration, and a history of
constant degree fixes its input.

We use `homogeneousHistoryStage` and its component-propagation equations.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- Omitting a step whose whole decoration is unchanged preserves the final
weight of a homogeneous history. No other map or selected degree is changed. -/
theorem homogeneousHistory_removeNth {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (r : Fin (n + 1) → ι) (a : M)
    (j : Fin (n + 1))
    (hfix : homogeneousHistoryStage ℳ T r j.castSucc a =
      homogeneousHistoryStage ℳ T r j.succ a) :
    homogeneousHistory ℳ T r a =
      homogeneousHistory ℳ (j.removeNth T) (j.removeNth r) a := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
      homogeneousHistoryStage_succ, homogeneousHistoryStage_last,
      homogeneousHistory_zero, LinearMap.id_apply] using hfix
  | succ n ih =>
    revert hfix
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hfix
      simpa only [Fin.castSucc_zero, homogeneousHistoryStage_zero,
        homogeneousHistoryStage_succ, homogeneousHistoryStage_zero,
        Fin.removeNth_zero, Fin.tail_def] using hfix
    · intro hfix
      have htail : homogeneousHistoryStage ℳ (fun i => T i.succ)
          (fun i => r i.succ) j.castSucc a =
        homogeneousHistoryStage ℳ (fun i => T i.succ)
          (fun i => r i.succ) j.succ a := by
        simpa only [← Fin.succ_castSucc, homogeneousHistoryStage_succ] using hfix
      conv_lhs => rw [homogeneousHistory_succ_apply]
      conv_rhs => rw [homogeneousHistory_succ_apply]
      rw [ih (fun i => T i.succ) (fun i => r i.succ) j htail]
      have hT : j.removeNth (fun i => T i.succ) = fun i => j.succ.removeNth T i.succ := by
        funext i
        simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
      have hr : j.removeNth (fun i => r i.succ) = fun i => j.succ.removeNth r i.succ := by
        funext i
        simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
      rw [hT, hr, Fin.removeNth_apply, Fin.removeNth_apply, Fin.succ_succAbove_zero]

/-- Omitting a step whose whole decoration is unchanged preserves every retained
segment decoration, with indices transported past the deleted output segment. -/
@[simp]
theorem homogeneousHistoryStage_removeNth {n : ℕ}
    (T : Fin (n + 1) → Module.End R M) (r : Fin (n + 1) → ι) (a : M)
    (i : Fin (n + 1))
    (hfix : homogeneousHistoryStage ℳ T r i.castSucc a =
      homogeneousHistoryStage ℳ T r i.succ a) (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ (i.removeNth T) (i.removeNth r) j a =
      homogeneousHistoryStage ℳ T r (i.castSucc.succAbove j) a := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    simp only [Fin.castSucc_zero, Fin.zero_succAbove, homogeneousHistoryStage_succ,
      homogeneousHistoryStage_zero, homogeneousHistory_zero, LinearMap.id_apply]
  | succ n ih =>
    revert hfix
    refine Fin.cases ?_ (fun i => ?_) i
    · intro _
      simp only [Fin.castSucc_zero, Fin.zero_succAbove, Fin.removeNth_zero,
        Fin.tail_def, homogeneousHistoryStage_succ]
    · intro hfix
      have htail : homogeneousHistoryStage ℳ (fun k => T k.succ)
          (fun k => r k.succ) i.castSucc a =
        homogeneousHistoryStage ℳ (fun k => T k.succ) (fun k => r k.succ) i.succ a := by
        simpa only [← Fin.succ_castSucc, homogeneousHistoryStage_succ] using hfix
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [← Fin.succ_castSucc, Fin.succ_succAbove_zero,
          homogeneousHistoryStage_zero, homogeneousHistoryStage_zero]
        exact (homogeneousHistory_removeNth ℳ T r a i.succ hfix).symm
      · have hT : i.removeNth (fun k => T k.succ) =
            fun k => i.succ.removeNth T k.succ := by
          funext k
          simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
        have hr : i.removeNth (fun k => r k.succ) =
            fun k => i.succ.removeNth r k.succ := by
          funext k
          simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
        simpa only [← Fin.succ_castSucc, Fin.succ_succAbove_succ,
          homogeneousHistoryStage_succ, hT, hr] using
          ih (fun k => T k.succ) (fun k => r k.succ) i htail j

section DecomposeSelf

variable {ℳ} {n : ℕ} {T : Fin n → Module.End R M}
  (hT : ∀ j s x, x ∈ ℳ s → (DirectSum.decompose ℳ (T j x) s : M) = x)
include hT

/-- If every map fixes the same-degree component of each homogeneous input,
an encounter whose two recorded degrees coincide leaves the whole decoration
unchanged. The incoming segment has degree `r₀`. -/
theorem homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self
    (r : Fin n → ι) {r₀ : ι} {a : M} (ha : a ∈ ℳ r₀) (j : Fin n)
    (hj : r j = Fin.snoc (α := fun _ => ι) r r₀ j.succ) :
    homogeneousHistoryStage ℳ T r j.castSucc a = homogeneousHistoryStage ℳ T r j.succ a := by
  rw [homogeneousHistoryStage_castSucc_apply]
  apply hT
  rw [hj]
  exact homogeneousHistoryStage_mem_snoc ℳ T r r₀ ⟨a, ha⟩ j.succ

/-- If every map fixes the same-degree component of each homogeneous input,
every segment of a constant-degree history carries its incoming decoration. -/
theorem homogeneousHistoryStage_const_of_decompose_self {r : ι} {a : M} (ha : a ∈ ℳ r)
    (j : Fin (n + 1)) :
    homogeneousHistoryStage ℳ T (fun _ => r) j a = a := by
  induction j using Fin.reverseInduction with
  | last => simp only [homogeneousHistoryStage_last, LinearMap.id_apply]
  | cast j ih =>
    rw [homogeneousHistoryStage_castSucc_eq_succ_of_decompose_self hT (fun _ => r) ha j (by
      refine Fin.lastCases ?_ (fun i => ?_) j.succ <;> simp), ih]

/-- If every map fixes the same-degree component of each homogeneous input,
a constant-degree history fixes its input. -/
theorem homogeneousHistory_const_of_decompose_self {r : ι} {a : M} (ha : a ∈ ℳ r) :
    homogeneousHistory ℳ T (fun _ => r) a = a := by
  simpa only [homogeneousHistoryStage_zero] using
    homogeneousHistoryStage_const_of_decompose_self hT ha 0

end DecomposeSelf

variable {ℳ} {n : ℕ} {T : Fin n → Module.End R M}

/-- If the maps fix diagonal components at the final degree and the recorded
degrees from the output through a chosen segment agree, that segment carries
the final whole decoration. Encounters before the chosen segment may change
degree and decoration. -/
theorem homogeneousHistoryStage_eq_of_degrees_eq
    (r : Fin n → ι) {r₀ : ι} {a : M}
    (hT : ∀ j x, x ∈ ℳ (Fin.snoc (α := fun _ => ι) r r₀ 0) →
      (DirectSum.decompose ℳ (T j x) (Fin.snoc (α := fun _ => ι) r r₀ 0) : M) = x)
    (ha : a ∈ ℳ r₀) (j : Fin (n + 1))
    (hr : ∀ i ≤ j, Fin.snoc (α := fun _ => ι) r r₀ i =
      Fin.snoc (α := fun _ => ι) r r₀ 0) :
    homogeneousHistoryStage ℳ T r j a = homogeneousHistory ℳ T r a := by
  induction j using Fin.inductionOn with
  | zero => rw [homogeneousHistoryStage_zero]
  | succ j ih =>
    have hj : r j = Fin.snoc (α := fun _ => ι) r r₀ 0 := by
      simpa only [Fin.snoc_castSucc] using hr j.castSucc j.castSucc_le_succ
    have hfix : homogeneousHistoryStage ℳ T r j.castSucc a =
        homogeneousHistoryStage ℳ T r j.succ a := by
      rw [homogeneousHistoryStage_castSucc_apply, hj]
      apply hT
      rw [← hr j.succ le_rfl]
      exact homogeneousHistoryStage_mem_snoc ℳ T r r₀ ⟨a, ha⟩ j.succ
    rw [← hfix]
    exact ih (fun i hi => hr i (hi.trans j.castSucc_le_succ))

end Mei
