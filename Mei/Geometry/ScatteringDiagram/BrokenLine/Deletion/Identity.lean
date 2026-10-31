/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Deletion
public import Mei.LinearAlgebra.GradedModule.History.Identity

/-!
# Identity erasure on actual decorated ray fibers

Deleting an identity encounter embeds its actual decorated ray fiber in the
shorter fiber. Its image consists exactly of the shorter rays whose restored
degree history has the prescribed crossing signs and admits the full original
geometry. Consequently weighted evaluation is a sum over this explicitly
characterized subset of the shorter fiber. No surjectivity is asserted when
the omitted support prevents geometric reinsertion.

Each omitted encounter point must miss the retained walls, so coincident
walls that remain active cannot be silently erased. All incoming-source and
singular-avoidance conditions persist.
These comparisons allow an encounter that becomes inactive after coefficient
truncation to be removed without identifying distinct contributing histories.

We combine `DecoratedAdmissibleRay.removeEncounter` with
`homogeneousHistorySupportRemoveIdentityEquiv` and the uniqueness of admissible
realizations of a fixed degree history. Whole-component propagation and wall
truncation follow Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J J' K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin (n + 1) → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {v : Γ → V} {f : Fin (n + 1) → V →L[ℝ] ℝ} {c : Fin (n + 1) → ℝ}
  {ε : Fin (n + 1) → SignType} {P : Fin (n + 1) → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}

/-- An identity encounter in a contributing ray fixes the whole decoration on
its adjacent segments. Nonvanishing forces their homogeneous degrees to agree. -/
theorem decoration_castSucc_eq_succ_of_eq_id
    (r : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q)
    (i : Fin (n + 1)) (hi : T i = LinearMap.id) :
    r.decoration i.castSucc = r.decoration i.succ := by
  have hne := (mem_decoratedHistorySupport ..).mp r.1.property |>.1
  rw [r.decoration_castSucc, hi, LinearMap.id_apply,
    homogeneousHistory_degree_eq_of_eq_id ℳ T r.1.val p₀ a hne i hi]
  rw [decoration_def]
  exact DirectSum.decompose_of_mem_same ℳ
    (homogeneousHistoryStage_mem_snoc ℳ T r.1.val p₀ a i.succ)

local notation "Full" => DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q

variable (i : Fin (n + 1)) (hi : T i = LinearMap.id)
  (W' : J' → Set V) (e : J' → J) (hW : ∀ j, W' j ⊆ W (e j))
  (hoff : ∀ r : DecoratedAdmissibleRay ℳ T p₀ a v f c ε P W S C Q,
    ∀ j, r.2.ray (r.2.parameter i.succ) ∉ W' j)
local notation "Short" => DecoratedAdmissibleRay ℳ (i.removeNth T) p₀ a v
  (i.removeNth f) (i.removeNth c) (i.removeNth ε) (i.removeNth P) W' S C Q

/-- Erasing an identity encounter is injective on actual decorated rays.
Each omitted encounter point misses the retained wall family; no existence of a
reinsertion for arbitrary shorter rays is assumed. -/
def removeIdentityEncounterEmbedding : Full ↪ Short where
  toFun r := r.removeEncounter i (r.decoration_castSucc_eq_succ_of_eq_id i hi)
    W' e hW (hoff r)
  inj' r s hrs := by
    have hh : i.removeNth r.1.val = i.removeNth s.1.val :=
      by simpa only [history_removeEncounter] using
        congrArg (fun z : Short => z.1.val) hrs
    have hp : r.1 = s.1 := by
      apply Subtype.ext
      let er := homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a i hi
      have hr : r.1.val ∈ homogeneousHistorySupport ℳ T (a : M) :=
        (mem_homogeneousHistorySupport ..).mpr ((mem_decoratedHistorySupport ..).mp r.1.property).1
      have hs : s.1.val ∈ homogeneousHistorySupport ℳ T (a : M) :=
        (mem_homogeneousHistorySupport ..).mpr ((mem_decoratedHistorySupport ..).mp s.1.property).1
      have he : er ⟨_, hr⟩ = er ⟨_, hs⟩ := Subtype.ext (by
        simpa only [er, homogeneousHistorySupportRemoveIdentityEquiv_val] using hh)
      exact congrArg (fun z : (homogeneousHistorySupport ℳ T (a : M) : Type _) => z.val)
        (er.injective he)
    exact Sigma.fst_injective hp

/-- The shortened degree history deletes exactly the chosen entry. -/
@[simp]
theorem history_removeIdentityEncounterEmbedding (r : Full) :
    (removeIdentityEncounterEmbedding i hi W' e hW hoff r).1.val =
      i.removeNth r.1.val := by
  exact history_removeEncounter ..

/-- Identity erasure retains the entire path and incoming tail. -/
@[simp]
theorem ray_removeIdentityEncounterEmbedding (r : Full) :
    (removeIdentityEncounterEmbedding i hi W' e hW hoff r).2.ray = r.2.ray := by
  exact ray_removeEncounter ..

/-- Every remaining encounter keeps its original time. -/
@[simp]
theorem parameter_removeIdentityEncounterEmbedding (r : Full) (j : Fin (n + 1)) :
    (removeIdentityEncounterEmbedding i hi W' e hW hoff r).2.parameter j =
      r.2.parameter (i.succ.succAbove j) := by
  exact parameter_removeEncounter ..

/-- Every retained segment keeps its whole homogeneous decoration. -/
@[simp]
theorem decoration_removeIdentityEncounterEmbedding (r : Full) (j : Fin (n + 1)) :
    (removeIdentityEncounterEmbedding i hi W' e hW hoff r).decoration j =
      r.decoration (i.castSucc.succAbove j) := by
  exact decoration_removeEncounter ..

/-- Identity erasure preserves the whole final coefficient. -/
@[simp↓]
theorem decoration_zero_removeIdentityEncounterEmbedding (r : Full) :
    (removeIdentityEncounterEmbedding i hi W' e hW hoff r).decoration 0 =
      r.decoration 0 := by
  exact decoration_zero_removeEncounter ..

local notation "restore" s:max => i.insertNth (α := fun _ => Γ)
  (Fin.snoc (α := fun _ => Γ) (Subtype.val (Sigma.fst s)) p₀ i) (Subtype.val (Sigma.fst s))

include hi hW hoff in
/-- A shorter decorated ray comes from erasure exactly when its restored
history has the original signed normal conditions and its endpoint admits the
full original geometry. These tests retain all incoming and obstacle data. -/
theorem mem_range_removeIdentityEncounterEmbedding_iff (s : Short) :
    s ∈ range (removeIdentityEncounterEmbedding i hi W' e hW hoff) ↔
      restore s ∈ decoratedHistorySupport ℳ T p₀ a v f ε ∧
      Q ∈ admissibleBackwardDomain f c
        (fun j => v (Fin.snoc (α := fun _ => Γ) (restore s) p₀ j)) P W S C := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r.1.val ∈ homogeneousHistorySupport ℳ T (a : M) :=
      (mem_homogeneousHistorySupport ..).mpr ((mem_decoratedHistorySupport ..).mp r.1.property).1
    have he := congrArg Subtype.val
      ((homogeneousHistorySupportRemoveIdentityEquiv ℳ T p₀ a i hi).symm_apply_apply ⟨_, hr⟩)
    simp only [homogeneousHistorySupportRemoveIdentityEquiv_symm_val,
      homogeneousHistorySupportRemoveIdentityEquiv_val] at he
    simp only [history_removeIdentityEncounterEmbedding, he]
    exact ⟨r.1.property, r.2.mem_admissibleBackwardDomain⟩
  · rintro ⟨hs, hQ⟩
    let r : Full := ⟨⟨restore s, hs⟩, admissibleRayRealization _ _ _ _ _ _ _ _ hQ⟩
    refine ⟨r, ?_⟩
    have hh : (removeIdentityEncounterEmbedding i hi W' e hW hoff r).1 = s.1 := by
      apply Subtype.ext
      simp only [history_removeIdentityEncounterEmbedding, r, Fin.removeNth_insertNth]
    exact Sigma.fst_injective hh

include hi hW hoff in
open Classical in
/-- Evaluate the original decorated fiber as a weighted sum over exactly the
shorter rays that admit restoration of the erased identity encounter. The test
uses the original signed history and complete geometric endpoint domain, so
source restrictions, singular obstacles and unrecorded walls are retained.
No order or cancellation hypothesis on coefficients is needed. -/
theorem _root_.Mei.decoratedRayEvaluation_eq_sum_removeIdentityEncounter :
    decoratedRayEvaluation ℳ T p₀ a v f c ε P W S C Q =
      let := Fintype.ofFinite Short
      ∑ s : Short,
        if restore s ∈ decoratedHistorySupport ℳ T p₀ a v f ε ∧
          Q ∈ admissibleBackwardDomain f c
            (fun j => v (Fin.snoc (α := fun _ => Γ) (restore s) p₀ j)) P W S C
        then s.decoration 0 else 0 := by
  classical
  dsimp only
  let := Fintype.ofFinite Full
  let := Fintype.ofFinite Short
  let er : Full ↪ Short := removeIdentityEncounterEmbedding i hi W' e hW hoff
  rw [decoratedRayEvaluation_def]
  apply Fintype.sum_of_injective er er.injective
  · intro s hs
    exact ite_eq_right (fun h => hs ((mem_range_removeIdentityEncounterEmbedding_iff
      i hi W' e hW hoff s).mpr h))
  · intro r
    rw [ite_eq_left ((mem_range_removeIdentityEncounterEmbedding_iff
      i hi W' e hW hoff (er r)).mp ⟨r, rfl⟩)]
    exact (decoration_zero_removeIdentityEncounterEmbedding i hi W' e hW hoff r).symm

end Mei.DecoratedAdmissibleRay
