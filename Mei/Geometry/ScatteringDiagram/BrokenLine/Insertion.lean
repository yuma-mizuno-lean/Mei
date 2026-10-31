/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Insertion
public import Mei.LinearAlgebra.GradedModule.History.Identity

/-!
# Restoring identity encounters on decorated rays

Restore an identity propagation map at a transverse encounter inside a straight
segment of an actual decorated ray. Repeat the segment degree, retain the path
and incoming tail, and preserve every whole decoration. The inserted wall joins
the obstacle family, so its unrecorded intersections must be absent.

This combines `AdmissibleRayRealization.insertEncounter` with
`homogeneousHistory_insertNth_id`. It restores the decorations when
an inactive identity wall is reinserted. Degree changes with zero spatial shift
are retained: the inserted map is required to be the identity on coefficients.
The broken-line conventions follow Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.DecoratedAdmissibleRay

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} {T : Fin n → Module.End R M} {p₀ : Γ} {a : ℳ p₀}
  {velocity : Γ → V} {f : Fin n → V →L[ℝ] ℝ} {c : Fin n → ℝ}
  {ε : Fin n → SignType} {P : Fin n → Set V}
  {W : J → Set V} {S : K → Set V} {C : Set V} {Q : V}
  (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
  (i : Fin (n + 1)) (t : ℝ)
  (hbefore : t < r.2.parameter i)
  (hafter : ∀ j, i < j → r.2.parameter j < t)
  (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)
  (htrans : m (velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ i)) ≠ 0)
  (hheight : m (r.2.ray t) = b) (hinc : r.2.ray t ∈ H)
  (havoid : ∀ s, s < 0 → s ≠ t →
    (∀ j : Fin n, s ≠ r.2.parameter j.succ) → r.2.ray s ∉ H)
  (hoff : Q ∉ H)

local notation "q" => Fin.snoc (α := fun _ => Γ) r.fst.val p₀ i
local notation "ε₀" => SignType.sign (m (velocity q))

/-- Restore an identity wall encounter, repeating its incoming degree. All
previous encounters, the actual path and the final whole coefficient are retained. -/
def insertIdentityEncounter :
    DecoratedAdmissibleRay ℳ (i.insertNth LinearMap.id T) p₀ a velocity
      (i.insertNth (α := fun _ => V →L[ℝ] ℝ) m f)
      (i.insertNth (α := fun _ => ℝ) b c)
      (i.insertNth (α := fun _ => SignType) ε₀ ε)
      (i.insertNth (α := fun _ => Set V) H P)
      (Sum.elim W (fun _ : Unit => H)) S C Q := by
  let p := i.insertNth (α := fun _ => Γ) q r.1.val
  have hv : (fun j => velocity (Fin.snoc (α := fun _ => Γ) p p₀ j)) =
      i.succ.insertNth (α := fun _ => V) (velocity q)
        (fun j => velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j)) := by
    funext j
    rw [Fin.snoc_insertNth_self]
    cases j using Fin.succAboveCases i.succ <;> simp
  let g := r.2.insertEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff
  have hg : AdmissibleRayRealization (i.insertNth m f) (i.insertNth b c)
      (fun j => velocity (Fin.snoc (α := fun _ => Γ) p p₀ j))
      (i.insertNth H P) (Sum.elim W (fun _ : Unit => H)) S C Q := by
    exact { g with
      transverse := fun j => by
        rw [congrFun hv j.castSucc]
        exact g.transverse j
      directionAt_eq := fun j => by
        rw [congrFun hv j]
        exact g.directionAt_eq j }
  refine ⟨⟨p, (mem_decoratedHistorySupport ..).mpr ⟨?_, ?_⟩⟩, hg⟩
  · rw [homogeneousHistory_insertNth_id]
    exact (mem_decoratedHistorySupport ..).mp r.1.property |>.1
  · intro j
    have hout : velocity (p j) =
        i.insertNth (α := fun _ => V) (velocity q) (fun k => velocity (r.1.val k)) j := by
      cases j using Fin.succAboveCases i <;> simp [p]
    rw [hout, congrFun hv j.succ]
    cases j using Fin.succAboveCases i with
    | x => simp
    | p j =>
      simpa only [Fin.insertNth_apply_succAbove, ← Fin.succ_succAbove_succ] using
        And.intro (r.normal_velocity_eq j) (r.crossing_sign j)

/-- The restored encounter repeats the degree of the segment containing it. -/
@[simp]
theorem history_insertIdentityEncounter :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).1.val =
      i.insertNth (α := fun _ => Γ) q r.1.val := (rfl)

/-- The entire geometric ray and its incoming tail are preserved. -/
@[simp]
theorem ray_insertIdentityEncounter :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).2.ray =
      r.2.ray := by
  simp only [insertIdentityEncounter, AdmissibleRayRealization.ray_insertEncounter]

/-- The enlarged parameter tuple retains the old times and records the new one. -/
@[simp]
theorem parameter_insertIdentityEncounter :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).2.parameter
      = i.succ.insertNth (α := fun _ => ℝ) t r.2.parameter := by
  simp only [insertIdentityEncounter, AdmissibleRayRealization.parameter_insertEncounter]

/-- Every retained segment keeps its whole homogeneous decoration. At the
inserted encounter the same degree and decoration occur on both sides. -/
@[simp]
theorem decoration_insertIdentityEncounter (j : Fin (n + 1)) :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).decoration
      (i.castSucc.succAbove j) = r.decoration j := by
  simp only [decoration_def, history_insertIdentityEncounter,
    homogeneousHistoryStage_insertNth_id]

/-- The extra outgoing segment has the original segment's whole decoration. -/
@[simp]
theorem decoration_castSucc_insertIdentityEncounter :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).decoration
      i.castSucc = r.decoration i := by
  rw [decoration_castSucc, Fin.insertNth_apply_same, LinearMap.id_apply,
    history_insertIdentityEncounter, Fin.insertNth_apply_same]
  have hi := r.decoration_insertIdentityEncounter i t hbefore hafter
    m b H htrans hheight hinc havoid hoff i
  rw [Fin.succAbove_castSucc_self] at hi
  rw [hi]
  rw [decoration_def]
  exact DirectSum.decompose_of_mem_same ℳ
    (homogeneousHistoryStage_mem_snoc ℳ T r.1.val p₀ a i)

/-- Restoring an identity encounter preserves the final whole decoration. -/
@[simp↓]
theorem decoration_zero_insertIdentityEncounter :
    (r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff).decoration
      0 = r.decoration 0 := by
  rw [decoration_zero, decoration_zero, history_insertIdentityEncounter,
    homogeneousHistory_insertNth_id]

include hbefore hafter in
omit htrans hheight hinc havoid hoff in
/-- The geometric admission conditions are necessary and sufficient for
restoring an identity encounter with the prescribed history, path and times.
There is no additional coefficient condition on a contributing decorated ray. -/
theorem exists_insertIdentityEncounter_iff :
    (∃ s : DecoratedAdmissibleRay ℳ (i.insertNth LinearMap.id T) p₀ a velocity
        (i.insertNth (α := fun _ => V →L[ℝ] ℝ) m f)
        (i.insertNth (α := fun _ => ℝ) b c)
        (i.insertNth (α := fun _ => SignType) ε₀ ε)
        (i.insertNth (α := fun _ => Set V) H P)
        (Sum.elim W (fun _ : Unit => H)) S C Q,
      s.1.val = i.insertNth (α := fun _ => Γ) q r.1.val ∧
        s.2.ray = r.2.ray ∧
        s.2.parameter = i.succ.insertNth (α := fun _ => ℝ) t r.2.parameter) ↔
      m (velocity q) ≠ 0 ∧ m (r.2.ray t) = b ∧ r.2.ray t ∈ H ∧
        (∀ s, s < 0 → s ≠ t →
          (∀ j : Fin n, s ≠ r.2.parameter j.succ) → r.2.ray s ∉ H) ∧ Q ∉ H := by
  constructor
  · rintro ⟨s, hh, hr, hp⟩
    have ht : s.2.parameter i.succ = t := by simp [hp]
    refine ⟨?_, ?_, ?_, ?_, s.2.off_walls (.inr ())⟩
    · have hs := s.2.transverse i
      rw [hh, Fin.snoc_castSucc, Fin.insertNth_apply_same,
        Fin.insertNth_apply_same] at hs
      exact hs
    · simpa only [Fin.insertNth_apply_same, ht, hr] using s.2.height_eq i
    · simpa only [Fin.insertNth_apply_same, ht, hr] using s.2.incidence i
    · intro u hu hut huold
      rw [← hr]
      apply s.2.avoids_walls (.inr ()) u hu
      intro j
      cases j using Fin.succAboveCases i
      · simpa only [ht] using hut
      · simpa only [hp, ← Fin.succ_succAbove_succ, Fin.insertNth_apply_succAbove]
          using huold _
  · rintro ⟨htrans, hheight, hinc, havoid, hoff⟩
    exact ⟨r.insertIdentityEncounter i t hbefore hafter m b H htrans hheight hinc havoid hoff,
      history_insertIdentityEncounter .., ray_insertIdentityEncounter ..,
      parameter_insertIdentityEncounter ..⟩

end Mei.DecoratedAdmissibleRay
