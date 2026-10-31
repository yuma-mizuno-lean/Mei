/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Extend

/-!
# Attaching a final encounter to a decorated ray

Continue an actual decorated ray to a transverse encounter and select a nonzero
whole homogeneous component of its propagated final decoration. The incoming
history, every earlier decoration, the entire incoming path and its source
admission are retained. The new degree must preserve normal velocity; it may
have the same spatial velocity as the old degree. Thus coefficient changes with
no spatial bend remain recorded encounters.

`DecoratedAdmissibleRay.extend` combines `AdmissibleRayRealization.extend` with
`homogeneousHistory_succ_apply`. The existence and uniqueness criterion separates
the two coefficient conditions, survival and conservation of normal velocity,
from the incidence and avoidance conditions on the attached finite segments.
This is the attachment operation in the last-change recursion for broken-line
sums, following Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Definition 2.10 and §3.3.3 (arXiv:1503.06183v5).
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
  (U : Module.End R M) (q : Γ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t)
  (m : V →L[ℝ] ℝ) (b : ℝ) (H : Set V)

local notation "ε₀" => SignType.sign (m (velocity q))

variable (hcoeff : DirectSum.decompose ℳ (U (r.decoration 0)) q ≠ 0)
  (hnormal : m (velocity q) =
    m (velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0)))
  (htrans : m (velocity q) ≠ 0)
  (hheight : m (r.2.ray s) = b) (hinc : r.2.ray s ∈ H)
  (hW₁ : ∀ j u, 0 < u → u < s → r.2.ray u ∉ W j)
  (hW₂ : ∀ j u, -t < u → u ≤ 0 → (-u • velocity q) +ᵥ
      (r.2.ray.extend s t (velocity q) hs ht).endpoint ∉ W j)
  (hS₁ : ∀ j u, 0 < u → u ≤ s → r.2.ray u ∉ S j)
  (hS₂ : ∀ j u, -t < u → u ≤ 0 → (-u • velocity q) +ᵥ
      (r.2.ray.extend s t (velocity q) hs ht).endpoint ∉ S j)

/-- Attach the whole degree-`q` component after applying `U` at a new final
encounter. Incidence and avoidance are checked only on the two attached finite
segments. No diagonal or positivity hypothesis on propagation is required. -/
def extend :
    DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a velocity
      (Fin.cons m f) (Fin.cons b c) (Fin.cons ε₀ ε) (Fin.cons H P) W S C
      (r.2.ray.extend s t (velocity q) hs ht).endpoint := by
  let p : Fin (n + 1) → Γ := Fin.cons (α := fun _ => Γ) q r.1.val
  have hv : (fun j => velocity (Fin.snoc (α := fun _ => Γ) p p₀ j)) =
      Fin.cons (velocity q) (fun j => velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ j)) := by
    dsimp only [p]
    rw [← Fin.cons_snoc_eq_snoc_cons]
    exact Fin.comp_cons velocity q _
  refine ⟨⟨p, (mem_decoratedHistorySupport ..).mpr ⟨?_, ?_⟩⟩,
    (r.2.extend s t (velocity q) hs ht m b H htrans hheight hinc hW₁ hW₂ hS₁ hS₂).congrVelocity
      hv.symm⟩
  · rw [homogeneousHistory_succ_apply]
    rw [decoration_zero] at hcoeff
    exact Submodule.coe_eq_zero.not.mpr hcoeff
  · intro j
    cases j using Fin.cases with
    | zero =>
      simp only [p, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]
      exact ⟨hnormal, trivial⟩
    | succ j =>
      simpa only [p, Fin.cons_succ, ← Fin.cons_snoc_eq_snoc_cons] using
        And.intro (r.normal_velocity_eq j) (r.crossing_sign j)

/-- Attachment prepends the selected output degree to the old history. -/
@[simp]
theorem history_extend :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).1.val =
      Fin.cons (α := fun _ => Γ) q r.1.val := (rfl)

/-- The decorated attachment uses the canonical geometric extension. Its
incoming path and tail are therefore preserved by translation of time. -/
@[simp]
theorem ray_extend :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).2.ray =
      r.2.ray.extend s t (velocity q) hs ht := by
  simp only [extend, AdmissibleRayRealization.ray_congrVelocity,
    AdmissibleRayRealization.ray_extend]

/-- The new encounter occurs at `-t`, and old encounter times translate by
`s + t`. The endpoint parameter remains zero. -/
@[simp]
theorem parameter_extend :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).2.parameter =
      Fin.cons (α := fun _ => ℝ) 0
        (Fin.cons (α := fun _ => ℝ) (-t) (fun j => r.2.parameter j.succ - (s + t))) := by
  simp only [extend, AdmissibleRayRealization.parameter_congrVelocity,
    AdmissibleRayRealization.parameter_extend]

/-- Every earlier segment retains its entire original decoration. -/
@[simp]
theorem decoration_succ_extend (j : Fin (n + 1)) :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).decoration
      j.succ = r.decoration j := by
  simp only [decoration_def, history_extend, homogeneousHistoryStage_succ, Fin.cons_succ]

/-- The new final decoration is precisely the whole chosen output component. -/
@[simp↓]
theorem decoration_zero_extend :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).decoration
      0 = (DirectSum.decompose ℳ (U (r.decoration 0)) q : M) := by
  simp only [decoration_zero, history_extend, homogeneousHistory_succ_apply,
    Fin.cons_zero, Fin.cons_succ]
  rfl

/-- The new encounter is at the end of the straight continuation of the old
ray, even when the new degree has the same spatial velocity. -/
theorem extend_ray_parameter_one :
    (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).2.ray
      ((r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).2.parameter
        (0 : Fin (n + 1)).succ) = r.2.ray s := by
  rw [ray_extend, parameter_extend, Fin.cons_succ, Fin.cons_zero,
    FiniteAffineRay.extend_apply_of_le _ _ _ _ hs ht le_rfl]
  congr 1
  ring

include htrans hheight hinc hW₁ hW₂ hS₁ hS₂ in
omit hcoeff hnormal in
/-- Once the attached geometry is admissible, a unique decorated extension
with the prescribed history exists exactly when the chosen whole component
survives and preserves normal velocity. In particular killed components create
no ray; a nonzero degree change with unchanged spatial velocity is allowed. -/
theorem existsUnique_extend_iff :
    (∃! z : DecoratedAdmissibleRay ℳ (Fin.cons U T) p₀ a velocity
        (Fin.cons m f) (Fin.cons b c) (Fin.cons ε₀ ε) (Fin.cons H P) W S C
        (r.2.ray.extend s t (velocity q) hs ht).endpoint,
      z.1.val = Fin.cons (α := fun _ => Γ) q r.1.val) ↔
      DirectSum.decompose ℳ (U (r.decoration 0)) q ≠ 0 ∧
        m (velocity q) = m (velocity (Fin.snoc (α := fun _ => Γ) r.1.val p₀ 0)) := by
  constructor
  · rintro ⟨z, hz, _⟩
    have hmem := (mem_decoratedHistorySupport ..).mp z.1.property
    have hn := z.normal_velocity_eq 0
    rw [hz] at hmem hn
    refine ⟨?_, ?_⟩
    · rw [homogeneousHistory_succ_apply] at hmem
      rw [decoration_zero]
      exact Submodule.coe_eq_zero.not.mp hmem.1
    · simpa only [Fin.cons_zero, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ] using hn
  · rintro ⟨hcoeff, hnormal⟩
    refine ⟨r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂,
      history_extend .., fun z hz => ?_⟩
    have hp : z.1 =
        (r.extend U q s t hs ht m b H hcoeff hnormal htrans hheight hinc hW₁ hW₂ hS₁ hS₂).1 :=
      Subtype.ext (hz.trans (history_extend ..).symm)
    exact Sigma.ext hp (Subsingleton.helim (by rw [hp]) _ _)

end Mei.DecoratedAdmissibleRay
