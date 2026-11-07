/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
import Mathlib.Data.Set.Finite.List

/-!
# Complete decorated types with a bound on encounters

A bound on the number of encounters gives a finite inventory of complete
whole-component histories over a finite wall alphabet. No order on the degree
set is required. Each type retains every encounter, its crossing sign and normal
velocity condition, and its nonzero whole decoration. Its endpoint domain is
the full admissible backward domain, including the original incoming source and
avoidance of unrecorded walls and singularities.

When every actual ray obeys the bound, these domains parameterize all actual
rays, without imposing a bound on the actual-ray carrier. Fixed endpoint and
complete type determine the entire ray, including its incoming tail.
This is the bounded encounter-tree construction of Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*,
Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4), using the existing
`decoratedHistorySupport` and `Convex.admissibleRayRealization`.
-/

public noncomputable section

open Mei.Convex

namespace Mei

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (p₀ : Γ) (a : ℳ p₀) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (ε : J → SignType) (L : ℕ)

/-- A bounded encounter word and a surviving whole-component history satisfying
its crossing signs and normal-velocity conditions. No degree cutoff is imposed. -/
abbrev BoundedDecoratedType :=
  Σ l : {l : List J // l.length ≤ L},
    (decoratedHistorySupport ℳ (fun j => T (l.val.get j)) p₀ a v
      (fun j => f (l.val.get j)) (fun j => ε (l.val.get j)) : Type _)

instance [Finite J] : Finite (BoundedDecoratedType ℳ T p₀ a v f ε L) := by
  let : Finite {l : List J // l.length ≤ L} := (List.finite_length_le J L).to_subtype
  infer_instance

namespace BoundedDecoratedType

variable {ℳ T p₀ a v f ε L}

/-- The final whole decoration, with all scalar multiplicities retained. -/
def decoration (t : BoundedDecoratedType ℳ T p₀ a v f ε L) : M :=
  homogeneousHistory ℳ (fun j => T (t.1.val.get j)) t.2.val a

/-- The decoration is the full homogeneous-history output. -/
@[simp]
theorem decoration_eq (t : BoundedDecoratedType ℳ T p₀ a v f ε L) :
    t.decoration = homogeneousHistory ℳ (fun j => T (t.1.val.get j)) t.2.val a := (rfl)

/-- The decoration of every inventoried type is nonzero. -/
theorem decoration_ne_zero (t : BoundedDecoratedType ℳ T p₀ a v f ε L) :
    t.decoration ≠ 0 :=
  ((mem_decoratedHistorySupport ..).mp t.2.property).1

variable (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)

/-- The complete valid endpoint domain; the incoming tail remains in the
original source specification even when endpoints are later restricted. -/
def domain (t : BoundedDecoratedType ℳ T p₀ a v f ε L) : Set V :=
  admissibleBackwardDomain (fun j => f (t.1.val.get j)) (fun j => c (t.1.val.get j))
    (fun j => v (Fin.snoc (α := fun _ => Γ) t.2.val p₀ j))
    (fun j => P (t.1.val.get j)) W S C

/-- The domain is the original admissible backward domain of the full history. -/
theorem domain_def (t : BoundedDecoratedType ℳ T p₀ a v f ε L) :
    t.domain c P W S C = admissibleBackwardDomain
      (fun j => f (t.1.val.get j)) (fun j => c (t.1.val.get j))
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.2.val p₀ j))
      (fun j => P (t.1.val.get j)) W S C := (rfl)

/-- Membership retains all incidence, avoidance and incoming-source conditions. -/
@[simp]
theorem mem_domain (t : BoundedDecoratedType ℳ T p₀ a v f ε L) (Q : V) :
    Q ∈ t.domain c P W S C ↔ Q ∈ admissibleBackwardDomain
      (fun j => f (t.1.val.get j)) (fun j => c (t.1.val.get j))
      (fun j => v (Fin.snoc (α := fun _ => Γ) t.2.val p₀ j))
      (fun j => P (t.1.val.get j)) W S C := Iff.rfl

end BoundedDecoratedType

variable (c : J → ℝ) (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)

local notation "Ray(" l ", " Q ")" => DecoratedAdmissibleRay ℳ (fun j => T (List.get l j)) p₀ a v
  (fun j => f (List.get l j)) (fun j => c (List.get l j)) (fun j => ε (List.get l j))
  (fun j => P (List.get l j)) W S C Q

/-- A genuine encounter bound identifies the unrestricted actual-ray fiber
with the admitted bounded types. The inverse recovers the unique whole ray. -/
def boundedDecoratedRayFiberEquiv (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) :
    (Σ l : List J, Ray(l, Q)) ≃
      {t : BoundedDecoratedType ℳ T p₀ a v f ε L // Q ∈ t.domain c P W S C} where
  toFun r := ⟨⟨⟨r.1, hbound r.1 r.2⟩, r.2.1⟩, r.2.2.mem_admissibleBackwardDomain⟩
  invFun t := ⟨t.val.1.val, t.val.2, admissibleRayRealization _ _ _ _ _ _ _ _
      ((BoundedDecoratedType.mem_domain c P W S C t.val Q).mp t.property)⟩
  left_inv r := by
    obtain ⟨l, p, β⟩ := r
    exact congrArg (Sigma.mk l) (congrArg (Sigma.mk p) (Subsingleton.elim _ _))
  right_inv _ := rfl

/-- Forgetting geometry retains the full encounter word and degree history. -/
@[simp]
theorem boundedDecoratedRayFiberEquiv_apply_val (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L) (r : Σ l : List J, Ray(l, Q)) :
    (boundedDecoratedRayFiberEquiv ℳ T p₀ a v f ε L c P W S C Q hbound r).val =
      ⟨⟨r.1, hbound r.1 r.2⟩, r.2.1⟩ := (rfl)

/-- The inverse recovers the unique admissible ray with the recorded history. -/
@[simp]
theorem boundedDecoratedRayFiberEquiv_symm_apply (Q : V)
    (hbound : ∀ (l : List J), Ray(l, Q) → l.length ≤ L)
    (t : {t : BoundedDecoratedType ℳ T p₀ a v f ε L // Q ∈ t.domain c P W S C}) :
    (boundedDecoratedRayFiberEquiv ℳ T p₀ a v f ε L c P W S C Q hbound).symm t =
      ⟨t.val.1.val, t.val.2, admissibleRayRealization _ _ _ _ _ _ _ _
      ((BoundedDecoratedType.mem_domain c P W S C t.val Q).mp t.property)⟩ := (rfl)

end Mei
