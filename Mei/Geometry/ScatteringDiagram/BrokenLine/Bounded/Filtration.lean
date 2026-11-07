/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Bounded.Family
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.EncounterBound

/-!
# Exhaustive closed endpoint charts from nilpotent component filtrations

A component filtration vanishing at order `r` and a finite supporting-hyperplane
alphabet give a finite family of all actual decorated rays, over every encounter
word. Unmarked components must preserve spatial direction. The encounter bound
is derived from the filtration; it is not a restriction on the ray carrier.
The resulting closed polyhedral endpoint charts retain the endpoint, complete
encounter word and final whole decoration. No positive degree monoid is needed.

This combines `DecoratedAdmissibleRay.encounter_count_le_of_filtration` with the
bounded endpoint-family construction. In particular it supplies that construction
for the nilpotent-ideal component estimates of ordinary function walls and slab
faces. The argument is the straight-piece finiteness mechanism of
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set

namespace Mei

variable {R M Γ V J K O : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (T : J → Module.End R M) (p₀ : Γ) (a : ℳ p₀) (v : Γ → V)
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : O → Set V) (S : K → Set V) (C : Set V)
  (F : ModuleFiltration R M) (mark : J → Γ → Γ → ℕ)
  (hT : ∀ e p q k (x : M), x ∈ ℳ p → x ∈ F.submodule k →
    homogeneousComponent ℳ q (T e x) ∈ F.submodule (k + mark e p q))
  (hstraight : ∀ e p q, mark e p q = 0 → v p = v q)
  {r : ℕ} (hr : F.submodule r = ⊥)

local notation "Ray(" l ", " Q ")" => DecoratedAdmissibleRay ℳ
  (fun j => T (List.get l j)) p₀ a v
  (fun j => f (List.get l j)) (fun j => c (List.get l j))
  (fun j => ε (List.get l j)) (fun j => P (List.get l j)) W S C Q

include hT hstraight hr in
/-- A nilpotent component filtration makes the unrestricted actual-ray fiber
finite. Degrees may recur and the same wall may occur in different straight pieces. -/
theorem finite_decoratedAdmissibleRays_of_filtration (Q : V) :
    Finite (Σ l : List J, Ray(l, Q)) := by
  have hbound (l : List J) (β : Ray(l, Q)) : l.length ≤ r * Nat.card J :=
    β.encounter_count_le_of_filtration (wall := l.get) F mark hT hstraight hr
  exact Finite.of_equiv _
    (boundedDecoratedRayFiberEquiv ℳ T p₀ a v f ε (r * Nat.card J) c P W S C Q hbound).symm

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Γ → Λ) [Finite K] [Finite O]
  (hf : ∀ j, Toric.IsRationalFunctional h (f j).toLinearMap)
  (hP : ∀ j, IsRationalSemilinear h (P j))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "Types" => BoundedDecoratedType ℳ T p₀ a (fun q => i (w q)) f ε (r * Nat.card J)

include hT hr hf hP hW hS hC in
/-- Nilpotent component filtrations give exhaustive finite closed endpoint
charts, without an assumed encounter bound. Their relative interiors are in
bijection with all actual rays and retain their complete labels and weights.
Closed charts include limiting endpoints, with proper endpoint inclusions;
boundary-path admissibility and the classification of degenerations are separate. -/
theorem exists_closedDecoratedRayCharts_of_filtration
    (hstraight : ∀ e p q, mark e p q = 0 → i (w p) = i (w q)) :
    ∃ (κ : Types → Type) (_ : ∀ t, Finite (κ t)) (B : ∀ t, κ t → Set V),
      (∀ t j, (B t j).Nonempty ∧ IsRationalNormalPolyhedron h (B t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (B t j)) ∧
        B t j ⊆ closure (t.domain c P W S C) ∧
        IsProperMap (fun Q : B t j => (Q : V))) ∧
      (∀ t, Pairwise fun j l => Disjoint (intrinsicInterior ℝ (B t j))
        (intrinsicInterior ℝ (B t l))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (B t j) = t.domain c P W S C) ∧
      ∃ e : (Σ t, Σ j : κ t, intrinsicInterior ℝ (B t j)) ≃
          (Σ Q, Σ l : List J, DecoratedAdmissibleRay ℳ
            (fun j => T (l.get j)) p₀ a (fun q => i (w q))
            (fun j => f (l.get j)) (fun j => c (l.get j))
            (fun j => ε (l.get j)) (fun j => P (l.get j)) W S C Q),
        (∀ z, (e z).1 = z.2.2.val) ∧
        (∀ z, (e z).2.1 = z.1.1.val) ∧
        ∀ z, (e z).2.2.decoration 0 = z.1.decoration := by
  apply exists_boundedBrokenLineFamily_closedCharts
    ℳ T p₀ a f c ε P W S C h w hf hP hW hS hC
  intro Q l β
  exact β.encounter_count_le_of_filtration (wall := l.get) F mark hT hstraight hr

end Rational

end Mei
