/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Bounded
public import Mei.LinearAlgebra.GradedModule.History.Filtration

/-!
# Exhaustive varying-chamber families from component filtrations

Suppose component transfers between possibly different graded chamber modules
preserve finite-length filtrations, with prescribed nonnegative increases.
A bound of `h` on unmarked runs of actual rays gives at most `r * h + r - 1`
encounters when the terminal filtration vanishes at order `r`. The unrestricted
endpoint fiber is therefore finite. Rational wall data and lattice velocities
then give exhaustive finite closed charts, proper endpoint and whole-path maps,
and continuous boundary paths admitted by the original incoming source.

The unmarked-run condition is required only for actual admissible rays, so
geometric incidence and avoidance constraints can rule out long runs. No
positive degree monoid, finite set of degrees, coefficient basis or identification
of chamber modules is assumed. Unchanged-degree encounters and degree changes
invisible in space remain part of each history. Boundary paths are not asserted
admissible.

The proof combines `Quiver.Path.length_add_one_le_of_homogeneousHistory_ne_zero`
with the existing exhaustive bounded-family construction. The finiteness
mechanism follows Gross–Hacking–Siebert, *Theta functions on varieties with
effective anti-canonical class*, Proposition 3.5 and Lemma 3.7
(arXiv:1601.07081v4).
-/

public noncomputable section

open Set Filter Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

local notation "Ray" p:max X:max => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X

variable (F : ∀ q, ModuleFiltration R (M q))
  (mark : ∀ {q q' : Q}, (q ⟶ q') → ι q → ι q' → ℕ)
  (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
  {r h₀ : ℕ} (hr : (F b).submodule r = ⊥)

variable {T ℳ i₀ x v ν ε c P W S C F mark}

/-- Filtration increases and bounded unmarked runs control every encounter of
an actual ray through different chamber modules. Only the terminal chamber's
filtration needs to vanish at the stated order. -/
theorem PathDecoratedRay.length_le_of_componentTransfersRaise
    {p : Path a b} {X : V} (β : Ray p X)
    (hraise : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
    (hvanish : (F b).submodule r = ⊥)
    (hrun : Path.IsZeroRunBounded (GradedVertex.componentWeight mark) h₀
      (Path.Degrees.liftPath i₀ p β.1.val)) :
    p.length ≤ r * h₀ + r - 1 := by
  have hne := β.decoration_ne_zero
  rw [PathDecoratedRay.decoration_def] at hne
  have hlen := p.length_add_one_le_of_homogeneousHistory_ne_zero hraise i₀ x.property hvanish
    hne hrun
  rw [Nat.mul_add, Nat.mul_one] at hlen
  omega

variable (T ℳ i₀ x v ν ε c P W S C F mark)
  [Finite Q] [∀ q q' : Q, Finite (q ⟶ q')]

include hT hr in
/-- A nilpotent component filtration and bounded unmarked runs make the entire
actual varying-chamber endpoint fiber finite, with all encounter paths allowed. -/
theorem finite_pathDecoratedRays_of_filtration (X : V)
    (hrun : ∀ (p : Path a b) (β : Ray p X),
      Path.IsZeroRunBounded (GradedVertex.componentWeight mark) h₀
        (Path.Degrees.liftPath i₀ p β.1.val)) :
    Finite (Σ p : Path a b, Ray p X) := by
  apply finite_pathDecoratedRays_of_encounter_bound T ℳ i₀ x v ν ε c P W S C
    (r * h₀ + r - 1) X
  intro p β
  exact β.length_le_of_componentTransfersRaise (F := F) (mark := mark) hT hr (hrun p β)

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)

local notation "vel" => fun q d => i (w q d)
local notation "Types" s:max => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "dirs" t:max => Path.Degrees.reverseVertexLabels vel i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t))
local notation "D" t:max => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "path" t:max => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
local notation "Rays" X:max => Σ p : Path a b,
  PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X

include hT hr hν hP hW hS hC in
/-- Component filtration estimates construct exhaustive closed endpoint charts
for all actual rays through varying chamber modules. The numerical encounter
bound is derived rather than imposed on the resulting ray fiber. The chart
comparison retains complete histories and whole final decorations. -/
theorem exists_closedPathDecoratedRayCharts_of_filtration
    (hrun : ∀ X (p : Path a b)
      (β : PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X),
      Path.IsZeroRunBounded (GradedVertex.componentWeight mark) h₀
        (Path.Degrees.liftPath i₀ p β.1.val)) :
    ∃ s : Finset (Path a b),
      (∀ X (p : Path a b),
        PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X → p ∈ s) ∧
      ∃ (κ : Types s → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
        (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
          IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
          A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
          IsProperMap (fun X : A t j => (path t) X.val) ∧
          ∀ X ∈ A t j, (path t) X 0 = X ∧
            (∀ᶠ r : ℝ in atBot, (path t) X r ∈ C) ∧
            (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
        (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
          (intrinsicInterior ℝ (A t k))) ∧
        (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
        ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃ (Σ X, Rays X),
          (∀ z, (E z).1 = z.2.2.val) ∧
          (∀ z, (E z).2.1 = z.1.1.val) ∧
          (∀ z, HEq (E z).2.2.1 z.1.2) ∧
          ∀ z, (E z).2.2.decoration = z.1.1.val.homogeneousHistory T ℳ z.1.2.val x := by
  apply exists_exhaustive_pathDecoratedFamily_closedCharts T ℳ i₀ x ν ε c P W S C
    h w hν hP hW hS hC (r * h₀ + r - 1)
  intro X p β
  exact β.length_le_of_componentTransfersRaise (F := F) (mark := mark) hT hr (hrun X p β)

end Rational

end Mei
