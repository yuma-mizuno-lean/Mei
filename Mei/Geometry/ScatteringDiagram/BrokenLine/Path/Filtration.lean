/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Bounded
public import Mei.Geometry.Convex.Sweep.Encounter.Bound
public import Mei.LinearAlgebra.GradedModule.History.Path.Marks

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

Alternatively, if unmarked components preserve spatial direction, every actual ray
has at most `n * N` encounters, where `N` is the number of arrows. This needs no
unmarked-run hypothesis. The estimate ranks the segments by the accumulated marks
of their history; a run of equal rank is straight and meets each hyperplane at most
once. Hence any inventory containing the paths of length at most `n * N` gives closed
charts for all actual rays.

The unmarked-run proof combines
`Quiver.Path.length_add_one_le_of_homogeneousHistory_ne_zero` with the existing
exhaustive bounded-family construction. The directional estimate uses
`Quiver.Path.Degrees.reverseRanks` and
`Convex.encounter_count_le_of_antitone_rank`. The finiteness mechanisms follow
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4); the closed charts follow
Carl–Pumperla–Siebert, *A tropical view on Landau–Ginzburg models*, §4
(arXiv:2205.07753v2).
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

namespace PathDecoratedRay

variable {p : Path a b} {X : V}

/-- A nilpotent component filtration bounds the encounters of every actual decorated ray
along a quiver path by the product of its vanishing order and the number of arrows. The
filtrations of different chamber modules are unrelated, and components with zero mark
need only preserve the spatial direction. -/
theorem length_le_of_filtration [Finite (Σ b c : Q, b ⟶ c)]
    (β : Ray p X)
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
    (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), mark e i j = 0 → v b i = v c j)
    {n : ℕ} (hn : (F b).submodule n = ⊥) :
    p.length ≤ n * Nat.card (Σ b c : Q, b ⟶ c) := by
  obtain ⟨d, β⟩ := β
  obtain ⟨hpos, -, -⟩ := β.eq_backwardRay
  have hne := ((mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε p d.val).mp d.property).1
  have hν : (fun j => ν (p.reverseArrowLabels (fun e => (⟨_, _, e⟩ : Σ b c : Q, b ⟶ c)) j).2.2) =
      p.reverseArrowLabels ν :=
    (Path.reverseArrowLabels_comp (fun e => (⟨_, _, e⟩ : Σ b c : Q, b ⟶ c))
      (fun z => ν z.2.2) p).symm
  have hc : (fun j => c (p.reverseArrowLabels (fun e => (⟨_, _, e⟩ : Σ b c : Q, b ⟶ c)) j).2.2) =
      p.reverseArrowLabels c :=
    (Path.reverseArrowLabels_comp (fun e => (⟨_, _, e⟩ : Σ b c : Q, b ⟶ c))
      (fun z => c z.2.2) p).symm
  refine encounter_count_le_of_antitone_rank (fun z : Σ b c : Q, b ⟶ c => ν z.2.2)
    (fun z => c z.2.2) (p.reverseArrowLabels fun e => (⟨_, _, e⟩ : Σ b c : Q, b ⟶ c))
    (Path.Degrees.reverseVertexLabels v i₀ p d.val) X ?_ ?_
    (Path.Degrees.reverseRanks mark i₀ p d.val)
    (Path.Degrees.antitone_reverseRanks mark i₀ p d.val)
    (Path.Degrees.reverseRanks_zero_lt_of_homogeneousHistory_ne_zero p hT i₀ x.property hn hne)
    fun j hj => Path.Degrees.reverseVertexLabels_castSucc_eq_succ_of_reverseRanks_eq mark i₀ v
      hstraight p d.val j hj
  · rw [hν, hc]
    exact hpos
  · intro j
    rw [congrFun hν j]
    exact β.transverse j

end PathDecoratedRay

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

include hT hr in
/-- If unmarked components preserve spatial directions, a nilpotent component
filtration makes the unrestricted actual-ray fiber finite, with no unmarked-run
hypothesis. Degrees and arrows may recur along a path. -/
theorem finite_pathDecoratedRays_of_filtration_of_direction_eq (X : V)
    (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c),
      mark e i j = 0 → v b i = v c j) :
    Finite (Σ p : Path a b, Ray p X) := by
  apply finite_pathDecoratedRays_of_encounter_bound T ℳ i₀ x v ν ε c P W S C
    (r * Nat.card (Σ b c : Q, b ⟶ c)) X
  intro p β
  exact β.length_le_of_filtration (F := F) (mark := mark) hT hstraight hr

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

section Direction

variable (s : Finset (Path a b))
  (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i' : ι b) (j : ι c),
    mark e i' j = 0 → i (w b i') = i (w c j))
  (hs : ∀ p : Path a b, p.length ≤ r * Nat.card (Σ b c : Q, b ⟶ c) → p ∈ s)

include hT hr hν hP hW hS hC hstraight hs in
/-- A nilpotent component filtration and direction preservation on unmarked components
give finite closed endpoint charts exhausting every actual decorated ray. It suffices
that the finite inventory `s` contains all paths of length at most `n * N`; no bound on
unmarked runs is assumed. The relative interiors are in bijection with all actual rays
and retain endpoints, complete histories and final decorations. The closures add only
limits of valid endpoints with proper endpoint and whole-path inclusions. -/
theorem exists_pathDecoratedRay_closedCharts_of_filtration_of_direction_eq :
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
  have hbound (X : V) (p : Path a b)
      (β : PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X) : p ∈ s :=
    hs p (β.length_le_of_filtration (F := F) (mark := mark) hT hstraight hr)
  let e (X : V) := Equiv.sigmaSubtypeEquivOfSubset
    (fun p : Path a b => PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X)
    (fun p => p ∈ s) (hbound X)
  obtain ⟨κ, hκ, A, hA, hdisj, hcover, E, hX, ht⟩ :=
    exists_pathDecoratedFamily_closedCharts T ℳ i₀ x s ν ε c P W S C
      h w hν hP hW hS hC
  refine ⟨κ, hκ, A, hA, hdisj, hcover,
    E.trans (Equiv.sigmaCongrRight e), hX, ?_, ?_, ?_⟩
  · intro z
    exact congrArg (fun t : Types s => t.1.val) (ht z)
  · intro z
    exact (Sigma.mk.inj_iff.mp (ht z)).2
  · intro z
    rw [PathDecoratedRay.decoration_def]
    exact congrArg (fun t : Types s => t.1.val.homogeneousHistory T ℳ t.2.val x) (ht z)

end Direction

end Rational

end Mei
