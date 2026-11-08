/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Encounter.Bound
public import Mei.LinearAlgebra.GradedModule.History.Path.Marks
public import TauCeti.Combinatorics.Quiver.BoundedPaths

/-!
# Exhaustive closed ray charts through different chamber modules

Let a finite quiver of chambers carry a nilpotent filtration on every chamber module,
raised by the component transfers along its arrows with prescribed marks. If an
unmarked component preserves the spatial direction, a nonzero history along any
encounter path has at most `n * N` encounters, where `n` is the vanishing order of the
filtration and `N` is the number of arrows. Hence one finite inventory of paths carries
every actual decorated ray, and the finite closed endpoint charts of that inventory
exhaust all of them, through chambers whose modules and degree types may differ.

The estimate ranks the segments of a ray by the accumulated marks of its history; a
rank that is constant along a run of segments forces the run to be straight, and a
straight run meets each hyperplane at most once. All encounters stay recorded, including
those between equal degrees and those that leave the spatial direction unchanged. The
charts retain the entire encounter path, complete degree history and incoming tail, and
the closed extensions add only limits of valid endpoints; admissibility of boundary
paths is not asserted.

We combine `exists_pathDecoratedFamily_closedCharts` with
`Convex.encounter_count_le_of_antitone_rank`, ranking by `Quiver.Path.Degrees.reverseRanks`.
The finiteness mechanism is the straight-piece argument of Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, Proposition 3.5 and
Lemma 3.7 (arXiv:1601.07081v4); the closed charts follow Carl–Pumperla–Siebert,
*A tropical view on Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

open Set Quiver Mei.Convex

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

namespace PathDecoratedRay

variable {T ℳ i₀ x v ν ε c P W S C} {p : Path a b} {X : V}
  (F : ∀ q, ModuleFiltration R (M q)) (mark : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)

/-- A nilpotent component filtration bounds the encounters of every actual decorated ray
along a quiver path by the product of its vanishing order and the number of arrows. The
filtrations of different chamber modules are unrelated, and components with zero mark
need only preserve the spatial direction. -/
theorem length_le_of_filtration [Finite (Σ b c : Q, b ⟶ c)]
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X)
    (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
    (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), mark e i j = 0 → v b i = v c j)
    {n : ℕ} (hn : (F b).submodule n = ⊥) :
    p.length ≤ n * Nat.card (Σ b c : Q, b ⟶ c) := by
  obtain ⟨d, β⟩ := r
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

section Finite

variable [Finite Q] [∀ b c : Q, Finite (b ⟶ c)]
  (F : ∀ q, ModuleFiltration R (M q)) (mark : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)
  (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
  (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i : ι b) (j : ι c), mark e i j = 0 → v b i = v c j)
  {n : ℕ} (hn : (F b).submodule n = ⊥)

include hT hstraight hn in
/-- A nilpotent component filtration makes the unrestricted fiber of actual decorated
rays over all encounter paths finite. Degrees and arrows may recur along a path. -/
theorem finite_pathDecoratedRays_of_filtration (X : V) :
    Finite (Σ p : Path a b, PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X) := by
  have hfin (N : ℕ) : Finite (Path.BoundedPaths a b N) :=
    TauCeti.Quiver.finite_boundedPaths N a b
  refine Finite.of_injective (β := Σ p : Path.BoundedPaths a b
    (n * Nat.card (Σ b c : Q, b ⟶ c)), PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X)
    (fun z => ⟨⟨z.1, z.2.length_le_of_filtration F mark hT hstraight hn⟩, z.2⟩) ?_
  rintro ⟨p, r⟩ ⟨q, s⟩ hrs
  obtain rfl : p = q := congrArg (fun z => z.1.val) hrs
  exact congrArg (Sigma.mk p) (eq_of_heq (Sigma.mk.inj hrs).2)

end Finite

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : ∀ q, ι q → Λ) [Finite J] [Finite K]
  (hν : ∀ {b c : Q} (e : b ⟶ c), Toric.IsRationalFunctional h (ν e).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)
  [Finite Q] [∀ b c : Q, Finite (b ⟶ c)]
  (F : ∀ q, ModuleFiltration R (M q)) (mark : ∀ {b c : Q}, (b ⟶ c) → ι b → ι c → ℕ)
  (hT : ComponentTransfersRaise (T := T) (ℳ := ℳ) (F := F) (w := mark))
  (hstraight : ∀ {b c : Q} (e : b ⟶ c) (i' : ι b) (j : ι c),
    mark e i' j = 0 → i (w b i') = i (w c j))
  {n : ℕ} (hn : (F b).submodule n = ⊥) (s : Finset (Path a b))
  (hs : ∀ p : Path a b, p.length ≤ n * Nat.card (Σ b c : Q, b ⟶ c) → p ∈ s)

local notation "vel" => fun q d => i (w q d)
local notation "Labels" => PathDecoratedType T ℳ i₀ x s vel ν ε
local notation "dirs" => (fun t : Labels => Path.Degrees.reverseVertexLabels vel i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t)))
local notation "D" => (fun t : Labels => admissibleBackwardDomain
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C)
local notation "path" => (fun t : Labels => backwardPath
  (Path.reverseArrowLabels ν (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels c (Subtype.val (Sigma.fst t))) (dirs t))

include hν hP hW hS hC hT hstraight hn hs in
/-- A nilpotent component filtration gives finite closed endpoint charts exhausting every
actual decorated ray through every encounter path, with no assumed bound on the number of
encounters: it suffices that the finite inventory `s` contain the paths of length at most
`n * N`. The relative interiors are in bijection with all actual rays and retain their
endpoints, encounter paths, complete degree histories and final whole decorations. The
chart closures add only limits of valid endpoints, with proper endpoint inclusions;
admissibility of boundary paths and the classification of the degenerations are
separate. -/
theorem exists_pathDecoratedRay_closedCharts_of_filtration :
    ∃ (κ : Labels → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
      (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
        IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
        A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
        IsProperMap (fun X : A t j => (path t) X.val) ∧
        ∀ X ∈ A t j, (path t) X 0 = X ∧
          (∀ᶠ r : ℝ in Filter.atBot, (path t) X r ∈ C) ∧
          (i (w a i₀) ≠ 0 → IsProperMap (fun r : Iic (0 : ℝ) => (path t) X r))) ∧
      (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
        (intrinsicInterior ℝ (A t k))) ∧
      (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
      ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃
          (Σ X, Σ p : Path a b, PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X),
        (∀ z, (E z).1 = z.2.2.val) ∧
          ∀ z, (⟨(E z).2.1, (E z).2.2.1.val⟩ : Σ p : Path a b, p.Degrees ι) =
            ⟨z.1.1.val, z.1.2.val⟩ := by
  classical
  obtain ⟨κ, hκ, A, hA, hdisj, hcover, E, hE₁, hE₂⟩ :=
    exists_pathDecoratedFamily_closedCharts T ℳ i₀ x s ν ε c P W S C h w hν hP hW hS hC
  have hbound (X : V) (p : Path a b) (r : PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X) :
      p ∈ s :=
    hs p (r.length_le_of_filtration F mark hT hstraight hn)
  let G (X : V) : (Σ p : (s : Type _), PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p.val X) ≃
      (Σ p : Path a b, PathDecoratedRay T ℳ i₀ x vel ν ε c P W S C p X) :=
    Equiv.ofBijective (fun z => ⟨z.1.val, z.2⟩) ⟨by
      rintro ⟨⟨p, hp⟩, r⟩ ⟨⟨q, hq⟩, r'⟩ hrr
      obtain rfl : p = q := congrArg Sigma.fst hrr
      exact congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj hrr).2), fun z =>
        ⟨⟨⟨z.1, hbound X z.1 z.2⟩, z.2⟩, rfl⟩⟩
  refine ⟨κ, hκ, A, hA, hdisj, hcover, E.trans (Equiv.sigmaCongrRight G), hE₁, fun z => ?_⟩
  exact congrArg (fun t : Labels => (⟨t.1.val, t.2.val⟩ : Σ p : Path a b, p.Degrees ι))
    (hE₂ z)

end Rational

end Mei
