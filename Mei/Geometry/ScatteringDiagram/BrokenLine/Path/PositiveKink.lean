/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Bounded
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Filtration.Mixed
public import Mei.LinearAlgebra.GradedModule.History.Path.Decorations

/-!
# Finite ray fibers for mixed function walls and positive-kink slabs

In monoid chamber coordinates, an ordinary function wall congruent to one
modulo a nilpotent coefficient ideal raises order on every changed component.
A transverse admissible slab crossing raises order by its positive incoming
normal weight. Applying the mixed encounter bound to the actual intermediate
whole decorations gives a uniform length bound on all quiver-path rays.
Consequently all paths, rather than a prescribed finite inventory, give finite
endpoint fibers. The bound is independent of the incoming coefficient.

The chamber velocity maps may differ across slabs. At ordinary walls they
agree. Each slab uses its inward normal coordinate, so its permitted crossing
has sign one; positive rescaling of that normal is allowed. Selected supports,
singular avoidance and admission of the whole incoming tail remain those of
`PathDecoratedRay`.

We apply `AdmissibleRayRealization.encounter_count_le_of_functionWalls_and_slabs`
and the bounded-path family construction. The positive-kink finiteness argument
is Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, Proposition 3.5 and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver AddMonoidAlgebra Mei.GradedAlgebra Mei.NodeAlgebra

namespace Mei

variable {Q R M V J₀ J₁ K O : Type*} [Quiver Q] [CommRing R]
  [AddCommMonoid M] [DecidableEq M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J₀] [Finite J₁]
  (𝒜 : J₀ → ℤ → Submodule R R[ℤ × M]) [∀ e, GradedAlgebra (𝒜 e)]
  (θ : ∀ e, (𝒜 e 0)ˣ) (weight : J₀ → ℤ × M → ℤ)
  (slab : J₁ → R[M]) (U : J₁ → Module.End R R[ℤ × M])
  (label : ∀ {b c : Q}, (b ⟶ c) → J₀ ⊕ J₁)
  (I : Ideal R) (v : Q → ℤ × M → V)
  (ν : J₀ ⊕ J₁ → V →L[ℝ] ℝ) (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : J₀ ⊕ J₁ → ℝ) (P : ∀ {b c : Q}, (b ⟶ c) → Set V)
  (W : O → Set V) (S : K → Set V) (C : Set V)

local notation "T" => (fun {b c : Q} (e : b ⟶ c) =>
  Sum.elim (fun j => AlgEquiv.toLinearMap (functionWallAction (𝒜 j) (θ j))) U (label e))
local notation "grades" => (fun _ : Q => grade R : Q → ℤ × M → Submodule R R[ℤ × M])
local notation "normals" => (fun {b c : Q} (e : b ⟶ c) => ν (label e))
local notation "offsets" => (fun {u z : Q} (e : u ⟶ z) => c (label e))

variable (hθ : ∀ e, algebraMap (𝒜 e 0) R[ℤ × M] (θ e) - 1 ∈
    I.map (algebraMap R R[ℤ × M]))
  (hw : ∀ e q, grade R q ≤ 𝒜 e (weight e q))
  (hslab : ∀ e m, (slab e).coeff m ∈ I)
  (hU : ∀ e, U e = (exponentCorrespondence (slab e)).totalTransfer ∨
    U e = (exponentCorrespondence (slab e)).symm.totalTransfer)
  (hcoord : ∀ {b c : Q} (e : b ⟶ c) j, label e = Sum.inl j → ∀ q, v c q = v b q)
  (hnormal : ∀ {b c : Q} (e : b ⟶ c) j, label e = Sum.inr j →
    ∀ q, 0 < ν (Sum.inr j) (v b q) → 0 < q.1)
  (hsign : ∀ {b c : Q} (e : b ⟶ c) j, label e = Sum.inr j → ε e = 1)
  {r : ℕ} (hr : I ^ r = ⊥)

include hθ hw hslab hU hcoord hnormal hsign hr

/-- Every actual ray in common monoid chamber coordinates has uniformly bounded
encounter length. Both slab orientations are allowed; the normal coordinate is
chosen inward at the source chamber of each slab arrow. -/
theorem PathDecoratedRay.length_le_of_functionWalls_and_slabs
    {a b : Q} {i₀ : ℤ × M} {x : grade R i₀} {p : Path a b} {X : V}
    (β : PathDecoratedRay T grades i₀ x v normals ε offsets P W S C p X) :
    p.length ≤ r * (Nat.card J₀ + Nat.card J₁) := by
  let d := β.1.val
  let deg := Path.Degrees.reverseVertexLabels (fun _ q => q) i₀ p d
  let vel := Path.Degrees.reverseVertexLabels (fun q _ => v q) i₀ p d
  let coeff := p.reverseHomogeneousDecorations T (grade R) x d
  have hvel : Path.Degrees.reverseVertexLabels v i₀ p d = fun j => vel j (deg j) :=
    Path.Degrees.reverseVertexLabels_map₂ (fun q _ => v q) (fun _ q => q)
      (fun f q => f q) i₀ p d
  have hnorm := (mem_pathDecoratedHistorySupport T grades i₀ x v normals ε p d).mp
    β.1.property
  -- Transfer the arrowwise coordinate and inward-normal conditions to the
  -- adjacent segments of this complete history.
  have hc := Path.Degrees.reverseLabels_forall label (fun q _ => v q)
    (fun l f g => ∀ j, l = Sum.inl j → ∀ q, f q = g q) (fun e _ _ => hcoord e) i₀ p d
  have hn := Path.Degrees.reverseLabels_forall
    (fun {b c : Q} (e : b ⟶ c) => (label e, ε e))
    (fun q i => (v q, i))
    (fun l _ z => ∀ j, l.1 = Sum.inr j →
      ((0 < ν (Sum.inr j) (z.1 z.2) → 0 < z.2.1) ∧ l.2 = 1))
    (fun e i _ j he => ⟨hnormal e j he i, hsign e j he⟩) i₀ p d
  have htrans (j : Fin p.length) (e : J₁)
      (he : p.reverseArrowLabels label j = Sum.inr e) : 0 < (deg j.succ).1 := by
    have hh := hn j
    simp only [Path.Degrees.reverseVertexLabels_map₂] at hh
    have hfst := congrFun (p.reverseArrowLabels_comp
      (fun {b c : Q} (e : b ⟶ c) => (label e, ε e)) Prod.fst) j
    have hsnd := congrFun (p.reverseArrowLabels_comp
      (fun {b c : Q} (e : b ⟶ c) => (label e, ε e)) Prod.snd) j
    obtain ⟨hheight, hsig⟩ := hh e (hfst.symm.trans he)
    have hs := (hnorm.2 j).1
    have hsign' := (hnorm.2 j).2
    simp only [Path.reverseArrowLabels_comp, Function.comp_apply, hvel] at hs hsign'
    have hpos : 0 < ν (Sum.inr e) (vel j.succ (deg j.succ)) := by
      apply sign_eq_one_iff.mp
      rw [← he, ← hs]
      exact hsign'.trans (hsnd.trans hsig)
    exact hheight hpos
  -- The existing geometric estimate now applies to the actual nonzero
  -- intermediate decorations, with no assumed bound on unmarked runs.
  have hprop := p.reverseHomogeneousDecorations_propagation T (grade R) i₀ x d
  simp only [Path.reverseArrowLabels_comp, Function.comp_apply] at hprop
  have β' : Convex.AdmissibleRayRealization
      (fun j => ν (p.reverseArrowLabels label j))
      (fun j => c (p.reverseArrowLabels label j)) (fun j => vel j (deg j))
      (p.reverseArrowLabels P) W S C X := by
    rw [← hvel]
    simpa only [Path.reverseArrowLabels_comp, Function.comp_def] using β.2
  exact β'.encounter_count_le_of_functionWalls_and_slabs 𝒜 θ weight slab U I
    vel deg coeff
    (p.reverseHomogeneousDecorations_mem T (grade R) i₀ x.property d)
    (p.reverseHomogeneousDecorations_ne_zero T (grade R) d hnorm.1)
    hprop hθ hw hslab hU hc htrans hr

variable [Finite Q] [∀ q q' : Q, Finite (q ⟶ q')]

/-- A nilpotent coefficient ideal makes the fiber of all mixed ordinary-wall
and slab rays finite, without imposing a finite encounter inventory. -/
theorem finite_pathDecoratedRays_of_functionWalls_and_slabs
    {a b : Q} (i₀ : ℤ × M) (x : grade R i₀) (X : V) :
    Finite (Σ p : Path a b,
      PathDecoratedRay T grades i₀ x v normals ε offsets P W S C p X) := by
  apply finite_pathDecoratedRays_of_encounter_bound T grades i₀ x v normals ε
    offsets P W S C (r * (Nat.card J₀ + Nat.card J₁)) X
  intro p β
  exact β.length_le_of_functionWalls_and_slabs 𝒜 θ weight slab U label I v ν ε c
    P W S C hθ hw hslab hU hcoord hnormal hsign hr

section Rational

variable {Λ : Type*} [AddCommGroup Λ] {i : Λ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice i) (w : Q → ℤ × M → Λ)
  (hv : v = fun q d => i (w q d)) [Finite O] [Finite K]
  (hν : ∀ j, Toric.IsRationalFunctional h (ν j).toLinearMap)
  (hP : ∀ {b c : Q} (e : b ⟶ c), IsRationalSemilinear h (P e))
  (hW : ∀ j, IsRationalNormalPolyhedron h (W j))
  (hS : ∀ j, IsRationalNormalPolyhedron h (S j))
  (hC : IsRationalNormalPolyhedron h C)
  {a b : Q} (i₀ : ℤ × M) (x : grade R i₀)

local notation "Types" s:max => PathDecoratedType T grades i₀ x s v normals ε
local notation "dirs" t:max => Path.Degrees.reverseVertexLabels v i₀
  (Subtype.val (Sigma.fst t)) (Subtype.val (Sigma.snd t))
local notation "D" t:max => Convex.admissibleBackwardDomain
  (Path.reverseArrowLabels normals (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels offsets (Subtype.val (Sigma.fst t))) (dirs t)
  (Path.reverseArrowLabels P (Subtype.val (Sigma.fst t))) W S C
local notation "path" t:max => Convex.backwardPath
  (Path.reverseArrowLabels normals (Subtype.val (Sigma.fst t)))
  (Path.reverseArrowLabels offsets (Subtype.val (Sigma.fst t))) (dirs t)
local notation "Rays" X:max => Σ p : Path a b,
  PathDecoratedRay T grades i₀ x v normals ε offsets P W S C p X

include hv hν hP hW hS hC

/-- Positive-kink monoid coordinates give exhaustive finite closed charts for
all actual mixed function-wall and slab rays. The numerical encounter bound is
derived from the nilpotent coefficient ideal. Closed extensions retain the
whole incoming tail and final decoration, without asserting admissibility at
singular or collapsed boundary paths. -/
theorem exists_closedPathDecoratedRayCharts_of_functionWalls_and_slabs :
    ∃ s : Finset (Path a b),
      (∀ X (p : Path a b),
        PathDecoratedRay T grades i₀ x v normals ε offsets P W S C p X → p ∈ s) ∧
      ∃ (κ : Types s → Type) (_ : ∀ t, Finite (κ t)) (A : ∀ t, κ t → Set V),
        (∀ t j, (A t j).Nonempty ∧ IsRationalNormalPolyhedron h (A t j) ∧
          IsLocallyClosedPolyhedron h (intrinsicInterior ℝ (A t j)) ∧
          A t j ⊆ closure (D t) ∧ IsProperMap (fun X : A t j => (X : V)) ∧
          IsProperMap (fun X : A t j => (path t) X.val) ∧
          ∀ X ∈ A t j, (path t) X 0 = X ∧
            (∀ᶠ t' : ℝ in Filter.atBot, (path t) X t' ∈ C) ∧
            (v a i₀ ≠ 0 → IsProperMap (fun t' : Iic (0 : ℝ) => (path t) X t'))) ∧
        (∀ t, Pairwise fun j k => Disjoint (intrinsicInterior ℝ (A t j))
          (intrinsicInterior ℝ (A t k))) ∧
        (∀ t, ⋃ j, intrinsicInterior ℝ (A t j) = D t) ∧
        ∃ E : (Σ t, Σ j : κ t, intrinsicInterior ℝ (A t j)) ≃ (Σ X, Rays X),
          (∀ z, (E z).1 = z.2.2.val) ∧
          (∀ z, (E z).2.1 = z.1.1.val) ∧
          (∀ z, HEq (E z).2.2.1 z.1.2) ∧
          ∀ z, (E z).2.2.decoration = z.1.1.val.homogeneousHistory T grades z.1.2.val x := by
  subst v
  apply exists_exhaustive_pathDecoratedFamily_closedCharts T grades i₀ x normals ε
    offsets P W S C h w (fun e => hν (label e)) hP hW hS hC
    (r * (Nat.card J₀ + Nat.card J₁))
  intro X p β
  exact β.length_le_of_functionWalls_and_slabs 𝒜 θ weight slab U label I
    (fun q d => i (w q d)) ν ε c P W S C hθ hw hslab hU hcoord hnormal hsign hr

end Rational

end Mei
