/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Basic
public import Mei.Geometry.Convex.Sweep.Finiteness
public import Mei.LinearAlgebra.GradedModule.History.Path.Decorations
public import Mei.Algebra.Lie.Graded.Shifted.Support

/-!
# Encounter bounds for path rays from positive degree cutoffs

Consider decorated rays along the paths of the one-object quiver on an encounter alphabet
`J`, with one chamber module graded by a group of positive degrees. Suppose every nonzero
homogeneous coefficient has a degree in the cutoff `d.cutoff k`, and every nonzero
component of a propagation map raises degree in the positive monoid. Then the degrees and
labels of the encounters of every actual ray form a realized degree itinerary, so the
number of encounters is at most `Nat.card (d.cutoff k) * Nat.card J`, uniformly in the
endpoint and the coefficient history. Unchanged-degree encounters are counted.

Finite shifted BCH actions satisfy both conditions, by
`PositiveDegrees.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero` and
`PositiveDegrees.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero`. This is the
finite-type argument of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Proposition 2.13 (arXiv:1503.06183v5), for path rays.
-/

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open Set Quiver Mei.Convex

namespace Mei

section SingleObj

variable {R M Γ V J K I : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] {d : PositiveDegrees Γ}
  {ℳ : Γ → Submodule R M} [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : J → Module.End R M} {a : ℳ 0} {v : Γ → V}
  {f : J → V →L[ℝ] ℝ} {c : J → ℝ} {ε : J → SignType}
  {P : J → Set V} {W : I → Set V} {S : K → Set V} {C : Set V}

local notation "PRay" => PathDecoratedRay (Q := SingleObj J) (M := fun _ => M)
  (ι := fun _ => Γ) (fun e => T e) (fun _ => ℳ) 0 a (fun _ => v) (fun e => f e)
  (fun e => ε e) (fun e => c e) (fun e => P e) W S C
local notation "Paths" => Path (SingleObj.star J) (SingleObj.star J)

variable (k : ℕ) (hcut : ∀ n (y : M), y ∈ ℳ n → y ≠ 0 → n ∈ d.cutoff k)
  (hshift : ∀ j n m (y : M), y ∈ ℳ n →
    (DirectSum.decompose ℳ (T j y) m : M) ≠ 0 → m - n ∈ d.monoid)

include hcut hshift

/-- The outgoing degrees and labels of the encounters of an actual ray form a realized
degree itinerary at the cutoff. -/
theorem PathDecoratedRay.degreeItinerary_mem {p : Paths} {X : V} (r : PRay p X) :
    List.ofFn (fun j : Fin p.length =>
      (Path.Degrees.reverseVertexLabels (fun _ n => n) (0 : Γ) p r.1.val j.castSucc,
        p.reverseArrowLabels (fun e => (e : J)) j)) ∈ realizedDegreeItineraries d f c v k := by
  obtain ⟨⟨dd, hdd⟩, g⟩ := r
  have hne := ((mem_pathDecoratedHistorySupport ..).mp hdd).1
  set deg := Path.Degrees.reverseVertexLabels (fun _ n => n) (0 : Γ) p dd with hdeg
  have hf : p.reverseArrowLabels (fun e => f e) = f ∘ p.reverseArrowLabels (fun e => (e : J)) :=
    Path.reverseArrowLabels_comp (fun e => (e : J)) f p
  have hc : p.reverseArrowLabels (fun e => c e) = c ∘ p.reverseArrowLabels (fun e => (e : J)) :=
    Path.reverseArrowLabels_comp (fun e => (e : J)) c p
  have hT : p.reverseArrowLabels (fun e => T e) = T ∘ p.reverseArrowLabels (fun e => (e : J)) :=
    Path.reverseArrowLabels_comp (fun e => (e : J)) T p
  have hv : Path.Degrees.reverseVertexLabels (fun _ => v) (0 : Γ) p dd = v ∘ deg :=
    Path.Degrees.reverseVertexLabels_comp (fun _ n => n) v 0 p dd
  have hdec := p.reverseHomogeneousDecorations_ne_zero (fun e => T e) ℳ 0 dd hne
  have hmem := p.reverseHomogeneousDecorations_mem (fun e => T e) ℳ 0 a.property dd
  obtain ⟨hpos, -, -⟩ := g.eq_backwardRay
  refine mem_realizedDegreeItineraries_ofFn d f c v k _
    (fun j => ⟨hcut _ _ (hmem j.castSucc) (hdec j.castSucc), ?_⟩) (fun i j hij => ?_) X ?_
  · have ht := g.transverse j
    rw [hf, hv] at ht
    exact ht
  · have hne' : Mei.homogeneousHistory ℳ (p.reverseArrowLabels (fun e => T e))
        (Fin.init deg) (a : M) ≠ 0 := by
      rw [← Path.homogeneousHistory_eq_reverseLabels]
      exact hne
    have h := Mei.homogeneousHistory_snoc_sub_mem_of_le d.monoid
      (p.reverseArrowLabels (fun e => T e))
      (fun j n m y hy hq => hshift (p.reverseArrowLabels (fun e => (e : J)) j) n m y hy
        (fun h => hq (Subtype.ext (by
          simpa only [hT, Function.comp_apply, ZeroMemClass.coe_zero] using h))))
      (Fin.init deg) 0 a hne' i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij)
    simpa only [Fin.snoc_castSucc, Fin.init] using h
  · intro j
    have h := hpos j
    rw [hf, hc, hv] at h
    exact h

/-- Every actual ray has at most one encounter for each pair of a cutoff degree and a
label, uniformly in the endpoint and the coefficient history. Unchanged-degree
encounters are counted. -/
theorem PathDecoratedRay.length_le_card_cutoff [Finite J] {p : Paths} {X : V} (r : PRay p X) :
    p.length ≤ Nat.card (d.cutoff k) * Nat.card J := by
  simpa only [List.length_ofFn] using
    length_le_card_of_mem_realizedDegreeItineraries d f c v (r.degreeItinerary_mem k hcut hshift)

end SingleObj

namespace PositiveDegrees

open TauCeti.PositiveDegrees

variable {Γ : Type} {R L M V J K I : Type*}
  [AddCommGroup Γ] [DecidableEq Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (ℳ : Γ → Submodule R M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [DirectSum.Decomposition ℳ]
  [SetLike.GradedBracket ℒ ℳ] (p : Γ) (k : ℕ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "F" => d.shiftedLieFiltration ℒ ℳ p

variable (g : J → d.truncatedGroup ℒ k) (a : (d.shiftedQuotientGrading ℳ p k).piece 0)
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P : J → Set V) (W : I → Set V) (S : K → Set V) (C : Set V)

/-- Every actual BCH-decorated ray along a path of the one-object quiver on the encounter
alphabet obeys the same uniform bound on its number of arrows, including encounters that
preserve degree. -/
theorem _root_.TauCeti.PositiveDegrees.pathDecoratedRay_shiftedBCH_length_le [Finite J]
    {q : Path (SingleObj.star J) (SingleObj.star J)} {Q : V}
    (r : PathDecoratedRay (Q := SingleObj J) (M := fun _ => (F).quotient k)
      (ι := fun _ => Γ) (fun e => ((F).truncatedBCHAction d ℒ k (g e)).toLinearMap)
      (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a (fun _ => v) (fun e => f e)
      (fun e => ε e) (fun e => c e) (fun e => P e) W S C q Q) :
    q.length ≤ Nat.card (d.cutoff k) * Nat.card J :=
  r.length_le_card_cutoff k
    (fun _ _ hy hne => d.mem_cutoff_of_mem_shiftedQuotientGrading_ne_zero ℳ p hy hne)
    (fun e _ _ _ hy hne => d.sub_mem_monoid_of_decompose_shiftedBCHAction_ne_zero ℒ ℳ p k (g e)
      hy fun hz => hne (congrArg Subtype.val hz))

end PositiveDegrees

end Mei
