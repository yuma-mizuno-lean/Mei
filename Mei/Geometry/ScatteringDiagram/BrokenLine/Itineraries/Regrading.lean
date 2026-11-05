/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Coefficient.Embedding

/-!
# Regrading all cutoff encounter itineraries

An injective additive degree map identifies surviving coefficient histories over
all finite encounter words. Only membership in the two chosen cutoffs and in the
positive monoids must agree on the degree map's image. The target grading may
have other degrees; every actual target history still lifts by coefficient
naturality. No finite ambient grading or assumed encounter bound is used.

The comparison retains the complete path, incoming tail, encounter parameters
and every whole-component segment decoration. Weighted cutoff evaluations commute
with the coefficient map, even when some source decorations vanish.

The whole-component decoration and encounter comparison follow
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Definitions 3.1–3.3 (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 and
Proposition 2.13 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei

open Mei.Convex

variable {R M N Γ Δ V J K : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommGroup Δ] [DecidableEq Δ]
  (d : PositiveDegrees Γ) (e : PositiveDegrees Δ)
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (𝓝 : Δ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (r : M →ₗ[R] N) (σ : Γ →+ Δ) (hσ : Function.Injective σ)
  (hr : ∀ p x, x ∈ ℳ p → r x ∈ 𝓝 (σ p))
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : J → Module.End R M) (U : J → Module.End R N)
  (hT : ∀ j, r.comp (T j) = (U j).comp r)
  (a : ℳ 0) (v : Γ → V) (w : Δ → V) (hv : ∀ p, v p = w (σ p))
  (f : J → V →L[ℝ] ℝ) (c : J → ℝ) (ε : J → SignType)
  (P W : J → Set V) (S : K → Set V) (C : Set V)
  (k l : ℕ) (hcut : ∀ p, p ∈ d.cutoff k ↔ σ p ∈ e.cutoff l)
  (hpos : ∀ p, p ∈ d.monoid ↔ σ p ∈ e.monoid) (Q : V)

/-- The regraded incoming coefficient, placed in degree zero using `map_zero`. -/
def regradeBase : 𝓝 0 :=
  ⟨r a, by simpa only [map_zero] using hr 0 a a.property⟩

omit [DecidableEq Γ] [DecidableEq Δ]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝓝] in
/-- Regrading the incoming coefficient does not change its underlying value. -/
@[simp]
theorem coe_regradeBase : (regradeBase ℳ 𝓝 r σ hr a : N) = r a := (rfl)

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] in
/-- For identity degree transport, the regraded base is the ordinary coefficient image. -/
@[simp]
theorem regradeBase_id (𝓟 : Γ → Submodule R N)
    (hr' : ∀ p x, x ∈ ℳ p → r x ∈ 𝓟 p) :
    regradeBase ℳ 𝓟 r (AddMonoidHom.id Γ) hr' a =
      (⟨r a, hr' 0 a a.property⟩ : 𝓟 0) :=
  Subtype.ext (coe_regradeBase ℳ 𝓟 r (AddMonoidHom.id Γ) hr' a)

local notation "a'" => regradeBase ℳ 𝓝 r σ hr a
local notation "Source" => CutoffDecoratedRay d ℳ T a v f c ε P W S C k Q
local notation "Target" => CutoffDecoratedRay e 𝓝 U a' w f c ε P W S C l Q

private def wordIncomingEquiv (word : List J) (p q : Δ) (b : 𝓝 p) (b' : 𝓝 q)
    (h : p = q) (hb : (b : N) = b') :
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) p b w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q ≃
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) q b' w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q := by
  -- Only the incoming degree and its subtype witness change; all ray data stay fixed.
  refine Equiv.cast ?_
  cases h
  exact congrArg (fun b => DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) p b w
    (fun j => f (word.get j)) (fun j => c (word.get j))
    (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q) (Subtype.ext hb)

omit [AddCommGroup Δ] in
private theorem wordIncomingEquiv_properties (word : List J) (p q : Δ)
    (b : 𝓝 p) (b' : 𝓝 q) (h : p = q) (hb : (b : N) = b') (β) :
    let γ := wordIncomingEquiv 𝓝 U w f c ε P W S C Q word p q b b' h hb β
    γ.1.val = β.1.val ∧ γ.2.ray = β.2.ray ∧ γ.2.parameter = β.2.parameter ∧
      γ.decoration = β.decoration := by
  cases h
  cases Subtype.ext hb
  exact ⟨rfl, rfl, rfl, rfl⟩

include hσ hT hv in
private def wordCoefficientEquiv (word : List J) :
    {β : DecoratedAdmissibleRay ℳ (fun j => T (word.get j)) 0 a v
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q //
      r (β.decoration 0) ≠ 0} ≃
    DecoratedAdmissibleRay 𝓝 (fun j => U (word.get j)) 0 a' w
      (fun j => f (word.get j)) (fun j => c (word.get j))
      (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q :=
  (decoratedRayCoefficientEquiv ℳ 𝓝 r σ hr hσ (fun j => T (word.get j))
    (fun j => U (word.get j)) (fun j => hT (word.get j)) 0 a v w hv
    (fun j => f (word.get j)) (fun j => c (word.get j))
    (fun j => ε (word.get j)) (fun j => P (word.get j)) W S C Q).trans
      (wordIncomingEquiv 𝓝 U w f c ε P W S C Q word (σ 0) 0
        ⟨r a, hr 0 a a.property⟩ a' σ.map_zero (coe_regradeBase ℳ 𝓝 r σ hr a).symm)

private theorem wordCoefficientEquiv_history (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).1.val =
      σ ∘ β.val.1.val := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).1]
  exact decoratedRayCoefficientEquiv_history ..

private theorem wordCoefficientEquiv_ray (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).2.ray =
      β.val.2.ray := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).2.1]
  exact decoratedRayCoefficientEquiv_ray ..

private theorem wordCoefficientEquiv_parameter (word : List J) (β) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).2.parameter =
      β.val.2.parameter := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    (wordIncomingEquiv_properties ..).2.2.1]
  exact decoratedRayCoefficientEquiv_parameter ..

private theorem wordCoefficientEquiv_decoration (word : List J) (β) (j) :
    (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C Q word β).decoration j =
      r (β.val.decoration j) := by
  rw [wordCoefficientEquiv, Equiv.trans_apply,
    congrFun (wordIncomingEquiv_properties ..).2.2.2 j]
  exact decoratedRayCoefficientEquiv_decoration ..

/-- Regrade a surviving cutoff ray, keeping its encounter word and complete geometry. -/
def cutoffDecoratedRayRegradingMap (β : {β : Source // r β.decoration ≠ 0}) : Target where
  itinerary := β.val.itinerary
  realization := wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C Q β.val.itinerary ⟨β.val.realization, by
      simpa only [CutoffDecoratedRay.decoration_eq, DecoratedAdmissibleRay.decoration_zero]
        using β.property⟩
  degree_mem j := by
    rw [wordCoefficientEquiv_history]
    exact (hcut _).mp (β.val.degree_mem j)
  degree_sub_mem i j hij := by
    rw [wordCoefficientEquiv_history]
    simpa only [Function.comp_apply, ← map_sub] using
      (hpos _).mp (β.val.degree_sub_mem i j hij)

/-- Every recorded encounter, including unchanged-degree encounters, is retained. -/
@[simp]
theorem cutoffDecoratedRayRegradingMap_itinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C
      k l hcut hpos Q β).itinerary = β.val.itinerary := (rfl)

/-- Every segment degree is regraded, retaining shifts of zero spatial direction. -/
@[simp]
theorem cutoffDecoratedRayRegradingMap_history
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.1.val (σ ∘ β.val.realization.1.val) :=
  heq_of_eq (wordCoefficientEquiv_history ..)

/-- The entire degree-labelled encounter word is reindexed without omitting encounters. -/
@[simp]
theorem cutoffDecoratedRayRegradingMap_degreeItinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).degreeItinerary =
      β.val.degreeItinerary.map (Prod.map σ id) := by
  simp only [CutoffDecoratedRay.degreeItinerary_eq, List.map_ofFn]
  rw [eq_of_heq (cutoffDecoratedRayRegradingMap_history d e ℳ 𝓝 r σ hσ hr
    T U hT a v w hv f c ε P W S C k l hcut hpos Q β)]
  -- The explicit `itinerary` field is unchanged; both functions form `(σ (p j), word[j])`.
  rfl

/-- Regrading preserves the entire affine path, including the incoming tail. -/
@[simp]
theorem cutoffDecoratedRayRegradingMap_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.ray = β.val.realization.2.ray :=
  wordCoefficientEquiv_ray ..

/-- Every encounter parameter is preserved across the full cutoff family. -/
@[simp]
theorem cutoffDecoratedRayRegradingMap_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.parameter β.val.realization.2.parameter :=
  heq_of_eq (wordCoefficientEquiv_parameter ..)

/-- The whole coefficient on every segment specializes by the coefficient map. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingMap_segmentDecorations
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.decoration
      (fun j => r (β.val.realization.decoration j)) :=
  heq_of_eq (funext (fun _j => wordCoefficientEquiv_decoration ..))

/-- The final whole decoration specializes without discarding retained encounters. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingMap_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).decoration = r β.val.decoration := by
  have hh := eq_of_heq
    (cutoffDecoratedRayRegradingMap_history d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β)
  rw [CutoffDecoratedRay.decoration_eq, CutoffDecoratedRay.decoration_eq, hh]
  exact (map_homogeneousHistory_of_injective ℳ 𝓝 r σ hr hσ
    (fun j => T (β.val.itinerary.get j)) (fun j => U (β.val.itinerary.get j))
    (fun j => hT (β.val.itinerary.get j)) β.val.realization.1.val a).symm

/-- An injective degree map separates surviving cutoff rays. -/
theorem cutoffDecoratedRayRegradingMap_injective : Function.Injective
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q) := by
  rintro ⟨⟨word, β, hβ, hmβ⟩, hb⟩ ⟨⟨word', γ, hγ, hmγ⟩, hc⟩ h
  have hw := congrArg CutoffDecoratedRay.itinerary h
  simp only [cutoffDecoratedRayRegradingMap_itinerary] at hw
  -- Unfold the itinerary projection of the two explicit cutoff-ray constructors.
  change word = word' at hw
  subst word'
  apply Subtype.ext
  apply CutoffDecoratedRay.ext
  · rfl
  have hg := congrArg (fun z : Target => z.degreeItinerary) h
  rw [cutoffDecoratedRayRegradingMap_degreeItinerary,
    cutoffDecoratedRayRegradingMap_degreeItinerary] at hg
  simp only [CutoffDecoratedRay.degreeItinerary_eq, List.map_ofFn] at hg
  have hh : σ ∘ β.1.val = σ ∘ γ.1.val := by
    have he := List.ofFn_injective hg
    exact funext fun j => congrArg Prod.fst (congrFun he j)
  exact heq_of_eq (DecoratedAdmissibleRay.ext_history
    (funext fun j => hσ (congrFun hh j)))

private theorem wordCoefficientEquiv_symm_history (word : List J) (β) :
    σ ∘ ((wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C Q word).symm β).val.1.val = β.1.val := by
  have hh := wordCoefficientEquiv_history ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C Q word ((wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C Q word).symm β)
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- Package a lifted word-specific realization using cutoff and positive-monoid reflection. -/
private def liftCutoffRay (β : Target)
    (α : DecoratedAdmissibleRay ℳ (fun j => T (β.itinerary.get j)) 0 a v
      (fun j => f (β.itinerary.get j)) (fun j => c (β.itinerary.get j))
      (fun j => ε (β.itinerary.get j)) (fun j => P (β.itinerary.get j)) W S C Q)
    (hh : σ ∘ α.1.val = β.realization.1.val) : Source where
  itinerary := β.itinerary
  realization := α
  degree_mem j := (hcut _).mpr
    ((congrArg (fun q => q ∈ e.cutoff l) (congrFun hh j)).mpr (β.degree_mem j))
  degree_sub_mem i j hij := (hpos _).mpr (by
    have hs : σ (α.1.val i - α.1.val j) =
        β.realization.1.val i - β.realization.1.val j :=
      (map_sub σ _ _).trans (congrArg₂ (· - ·) (congrFun hh i) (congrFun hh j))
    exact (congrArg (fun q => q ∈ e.monoid) hs).mpr (β.degree_sub_mem i j hij))

/-- Every target cutoff ray lifts through the word-specific coefficient equivalence. -/
theorem cutoffDecoratedRayRegradingMap_surjective : Function.Surjective
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q) := by
  intro β
  let α := (wordCoefficientEquiv ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C Q β.itinerary).symm β.realization
  have hh : σ ∘ α.val.1.val = β.realization.1.val := wordCoefficientEquiv_symm_history ..
  let γ : Source := liftCutoffRay d e ℳ 𝓝 r σ hr T U a v w f c ε P W S C
    k l hcut hpos Q β α.val hh
  refine ⟨⟨γ, by
    simpa only [γ, liftCutoffRay, CutoffDecoratedRay.decoration_eq,
      DecoratedAdmissibleRay.decoration_zero] using α.property⟩, ?_⟩
  apply CutoffDecoratedRay.degreeItinerary_injective
  rw [cutoffDecoratedRayRegradingMap_degreeItinerary]
  simp only [CutoffDecoratedRay.degreeItinerary_eq, List.map_ofFn]
  -- The lifted constructor keeps the target word; unfold it and `Prod.map` on each pair.
  change List.ofFn (fun j => (σ (α.val.1.val j), β.itinerary.get j)) =
    List.ofFn (fun j => (β.realization.1.val j, β.itinerary.get j))
  exact congrArg List.ofFn (funext fun j => Prod.ext (congrFun hh j) rfl)

/-- The regrading map is bijective on source rays whose final coefficient survives. -/
theorem cutoffDecoratedRayRegradingMap_bijective : Function.Bijective
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q) :=
  ⟨cutoffDecoratedRayRegradingMap_injective d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q,
    cutoffDecoratedRayRegradingMap_surjective d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q⟩

/-- Over all encounter words, regrading identifies exactly the source rays whose
final coefficient survives with the target cutoff ray family. -/
def cutoffDecoratedRayRegradingEquiv : {β : Source // r β.decoration ≠ 0} ≃ Target :=
  Equiv.ofBijective
    (cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q)
    (cutoffDecoratedRayRegradingMap_bijective d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q)

/-- The all-itinerary equivalence applies the named forward regrading map. -/
theorem cutoffDecoratedRayRegradingEquiv_apply
    (β : {β : Source // r β.decoration ≠ 0}) :
    cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β =
    cutoffDecoratedRayRegradingMap d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β := by
  exact Equiv.ofBijective_apply _ _ β

/-- Every recorded encounter, including unchanged-degree encounters, is retained. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_itinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv f c ε P W S C
      k l hcut hpos Q β).itinerary = β.val.itinerary := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_itinerary d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- Every segment degree is regraded, retaining shifts of zero spatial direction. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_history
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.1.val (σ ∘ β.val.realization.1.val) := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_history d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- The entire degree-labelled encounter word is reindexed without omitting encounters. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_degreeItinerary
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).degreeItinerary =
      β.val.degreeItinerary.map (Prod.map σ id) := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_degreeItinerary d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- Regrading preserves the entire affine path, including the incoming tail. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_ray
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.ray = β.val.realization.2.ray := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_ray d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- Every encounter parameter is preserved across the full cutoff family. -/
@[simp]
theorem cutoffDecoratedRayRegradingEquiv_parameter
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.2.parameter β.val.realization.2.parameter := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_parameter d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- The whole coefficient on every segment specializes by the coefficient map. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEquiv_segmentDecorations
    (β : {β : Source // r β.decoration ≠ 0}) :
    HEq (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).realization.decoration
      (fun j => r (β.val.realization.decoration j)) := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_segmentDecorations d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- The final whole decoration specializes without discarding retained encounters. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEquiv_decoration
    (β : {β : Source // r β.decoration ≠ 0}) :
    (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q β).decoration = r β.val.decoration := by
  rw [cutoffDecoratedRayRegradingEquiv_apply]
  exact cutoffDecoratedRayRegradingMap_decoration d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q β

/-- An injective coefficient map preserves every source ray at corresponding
cutoffs, including all unchanged-degree and zero-direction encounters. -/
def cutoffDecoratedRayRegradingEmbeddingEquiv (hinj : Function.Injective r) : Source ≃ Target :=
  (Equiv.subtypeUnivEquiv fun β => fun hz => β.decoration_ne_zero
    (hinj (by simpa only [map_zero] using hz))).symm.trans
      (cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
        f c ε P W S C k l hcut hpos Q)

/-- Injective coefficient transport retains every recorded encounter. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_itinerary
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).itinerary = β.itinerary := by
  simp only [cutoffDecoratedRayRegradingEmbeddingEquiv, Equiv.trans_apply,
    Equiv.subtypeUnivEquiv_symm_apply, cutoffDecoratedRayRegradingEquiv_itinerary]

/-- Injective coefficient transport regrades the complete segment history. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_history
    (hinj : Function.Injective r) (β : Source) :
    HEq (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.1.val
      (σ ∘ β.realization.1.val) :=
  cutoffDecoratedRayRegradingEquiv_history d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport maps the final whole decoration. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_decoration
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).decoration = r β.decoration := by
  simp only [cutoffDecoratedRayRegradingEmbeddingEquiv, Equiv.trans_apply,
    Equiv.subtypeUnivEquiv_symm_apply, cutoffDecoratedRayRegradingEquiv_decoration]

/-- With injective coefficients the full degree-labelled encounter word is retained. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_degreeItinerary
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).degreeItinerary =
      β.degreeItinerary.map (Prod.map σ id) := by
  simp only [cutoffDecoratedRayRegradingEmbeddingEquiv, Equiv.trans_apply,
    Equiv.subtypeUnivEquiv_symm_apply, cutoffDecoratedRayRegradingEquiv_degreeItinerary]

/-- Injective coefficient transport preserves the complete ray and incoming tail. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_ray
    (hinj : Function.Injective r) (β : Source) :
    (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.2.ray = β.realization.2.ray :=
  cutoffDecoratedRayRegradingEquiv_ray d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport preserves every encounter parameter. -/
@[simp]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_parameter
    (hinj : Function.Injective r) (β : Source) :
    HEq (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.2.parameter β.realization.2.parameter :=
  cutoffDecoratedRayRegradingEquiv_parameter d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

/-- Injective coefficient transport maps all whole-component segment decorations. -/
@[simp↓]
theorem cutoffDecoratedRayRegradingEmbeddingEquiv_segmentDecorations
    (hinj : Function.Injective r) (β : Source) :
    HEq (cutoffDecoratedRayRegradingEmbeddingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q hinj β).realization.decoration
      (fun j => r (β.realization.decoration j)) :=
  cutoffDecoratedRayRegradingEquiv_segmentDecorations d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q _

include hσ hT hv hcut hpos in
/-- Weighted evaluation across all finite encounter words commutes with
regrading and coefficient change. Source coefficients which vanish contribute zero. -/
theorem map_cutoffDecoratedEvaluation_regrading [Finite J] :
    r (cutoffDecoratedEvaluation d ℳ T a v f c ε P W S C k Q) =
      cutoffDecoratedEvaluation e 𝓝 U a' w f c ε P W S C l Q := by
  classical
  let := Fintype.ofFinite Source
  let := Fintype.ofFinite Target
  let E := cutoffDecoratedRayRegradingEquiv d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
    f c ε P W S C k l hcut hpos Q
  simp only [cutoffDecoratedEvaluation_def, map_sum]
  refine Finset.sum_bij_ne_zero (fun β _ hβ => E ⟨β, hβ⟩) (by simp) ?_ ?_ ?_
  · intro β _ hβ γ _ hγ he
    exact congrArg Subtype.val (E.injective he)
  · intro β _ _
    exact ⟨(E.symm β).val, Finset.mem_univ _, (E.symm β).property, E.apply_symm_apply β⟩
  · intro β _ hβ
    exact (cutoffDecoratedRayRegradingEquiv_decoration d e ℳ 𝓝 r σ hσ hr T U hT a v w hv
      f c ε P W S C k l hcut hpos Q ⟨β, hβ⟩).symm

end Mei
