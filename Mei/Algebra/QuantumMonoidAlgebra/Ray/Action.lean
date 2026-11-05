/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Map
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Action

/-!
# Completed quantum ray automorphisms

A unit scalar series along a positive quantum ray defines an algebra automorphism
of the coefficient completion. Its value on positive monomials is the quantum
rescaling ratio. Simultaneous coefficient and exponent maps intertwine both this
automorphism and its inverse on arbitrary completed coefficients.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
  (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)

local notation "F" => positiveFiltration q β P δ hδ

/-- Unit series on one positive quantum ray form a group of coefficient automorphisms. -/
abbrev completedRayAction (n : P) (hn : 0 < δ n) :
    (PowerSeries R)ˣ →* ((F).completion ≃ₐ[R] (F).completion) :=
  (F).completedSeriesAction (completedRayGenerator q β P δ hδ n hn)

/-- For arbitrary bilinear forms, the ray action uses rescaling exponent `β(n,p) - β(p,n)`. -/
theorem completedRayAction_monomial_skew (n p : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) :
    completedRayAction q β P δ hδ n hn H ((F).toCompletion (positiveMonomial q β P p)) =
      (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (PowerSeries.rescale ((q ^ (β n p - β p n) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R)) := by
  simp only [completedRayAction, AlgFiltration.completedSeriesAction_apply]
  exact completedRay_conj_skew q β P δ hδ n p hn H

/-- Under `β.IsAlt`, the ray action on a monomial uses rescaling exponent `2β(n,p)`. -/
theorem completedRayAction_monomial (hβ : β.IsAlt) (n p : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) :
    completedRayAction q β P δ hδ n hn H ((F).toCompletion (positiveMonomial q β P p)) =
      (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (PowerSeries.rescale ((q ^ (2 * β n p) : Rˣ) : R) (H : PowerSeries R) *
            (↑(H⁻¹) : PowerSeries R)) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    completedRayAction_monomial_skew q β P δ hδ n p hn H

variable {S Γ' : Type*} [CommRing S] [AddCommGroup Γ']
  {q' : Sˣ} {β' : LinearMap.BilinForm ℤ Γ'}
  (φ : R →+* S) (f : Γ →+ Γ')
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (f p) (f r))
  (P' : AddSubmonoid Γ') (hP : ∀ n ∈ P, f n ∈ P')
  (δ' : Γ' →+ ℤ) (hδ' : ∀ p ∈ P', 0 ≤ δ' p)
  (l : ℕ → ℕ) (hl : Monotone l)
  (hcut : ∀ k n, n ∈ P → (l k : ℤ) < δ n → (k : ℤ) < δ' (f n))
  (hpos : ∀ n ∈ P, 0 < δ n → 0 < δ' (f n))

local notation "G" => positiveFiltration q' β' P' δ' hδ'

local notation "Ψ" => mapPositiveCompletionOfDegree φ f h P P' hP δ δ' hδ hδ' l hl hcut

/-- Coefficient and exponent transport intertwines the completed ray automorphisms. -/
theorem mapPositiveCompletionOfDegree_completedRayAction (n : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) (a : (F).completion) :
    Ψ (completedRayAction q β P δ hδ n hn H a) =
      completedRayAction q' β' P' δ' hδ' ⟨f n, hP n n.property⟩ (hpos n n.property hn)
        (Units.map (PowerSeries.map φ).toMonoidHom H) (Ψ a) := by
  have hm (u v : (F).completion) : Ψ (u * v) = Ψ u * Ψ v := map_mul Ψ u v
  simp only [completedRayAction, AlgFiltration.completedSeriesAction_apply, hm,
    Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  simp only [mapPositiveCompletionOfDegree_completedRayAeval φ f h P P' hP δ δ' hδ hδ'
    l hl hcut hpos]

/-- The same transport intertwines inverse ray automorphisms, as used for reverse crossings. -/
theorem mapPositiveCompletionOfDegree_completedRayAction_symm (n : P) (hn : 0 < δ n)
    (H : (PowerSeries R)ˣ) (a : (F).completion) :
    Ψ ((completedRayAction q β P δ hδ n hn H).symm a) =
      (completedRayAction q' β' P' δ' hδ' ⟨f n, hP n n.property⟩ (hpos n n.property hn)
        (Units.map (PowerSeries.map φ).toMonoidHom H)).symm (Ψ a) := by
  simpa only [completedRayAction, map_inv, AlgEquiv.aut_inv] using
    mapPositiveCompletionOfDegree_completedRayAction q β P δ hδ φ f h P' hP δ' hδ'
      l hl hcut hpos n hn (H⁻¹) a

end Mei.QuantumMonoidAlgebra
