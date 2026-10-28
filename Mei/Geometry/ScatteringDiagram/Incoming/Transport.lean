/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Incoming.Affine

/-!
# Functorial coefficient transport of incoming tails

Compatible degree maps and linear coefficient maps transport one-chart incoming
sources. Their partial maps on admitted tails compose: if an intermediate coefficient
is zero, every subsequent linear image is zero as well. Thus deleting a tail at an
intermediate truncation agrees with deleting it after the composite coefficient map.
The surviving affine representative, and hence its actual incoming germ, is unchanged.

These are the coefficient-map and regrading laws for one-chart incoming sources.
The atlas, common-facet and deck identifications require additional data.
-/

public section

namespace Mei

variable {Γ Γ' Γ'' V R E : Type*}
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommMonoid Γ'']
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [Semiring R] [AddCommMonoid E] [Module R E]
  {M : Γ → Type*} [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  {M' : Γ' → Type*} [∀ p, AddCommMonoid (M' p)] [∀ p, Module R (M' p)]
  {M'' : Γ'' → Type*} [∀ p, AddCommMonoid (M'' p)] [∀ p, Module R (M'' p)]
  {v : Γ →+ V} (T : Γ →+ Γ') (w : Γ' →+ V) (hw : w.comp T = v)
  (ψ : ∀ p, M p →ₗ[R] M' (T p))
  (U : Γ' →+ Γ'') (z : Γ'' →+ V) (hz : z.comp U = w)
  (χ : ∀ p, M' p →ₗ[R] M'' (U p))

namespace AffineIncomingSource

omit [TopologicalSpace V] in
/-- Source transport along identity degree and coefficient maps is the identity. -/
@[simp]
theorem regrade_id (S : AffineIncomingSource R E M v) :
    S.regrade (AddMonoidHom.id Γ) v (by rfl) (fun p => LinearMap.id (R := R) (M := M p)) =
      S := by
  cases S
  rfl

omit [TopologicalSpace V] in
/-- Successive degree and coefficient changes give the composite source. -/
theorem regrade_comp (S : AffineIncomingSource R E M v) :
    (S.regrade T w hw ψ).regrade U z hz χ =
      S.regrade (U.comp T) z (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) := by
  rfl

end AffineIncomingSource

namespace AffineIncomingTail

variable {S : AffineIncomingSource R E M v} {a : E}

/-- The actual incoming germ of a surviving tail is unchanged by coefficient transport. -/
@[simp]
theorem germ_regrade (β : AffineIncomingTail S a)
    (ha : ψ S.degree (S.coefficient a) ≠ 0) :
    (β.regrade T w hw ψ ha).germ = β.germ := by
  rw [germ_eq_ofFun, germ_eq_ofFun]
  apply congrArg (fun f : ℝ → V => Filter.Germ.ofFun f)
  funext t
  exact regrade_apply T w hw ψ β ha t

/-- Identity transport neither deletes nor changes an admitted tail. -/
@[simp]
theorem regrade?_id (β : AffineIncomingTail S a) :
    β.regrade? (AddMonoidHom.id Γ) v (by rfl)
      (fun p => LinearMap.id (R := R) (M := M p)) = some β := by
  apply (regrade?_eq_some_iff (AddMonoidHom.id Γ) v (by rfl)
    (fun p => LinearMap.id (R := R) (M := M p)) β β).mpr
  exact ⟨β.coefficient_ne_zero, rfl⟩

open scoped Classical in
/-- The partial coefficient map deletes exactly zero image coefficients, while its
surviving geometric germ is unchanged. -/
theorem map_germ_regrade? (β : AffineIncomingTail S a) :
    Option.map AffineIncomingTail.germ (β.regrade? T w hw ψ) =
      if ψ S.degree (S.coefficient a) = 0 then none else some β.germ := by
  classical
  by_cases h : ψ S.degree (S.coefficient a) = 0
  · rw [(regrade?_eq_none_iff T w hw ψ β).mpr h, ite_eq_left h]
    rfl
  · have hs := (regrade?_eq_some_iff T w hw ψ β (β.regrade T w hw ψ h)).mpr
      ⟨h, regrade_representative T w hw ψ β h⟩
    rw [hs, ite_eq_right h, Option.map_some, germ_regrade]

/-- Successive transports of a surviving coefficient retain the same full tail
as transport by the composite map. -/
theorem regrade_comp (β : AffineIncomingTail S a)
    (ha : χ (T S.degree) (ψ S.degree (S.coefficient a)) ≠ 0) :
    (β.regrade T w hw ψ (fun h => ha (by rw [h, map_zero]))).regrade U z hz χ ha =
      β.regrade (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) ha := by
  apply ext
  exact (regrade_representative (M' := M'') U z hz χ _ ha).trans
    ((regrade_representative (M' := M') T w hw ψ β _).trans
      (regrade_representative (M' := M'') (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) β ha).symm)

/-- Partial transport is functorial: deleting a zero intermediate coefficient
agrees with deletion after the composite coefficient map. -/
theorem regrade?_comp (β : AffineIncomingTail S a) :
    (β.regrade? T w hw ψ).bind (fun γ => γ.regrade? U z hz χ) =
      β.regrade? (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) := by
  classical
  by_cases h : ψ S.degree (S.coefficient a) = 0
  · have hc : χ (T S.degree) (ψ S.degree (S.coefficient a)) = 0 := by
      rw [h, map_zero]
    rw [(regrade?_eq_none_iff T w hw ψ β).mpr h, Option.bind_none]
    exact ((regrade?_eq_none_iff (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) β).mpr hc).symm
  · have hs := (regrade?_eq_some_iff T w hw ψ β (β.regrade T w hw ψ h)).mpr
      ⟨h, regrade_representative T w hw ψ β h⟩
    rw [hs, Option.bind_some]
    by_cases hc : χ (T S.degree) (ψ S.degree (S.coefficient a)) = 0
    · rw [(regrade?_eq_none_iff U z hz χ _).mpr hc]
      exact ((regrade?_eq_none_iff (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) β).mpr hc).symm
    · have hs' := (regrade?_eq_some_iff U z hz χ _
        ((β.regrade T w hw ψ h).regrade U z hz χ hc)).mpr
          ⟨hc, regrade_representative U z hz χ _ hc⟩
      rw [hs']
      apply Eq.symm
      apply (regrade?_eq_some_iff (U.comp T) z
        (by rw [← AddMonoidHom.comp_assoc, hz, hw])
        (fun p => (χ (T p)).comp (ψ p)) β _).mpr
      refine ⟨hc, ?_⟩
      exact (regrade_representative (M' := M'') U z hz χ _ hc).trans
        (regrade_representative (M' := M') T w hw ψ β h)

end AffineIncomingTail
end Mei
