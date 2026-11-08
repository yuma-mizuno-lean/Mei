/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Coefficient

/-!
# Successive coefficient changes of varying-chamber rays

The coefficient comparison of actual rays through independently graded chamber
modules respects identities and composition. For general coefficient maps the
comparison is defined on precisely the source rays whose final whole decoration
survives. Survival under a composite implies survival at the intermediate stage;
the two successive comparisons then agree with the composite comparison.
Lifting a target ray through two comparisons likewise gives the same source ray
as lifting it through the composite. Injective final chamber maps give identity
and composition laws for equivalences of unrestricted fibers.

The laws concern the complete ray, including every encounter and its degree,
the incoming tail, and all crossing parameters. They allow zero inputs, empty
paths, coefficient cancellation, and degree changes invisible in space. No
injectivity in intermediate chambers is required. Whole-component propagation
follows Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver

namespace Mei

section IdentityComposition

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M N O : Q → Type*}
  [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  [∀ q, AddCommMonoid (O q)] [∀ q, Module R (O q)]
  {ι κ ξ : Q → Type*}
  [∀ q, DecidableEq (ι q)] [∀ q, DecidableEq (κ q)] [∀ q, DecidableEq (ξ q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  (Z : ∀ {b c : Q}, (b ⟶ c) → O b →ₗ[R] O c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (𝓝 : ∀ q, κ q → Submodule R (N q)) [∀ q, DirectSum.Decomposition (𝓝 q)]
  (𝓞 : ∀ q, ξ q → Submodule R (O q)) [∀ q, DirectSum.Decomposition (𝓞 q)]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (w : ∀ q, κ q → V) (z : ∀ q, ξ q → V)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V)
  (W : J → Set V) (S : K → Set V) (C : Set V)
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀) (p : Path a b) (X : V)

local notation "Src" => PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p X

/-- Identity coefficient change fixes each actual ray, with its automatically
nonzero final decoration. -/
@[simp↓] -- Simplify the comparison before its dependent input and fiber types normalize.
theorem pathDecoratedRayCoefficientEquiv_refl_apply
    (s : {s : Src // LinearMap.id s.decoration ≠ 0}) :
    pathDecoratedRayCoefficientEquiv T T ℳ ℳ (fun _ => LinearMap.id)
      (fun _ => Equiv.refl _) (fun _ _ _ hx => hx)
      (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm)
      i₀ x v v (fun _ _ => rfl) ν ε c P W S C p X s = s.val := by
  apply PathDecoratedRay.ext_history
  simpa only [Path.Degrees.mapEquiv_apply, Equiv.coe_refl, Equiv.refl_apply,
    Path.Degrees.map_id] using
    pathDecoratedRayCoefficientEquiv_history T T ℳ ℳ (fun _ => LinearMap.id)
      (fun _ => Equiv.refl _) (fun _ _ _ hx => hx)
      (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm)
      i₀ x v v (fun _ _ => rfl) ν ε c P W S C p X s

/-- The unrestricted comparison for the identity coefficient map is the identity. -/
@[simp]
theorem pathDecoratedRayEmbeddingEquiv_refl :
    pathDecoratedRayEmbeddingEquiv T T ℳ ℳ (fun _ => LinearMap.id)
      (fun _ => Equiv.refl _) (fun _ _ _ hx => hx)
      (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm)
      i₀ x v v (fun _ _ => rfl) ν ε c P W S C Function.injective_id p X =
        Equiv.refl Src := by
  apply Equiv.ext
  intro s
  apply PathDecoratedRay.ext_history _ s
  simpa only [Path.Degrees.mapEquiv_apply, Equiv.coe_refl, Equiv.refl_apply,
    Path.Degrees.map_id] using
    pathDecoratedRayEmbeddingEquiv_history T T ℳ ℳ (fun _ => LinearMap.id)
      (fun _ => Equiv.refl _) (fun _ _ _ hx => hx)
      (fun _ => (LinearMap.id_comp _).trans (LinearMap.comp_id _).symm)
      i₀ x v v (fun _ _ => rfl) ν ε c P W S C Function.injective_id p X s

variable (r : ∀ q, M q →ₗ[R] N q) (s : ∀ q, N q →ₗ[R] O q)
  (σ : ∀ q, ι q ≃ κ q) (τ : ∀ q, κ q ≃ ξ q)
  (hr : ∀ q d x, x ∈ ℳ q d → r q x ∈ 𝓝 q (σ q d))
  (hs : ∀ q d x, x ∈ 𝓝 q d → s q x ∈ 𝓞 q (τ q d))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))
  (hU : ∀ {b c : Q} (e : b ⟶ c), (s c).comp (U e) = (Z e).comp (s b))
  (hv : ∀ q d, w q (σ q d) = v q d)
  (hw : ∀ q d, z q (τ q d) = w q d)

local notation "y" => (Subtype.mk (r a x) (hr a i₀ x x.property) : 𝓝 a (σ a i₀))
local notation "F" => pathDecoratedRayCoefficientEquiv T U ℳ 𝓝 r σ hr hT
  i₀ x v w hv ν ε c P W S C p X
local notation "G" => pathDecoratedRayCoefficientEquiv U Z 𝓝 𝓞 s τ hs hU
  (σ a i₀) y w z hw ν ε c P W S C p X

include hr hT hv

/-- If a whole decoration survives a composite coefficient change, the first
image survives and the second comparison is defined on that image. -/
theorem pathDecoratedRayCoefficientEquiv_survives_comp
    (β : Src) (hβ : (s b).comp (r b) β.decoration ≠ 0) :
    ∃ h₁ : r b β.decoration ≠ 0,
      s b (F ⟨β, h₁⟩).decoration ≠ 0 := by
  have h₁ : r b β.decoration ≠ 0 := fun h =>
    hβ (by simp only [LinearMap.comp_apply, h, map_zero])
  exact ⟨h₁, by
    simpa only [pathDecoratedRayCoefficientEquiv_decoration, LinearMap.comp_apply] using hβ⟩

include hs hU hw

/-- Two successive coefficient comparisons equal the composite comparison on
every surviving source ray. The intermediate survival proof may be chosen freely. -/
@[simp]
theorem pathDecoratedRayCoefficientEquiv_trans_apply
    (β : Src) (h₁ : r b β.decoration ≠ 0)
    (h₂ : s b (F ⟨β, h₁⟩).decoration ≠ 0) :
    G ⟨F ⟨β, h₁⟩, h₂⟩ =
      (pathDecoratedRayCoefficientEquiv T Z ℳ 𝓞
        (fun q => (s q).comp (r q)) (fun q => (σ q).trans (τ q))
        (fun q d x hx => by
          simpa only [LinearMap.comp_apply, Equiv.trans_apply] using hs q _ _ (hr q d x hx))
        (fun {b c} e => by
          rw [LinearMap.comp_assoc, hT e, ← LinearMap.comp_assoc, hU e, LinearMap.comp_assoc])
        i₀ x v z (fun q d => by
          simpa only [Equiv.trans_apply] using (hw q (σ q d)).trans (hv q d))
        ν ε c P W S C p X) ⟨β, by
          simpa only [pathDecoratedRayCoefficientEquiv_decoration, LinearMap.comp_apply]
            using h₂⟩ := by
  apply PathDecoratedRay.ext_history
  rw [pathDecoratedRayCoefficientEquiv_history U Z 𝓝 𝓞 s τ hs hU,
    pathDecoratedRayCoefficientEquiv_history T U ℳ 𝓝 r σ hr hT,
    pathDecoratedRayCoefficientEquiv_history T Z ℳ 𝓞
      (fun q => (s q).comp (r q)) (fun q => (σ q).trans (τ q))
      (fun q d x hx => by
        simpa only [LinearMap.comp_apply, Equiv.trans_apply] using hs q _ _ (hr q d x hx))]
  simp only [Path.Degrees.mapEquiv_apply, Path.Degrees.map_map, Equiv.coe_trans,
    Function.comp_def]

/-- Lifting an actual target ray through two coefficient changes equals lifting
through their composite, even when either change kills some source decorations. -/
@[simp]
theorem pathDecoratedRayCoefficientEquiv_trans_symm_apply
    (β : PathDecoratedRay Z 𝓞 (τ a (σ a i₀))
      ⟨s a (r a x), by
        exact hs a _ _ (hr a i₀ x x.property)⟩ z ν ε c P W S C p X) :
    ((F).symm ((G).symm β).val).val =
      ((pathDecoratedRayCoefficientEquiv T Z ℳ 𝓞
        (fun q => (s q).comp (r q)) (fun q => (σ q).trans (τ q))
        (fun q d x hx => by
          simpa only [LinearMap.comp_apply, Equiv.trans_apply] using hs q _ _ (hr q d x hx))
        (fun {b c} e => by
          rw [LinearMap.comp_assoc, hT e, ← LinearMap.comp_assoc, hU e, LinearMap.comp_assoc])
        i₀ x v z (fun q d => by
          simpa only [Equiv.trans_apply] using (hw q (σ q d)).trans (hv q d))
        ν ε c P W S C p X).symm β).val := by
  apply PathDecoratedRay.ext_history
  rw [pathDecoratedRayCoefficientEquiv_symm_history T U ℳ 𝓝 r σ hr hT,
    pathDecoratedRayCoefficientEquiv_symm_history U Z 𝓝 𝓞 s τ hs hU]
  -- Normalize the composite input degree and coefficient when matching the target fiber.
  erw [pathDecoratedRayCoefficientEquiv_symm_history T Z ℳ 𝓞
      (fun q => (s q).comp (r q)) (fun q => (σ q).trans (τ q))
      (fun q d x hx => by
        simpa only [LinearMap.comp_apply, Equiv.trans_apply] using hs q _ _ (hr q d x hx))]
  simp only [Path.Degrees.mapEquiv_symm_apply, Path.Degrees.map_map,
    Equiv.symm_trans, Equiv.coe_trans, Function.comp_def]

/-- Injective final chamber maps give composable equivalences of unrestricted
fibers. Injectivity is unnecessary in every other chamber. -/
@[simp]
theorem pathDecoratedRayEmbeddingEquiv_trans
    (hinj : Function.Injective (r b)) (hinj' : Function.Injective (s b)) :
    (pathDecoratedRayEmbeddingEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv
      ν ε c P W S C hinj p X).trans
      (pathDecoratedRayEmbeddingEquiv U Z 𝓝 𝓞 s τ hs hU (σ a i₀) y w z hw
        ν ε c P W S C hinj' p X) =
      pathDecoratedRayEmbeddingEquiv T Z ℳ 𝓞
        (fun q => LinearMap.comp (s q) (r q)) (fun q => Equiv.trans (σ q) (τ q))
        (fun q d x hx => by
          simpa only [LinearMap.comp_apply, Equiv.trans_apply] using hs q _ _ (hr q d x hx))
        (fun {b c} e => by
          rw [LinearMap.comp_assoc, hT e, ← LinearMap.comp_assoc, hU e,
            LinearMap.comp_assoc])
        i₀ x v z (fun q d => by
          simpa only [Equiv.trans_apply] using (hw q (σ q d)).trans (hv q d))
        ν ε c P W S C (hinj'.comp hinj) p X := by
  apply Equiv.ext
  intro β
  have h₁ : r b β.decoration ≠ 0 := fun h =>
    β.decoration_ne_zero (hinj (h.trans (map_zero (r b)).symm))
  have h₂ : s b (F ⟨β, h₁⟩).decoration ≠ 0 := fun h =>
    (F ⟨β, h₁⟩).decoration_ne_zero (hinj' (h.trans (map_zero (s b)).symm))
  rw [Equiv.trans_apply]
  -- The second and composite fibers use propositionally normalized incoming data.
  erw [pathDecoratedRayEmbeddingEquiv_apply U Z 𝓝 𝓞 s τ hs hU,
    pathDecoratedRayEmbeddingEquiv_apply T U ℳ 𝓝 r σ hr hT,
    pathDecoratedRayEmbeddingEquiv_apply T Z ℳ 𝓞]
  exact pathDecoratedRayCoefficientEquiv_trans_apply T U Z ℳ 𝓝 𝓞 v w z ν ε c P W S C i₀ x p X
      r s σ τ hr hs hT hU hv hw β h₁ h₂

end IdentityComposition

end Mei
