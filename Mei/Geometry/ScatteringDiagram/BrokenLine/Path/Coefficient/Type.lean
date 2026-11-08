/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Coefficient
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family

/-!
# Coefficient embeddings of complete types of path families

A coefficient comparison that is injective in the final chamber, carries homogeneous
pieces along degree bijections and preserves velocities identifies the complete types of
a finite path inventory with those of the comparison. The identification keeps every
encounter path, applies the degree bijections to the whole history, and sends the final
decoration through the comparison. The complete endpoint domains and the continuous path
extensions are unchanged (`Path.Degrees.reverseVertexLabels_map`), so closed endpoint charts
of one family are closed endpoint charts of the other with weights sent through the
comparison. This is compatible with
the comparison of actual ray fibers.

The construction is `pathDecoratedHistoryCoefficientEquiv` on each path, whose histories
all survive by injectivity. It follows Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3 (arXiv:1601.07081v4).
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M N : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  {ι κ : Q → Type*} [∀ q, DecidableEq (ι q)] [∀ q, DecidableEq (κ q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  (U : ∀ {b c : Q}, (b ⟶ c) → N b →ₗ[R] N c)
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  (𝓝 : ∀ q, κ q → Submodule R (N q)) [∀ q, DirectSum.Decomposition (𝓝 q)]
  (r : ∀ q, M q →ₗ[R] N q) (σ : ∀ q, ι q ≃ κ q)
  (hr : ∀ q d x, x ∈ ℳ q d → r q x ∈ 𝓝 q (σ q d))
  (hT : ∀ {b c : Q} (e : b ⟶ c), (r c).comp (T e) = (U e).comp (r b))
  {a b : Q} (i₀ : ι a) (x : ℳ a i₀)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (v : ∀ q, ι q → V) (w : ∀ q, κ q → V)
  (hv : ∀ q d, w q (σ q d) = v q d)
  (ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ)
  (ε : ∀ {b c : Q}, (b ⟶ c) → SignType)
  (hinj : Function.Injective (r b)) (s : Finset (Path a b))

local notation "x'" => (Subtype.mk (r a x) (hr a i₀ x x.property) : 𝓝 a (σ a i₀))
local notation "Source" => PathDecoratedType T ℳ i₀ x s v ν ε
local notation "Target" => PathDecoratedType U 𝓝 (σ a i₀) x' s w ν ε

include hinj in
/-- Injectivity in the final chamber keeps every surviving history surviving. -/
theorem map_homogeneousHistory_ne_zero_of_mem_pathDecoratedHistorySupport (p : Path a b)
    (d : (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p : Type _)) :
    r b (p.homogeneousHistory T ℳ d.val x) ≠ 0 := fun hz =>
  ((mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε p d.val).mp d.property).1
    (hinj (hz.trans (map_zero (r b)).symm))

/-- An injective coefficient comparison identifies the complete types of a path
inventory, keeping each encounter path and transporting the whole degree history. -/
def pathDecoratedTypeEmbeddingEquiv : Source ≃ Target :=
  Equiv.sigmaCongrRight fun p =>
    (Equiv.subtypeUnivEquiv (map_homogeneousHistory_ne_zero_of_mem_pathDecoratedHistorySupport
      T ℳ r i₀ x v ν ε hinj p.val)).symm.trans
      (pathDecoratedHistoryCoefficientEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε p.val)

local notation "E" => pathDecoratedTypeEmbeddingEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε hinj s
local notation "H" p:max d:max => Path.Degrees.mapEquiv σ (Subtype.val p) (Subtype.val d)

/-- The type comparison keeps the encounter path and applies the degree bijections to the
whole history. -/
theorem pathDecoratedTypeEmbeddingEquiv_mk (p : (s : Type _))
    (d : (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val : Type _)) :
    E ⟨p, d⟩ = ⟨p, pathDecoratedHistoryCoefficientEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε p.val
      ⟨d, map_homogeneousHistory_ne_zero_of_mem_pathDecoratedHistorySupport T ℳ r i₀ x v ν ε
        hinj p.val d⟩⟩ := (rfl)

include hr hT in
/-- The type comparison sends the whole final decoration through the comparison. -/
theorem pathDecoratedTypeEmbeddingEquiv_decoration (p : (s : Type _))
    (d : (pathDecoratedHistorySupport T ℳ i₀ x v ν ε p.val : Type _)) :
    p.val.homogeneousHistory U 𝓝 (H p d) x' = r b (p.val.homogeneousHistory T ℳ d.val x) := by
  rw [Path.Degrees.mapEquiv_apply]
  exact (p.val.map_homogeneousHistory_of_injective T ℳ U 𝓝 r (fun q => σ q)
    (fun _ => hr _) hT (fun {_ _} _ => (σ _).injective) d.val x).symm

variable (c : ∀ {b c : Q}, (b ⟶ c) → ℝ)
  (P : ∀ {b c : Q}, (b ⟶ c) → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

/-- The type comparison agrees with the comparison of actual ray fibers. -/
theorem pathDecoratedRayEmbeddingEquiv_type (p : (s : Type _)) (X : V)
    (q : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C p.val X) :
    (⟨p, (pathDecoratedRayEmbeddingEquiv T U ℳ 𝓝 r σ hr hT i₀ x v w hv ν ε c P W S C hinj
      p.val X q).1⟩ : Target) = E ⟨p, q.1⟩ := by
  rw [pathDecoratedTypeEmbeddingEquiv_mk]
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  rw [pathDecoratedRayEmbeddingEquiv_history, pathDecoratedHistoryCoefficientEquiv_val]

end Mei
