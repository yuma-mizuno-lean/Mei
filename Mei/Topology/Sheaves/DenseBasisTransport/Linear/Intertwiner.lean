/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Morphism
public import Mei.Topology.Category.TopCat.Opens

/-!
# Composing semilinear coefficient transport

Semilinear intertwiners record the coefficient-point map, coefficient map and chart
compatibility over a fixed open embedding. They compose even when the intermediate
and final coefficient domains have points missing from the preceding dense domain.

Their maps on sections are the existing semilinear transport maps. Identity and
composition hold on the whole section, including the additional coefficient
points. The composition equation uses the original linear restriction to identify
the equal opens obtained by taking the two images successively or at once.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Topology TopCat

universe u v r r' r''

namespace Mei.DenseBasisTransport

variable {X Y Z : TopCat.{u}} {S : Set X} {S' : Set Y} {S'' : Set Z}
  {M N P : Type v} {R : Type r} {R' : Type r'} {R'' : Type r''}
  [Semiring R] [Semiring R'] [Semiring R'']
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R' N] [Module R'' P]
  (T : DenseBasisTransport S M) (T' : DenseBasisTransport S' N)

/-- A semilinear coefficient map compatible with the charts and transports of an
open embedding. The point map need not exhaust the target coefficient domain. -/
structure SemilinearIntertwiner (σ : R →+* R') (j : X ⟶ Y) (hj : IsOpenEmbedding j) where
  /-- Map from source coefficient points to target coefficient points. -/
  mapPoint : S → S'
  /-- The point map lies over the ambient open embedding. -/
  mapPoint_val : ∀ x, (mapPoint x).val = j x.val
  /-- The semilinear map on coefficient values. -/
  mapCoefficients : M →ₛₗ[σ] N
  /-- Images of source transport charts are target transport charts. -/
  map_basis : ∀ B, B ∈ T.basis → hj.functor.obj B ∈ T'.basis
  /-- Coefficient transport commutes with the semilinear coefficient map. -/
  map_transport : ∀ B (hB : B ∈ T.basis) x y hx hy m,
    mapCoefficients (T.transport B hB x y hx hy m) =
      T'.transport (hj.functor.obj B) (map_basis B hB) (mapPoint x) (mapPoint y)
        (mem_image_of_mem j hj mapPoint mapPoint_val B x hx)
        (mem_image_of_mem j hj mapPoint mapPoint_val B y hy) (mapCoefficients m)

namespace SemilinearIntertwiner

variable {T T'} {T'' : DenseBasisTransport S'' P}
  {σ : R →+* R'} {τ : R' →+* R''} {ρ : R →+* R''}
  {j : X ⟶ Y} {k : Y ⟶ Z} {hj : IsOpenEmbedding j} {hk : IsOpenEmbedding k}

/-- An intertwiner is determined by its semilinear coefficient map: the ambient
map already determines the image of every coefficient point. -/
@[ext]
theorem ext {f g : T.SemilinearIntertwiner T' σ j hj}
    (h : f.mapCoefficients = g.mapCoefficients) : f = g := by
  have hq : f.mapPoint = g.mapPoint := by
    funext x
    apply Subtype.ext
    exact (f.mapPoint_val x).trans (g.mapPoint_val x).symm
  cases f
  cases g
  cases hq
  cases h
  rfl

/-- The identity coefficient intertwiner over the identity open embedding. -/
def id (T : DenseBasisTransport S M) (R : Type r) [Semiring R] [Module R M] :
    T.SemilinearIntertwiner T (RingHom.id R) (𝟙 X) IsOpenEmbedding.id where
  mapPoint := _root_.id
  mapPoint_val _ := rfl
  mapCoefficients := LinearMap.id
  map_basis B hB := by
    rw [IsOpenMap.functor_obj_id]
    exact hB
  map_transport B hB x y hx hy m := by
    simp only [LinearMap.id_apply, IsOpenMap.functor_obj_id, _root_.id_eq]

/-- Identity transport fixes each coefficient point. -/
@[simp]
theorem id_mapPoint (T : DenseBasisTransport S M) (R : Type r)
    [Semiring R] [Module R M] (x : S) : (id T R).mapPoint x = x := by rfl

/-- Identity transport fixes each coefficient value. -/
@[simp]
theorem id_mapCoefficients_apply (T : DenseBasisTransport S M) (R : Type r)
    [Semiring R] [Module R M] (m : M) : (id T R).mapCoefficients m = m := by rfl

/-- Compose coefficient intertwiners and their ambient open embeddings. -/
def comp [RingHomCompTriple σ τ ρ] (g : T'.SemilinearIntertwiner T'' τ k hk)
    (f : T.SemilinearIntertwiner T' σ j hj) :
    T.SemilinearIntertwiner T'' ρ (j ≫ k) (hk.comp hj) where
  mapPoint := g.mapPoint ∘ f.mapPoint
  mapPoint_val x := by
    exact (g.mapPoint_val (f.mapPoint x)).trans (congrArg k (f.mapPoint_val x))
  mapCoefficients := g.mapCoefficients.comp f.mapCoefficients
  map_basis B hB := by
    rw [hj.isOpenMap.functor_obj_comp hk.isOpenMap]
    exact g.map_basis _ (f.map_basis B hB)
  map_transport B hB x y hx hy m := by
    simp only [LinearMap.comp_apply]
    rw [f.map_transport, g.map_transport]
    simp only [hj.isOpenMap.functor_obj_comp hk.isOpenMap, Function.comp_apply]

/-- Composite transport sends coefficient points by the two successive point maps. -/
@[simp]
theorem comp_mapPoint [RingHomCompTriple σ τ ρ]
    (g : T'.SemilinearIntertwiner T'' τ k hk)
    (f : T.SemilinearIntertwiner T' σ j hj) (x : S) :
    (g.comp (ρ := ρ) f).mapPoint x = g.mapPoint (f.mapPoint x) := by rfl

/-- Composite transport applies the two semilinear coefficient maps successively. -/
@[simp]
theorem comp_mapCoefficients_apply [RingHomCompTriple σ τ ρ]
    (g : T'.SemilinearIntertwiner T'' τ k hk)
    (f : T.SemilinearIntertwiner T' σ j hj) (m : M) :
    (g.comp (ρ := ρ) f).mapCoefficients m = g.mapCoefficients (f.mapCoefficients m) := by rfl

variable [T.IsAdditive] [T'.IsAdditive] [T''.IsAdditive]
  [T.PreservesSMul R] [T'.PreservesSMul R'] [T''.PreservesSMul R'']

/-- Apply an intertwiner to the actual locally parallel sections. -/
def sections (f : T.SemilinearIntertwiner T' σ j hj) (U : Opens X) :
    T.sheaf.presheaf.obj (op U) →ₛₗ[σ] T'.sheaf.presheaf.obj (op (hj.functor.obj U)) :=
  T.semilinearMapOfIntertwining T' R R' j hj f.mapPoint f.mapPoint_val
    f.mapCoefficients f.map_basis f.map_transport U

/-- On mapped coefficient points, the section map is the coefficient map. -/
@[simp]
theorem value_sections (f : T.SemilinearIntertwiner T' σ j hj) (U : Opens X)
    (s : T.sheaf.presheaf.obj (op U)) (x : S) (hx : x.val ∈ U) :
    T'.value (f.sections U s) (f.mapPoint x)
      (mem_image_of_mem j hj f.mapPoint f.mapPoint_val U x hx) =
        f.mapCoefficients (T.value s x hx) :=
  T.value_semilinearMapOfIntertwining T' R R' j hj f.mapPoint f.mapPoint_val
    f.mapCoefficients f.map_basis f.map_transport U s x hx

/-- Dense mapped coefficient values determine the whole semilinear section map. -/
theorem sections_unique (f : T.SemilinearIntertwiner T' σ j hj) (U : Opens X)
    (ψ : T.sheaf.presheaf.obj (op U) →ₛₗ[σ]
      T'.sheaf.presheaf.obj (op (hj.functor.obj U)))
    (hψ : ∀ s x hx, T'.value (ψ s) (f.mapPoint x)
      (mem_image_of_mem j hj f.mapPoint f.mapPoint_val U x hx) =
        f.mapCoefficients (T.value s x hx)) : ψ = f.sections U :=
  T.semilinearMapOfIntertwining_unique T' R R' j hj f.mapPoint f.mapPoint_val
    f.mapCoefficients f.map_basis f.map_transport U ψ hψ

/-- Linear evaluation commutes semilinearly with the section map of an intertwiner. -/
theorem evaluationLinearMap_comp_sections (f : T.SemilinearIntertwiner T' σ j hj)
    (U : Opens X) (x : S) (hx : x.val ∈ U) :
    (T'.evaluationLinearMap R' (f.mapPoint x)
      (mem_image_of_mem j hj f.mapPoint f.mapPoint_val U x hx)).comp (f.sections U) =
        f.mapCoefficients.comp (T.evaluationLinearMap R x hx) :=
  T.evaluationLinearMap_comp_semilinearMapOfIntertwining T' R R' j hj
    f.mapPoint f.mapPoint_val f.mapCoefficients f.map_basis f.map_transport U x hx

/-- Restriction commutes with the section map of an intertwiner. -/
theorem sections_restrict (f : T.SemilinearIntertwiner T' σ j hj)
    {U V : Opens X} (hVU : V ≤ U) (s : T.sheaf.presheaf.obj (op U)) :
    f.sections V (T.restrictionLinearMap R hVU s) =
      T'.restrictionLinearMap R' (hj.functor.map (homOfLE hVU)).le (f.sections U s) :=
  T.semilinearMapOfIntertwining_restrict T' R R' j hj f.mapPoint f.mapPoint_val
    f.mapCoefficients f.map_basis f.map_transport hVU s

/-- Identity coefficient transport is the canonical restriction to the equal
identity-image open. -/
@[simp]
theorem sections_id (U : Opens X) :
    (id T R).sections U = T.restrictionLinearMap R
      (IsOpenMap.functor_obj_id U).le := by
  symm
  apply T.semilinearMapOfIntertwining_unique
  intro s x hx
  exact T.value_restrictionLinearMap R _ s x _

/-- Applying two coefficient changes successively agrees with their composite.
The canonical restriction only identifies the two equal image opens. -/
theorem sections_comp [RingHomCompTriple σ τ ρ] (g : T'.SemilinearIntertwiner T'' τ k hk)
    (f : T.SemilinearIntertwiner T' σ j hj) (U : Opens X) :
    (g.comp (ρ := ρ) f).sections U =
      (T''.restrictionLinearMap R''
        (hj.isOpenMap.functor_obj_comp hk.isOpenMap U).le).comp
        ((g.sections (hj.functor.obj U)).comp (f.sections U)) := by
  symm
  apply T.semilinearMapOfIntertwining_unique
  intro s x hx
  simp only [LinearMap.comp_apply, value_restrictionLinearMap]
  exact (g.value_sections _ (f.sections U s) (f.mapPoint x)
    (mem_image_of_mem j hj f.mapPoint f.mapPoint_val U x hx)).trans
      (congrArg g.mapCoefficients (f.value_sections U s x hx))

end SemilinearIntertwiner

end Mei.DenseBasisTransport
