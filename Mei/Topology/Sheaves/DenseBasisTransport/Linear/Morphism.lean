/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.DenseBasisTransport.Morphism
public import Mei.Topology.Sheaves.DenseBasisTransport.Linear.Basic

/-!
# Semilinear maps of transport sections

An intertwining semilinear coefficient map induces semilinear maps on the actual
sections of the transport sheaves. These are the components of the existing
Type-valued sheaf morphism, so they commute with restriction. Evaluation commutes
with the coefficient map as a semilinear identity.

The ambient map is an open embedding. Target coefficient points need not all come
from source coefficient points: the values on the mapped dense domain determine
the whole target section uniquely. Scalar rings may differ and need not be
commutative; coefficient semimodules need not have additive inverses.
-/

public noncomputable section

open CategoryTheory TopologicalSpace Opposite Set Topology TopCat

universe u v r r'

namespace Mei.DenseBasisTransport

variable {X Y : TopCat.{u}} {S : Set X} {S' : Set Y} {M N : Type v}
  (T : DenseBasisTransport S M) (T' : DenseBasisTransport S' N)
  (R : Type r) (R' : Type r') [Semiring R] [Semiring R']
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R' N]
  [T.IsAdditive] [T'.IsAdditive] [T.PreservesSMul R] [T'.PreservesSMul R']
  {σ : R →+* R'} (j : X ⟶ Y) (hj : IsOpenEmbedding j) (q : S → S')
  (hq : ∀ x, (q x).val = j x.val) (φ : M →ₛₗ[σ] N)
  (hchart : ∀ B, B ∈ T.basis → hj.functor.obj B ∈ T'.basis)
  (htransport : ∀ B (hB : B ∈ T.basis) x y hx hy m,
    φ (T.transport B hB x y hx hy m) =
      T'.transport (hj.functor.obj B) (hchart B hB) (q x) (q y)
        (mem_image_of_mem j hj q hq B x hx)
        (mem_image_of_mem j hj q hq B y hy) (φ m))

/-- The existing transport-sheaf morphism on each open, bundled semilinearly. -/
def semilinearMapOfIntertwining (U : Opens X) :
    T.sheaf.presheaf.obj (op U) →ₛₗ[σ]
      T'.sheaf.presheaf.obj (op (hj.functor.obj U)) where
  toFun := (T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom.app (op U)
  map_add' s t := by
    apply T.section_ext_image T' j hj q hq le_rfl
    intro x hx
    have hxU := hj.injective.mem_set_image.mp (hq x ▸ hx)
    -- Fix the section carrier explicitly: the Type-valued image restriction
    -- otherwise hides the target algebra from instance synthesis.
    let F : T.sheaf.presheaf.obj (op U) →
        T'.sheaf.presheaf.obj (op (hj.functor.obj U)) :=
      (T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom.app (op U)
    have hval (r : T.sheaf.presheaf.obj (op U)) :=
      T.value_mapOfIntertwining T' j hj q hq φ hchart htransport r x hxU
    calc
      T'.value (F (s + t)) (q x) hx = φ (T.value (s + t) x hxU) := hval (s + t)
      _ = φ (T.value s x hxU) + φ (T.value t x hxU) :=
        (congrArg φ (T.value_add s t x hxU)).trans (φ.map_add _ _)
      _ = T'.value (F s) (q x) hx + T'.value (F t) (q x) hx :=
        congrArg₂ (· + ·) (hval s).symm (hval t).symm
      _ = T'.value (F s + F t) (q x) hx := (T'.value_add (F s) (F t) (q x) hx).symm
  map_smul' a s := by
    apply T.section_ext_image T' j hj q hq le_rfl
    intro x hx
    have hxU := hj.injective.mem_set_image.mp (hq x ▸ hx)
    -- Fix the section carrier explicitly: the Type-valued image restriction
    -- otherwise hides the target algebra from instance synthesis.
    let F : T.sheaf.presheaf.obj (op U) →
        T'.sheaf.presheaf.obj (op (hj.functor.obj U)) :=
      (T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom.app (op U)
    have hval (r : T.sheaf.presheaf.obj (op U)) :=
      T.value_mapOfIntertwining T' j hj q hq φ hchart htransport r x hxU
    calc
      T'.value (F (a • s)) (q x) hx = φ (T.value (a • s) x hxU) := hval (a • s)
      _ = σ a • φ (T.value s x hxU) :=
        (congrArg φ (T.value_smul R a s x hxU)).trans (φ.map_smulₛₗ a _)
      _ = σ a • T'.value (F s) (q x) hx := congrArg (σ a • ·) (hval s).symm
      _ = T'.value (σ a • F s) (q x) hx := (T'.value_smul R' (σ a) (F s) (q x) hx).symm

/-- The semilinear section map is exactly the original Type-valued component. -/
theorem semilinearMapOfIntertwining_apply (U : Opens X)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s =
      (T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom.app (op U) s := by rfl

/-- Mapped dense coefficient values are transformed by the prescribed map. -/
@[simp]
theorem value_semilinearMapOfIntertwining (U : Opens X)
    (s : T.sheaf.presheaf.obj (op U)) (x : S) (hx : x.val ∈ U) :
    T'.value (T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s)
      (q x) (mem_image_of_mem j hj q hq U x hx) = φ (T.value s x hx) := by
  exact T.value_mapOfIntertwining T' j hj q hq φ hchart htransport s x hx

/-- Restricting a transformed section agrees with transforming its restriction. -/
theorem semilinearMapOfIntertwining_restrict {U V : Opens X} (hVU : V ≤ U)
    (s : T.sheaf.presheaf.obj (op U)) :
    T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport V
        (T.restrictionLinearMap R hVU s) =
      T'.restrictionLinearMap R' (hj.functor.map (homOfLE hVU)).le
        (T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s) := by
  let α := (T.mapOfIntertwining T' j hj q hq φ hchart htransport).hom
  -- Give the components their original section carriers so the public
  -- restriction equations apply through the Type-valued image restriction.
  let eU : T.sheaf.presheaf.obj (op U) →
      T'.sheaf.presheaf.obj (op (hj.functor.obj U)) := α.app (op U)
  let eV : T.sheaf.presheaf.obj (op V) →
      T'.sheaf.presheaf.obj (op (hj.functor.obj V)) := α.app (op V)
  calc
    T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport V
        (T.restrictionLinearMap R hVU s) = eV (T.restrictionLinearMap R hVU s) := rfl
    _ = eV (T.sheaf.presheaf.map (homOfLE hVU).op s) :=
      congrArg eV (T.restrictionLinearMap_apply R hVU s)
    _ = T'.sheaf.presheaf.map (hj.functor.map (homOfLE hVU)).op (eU s) :=
      α.naturality_apply (homOfLE hVU).op s
    _ = T'.restrictionLinearMap R' (hj.functor.map (homOfLE hVU)).le (eU s) :=
      (T'.restrictionLinearMap_apply R' (hj.functor.map (homOfLE hVU)).le (eU s)).symm
    _ = T'.restrictionLinearMap R' (hj.functor.map (homOfLE hVU)).le
        (T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s) := rfl

/-- Linear evaluation commutes semilinearly with changing coefficients. -/
theorem evaluationLinearMap_comp_semilinearMapOfIntertwining (U : Opens X)
    (x : S) (hx : x.val ∈ U) :
    (T'.evaluationLinearMap R' (q x) (mem_image_of_mem j hj q hq U x hx)).comp
        (T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U) =
      φ.comp (T.evaluationLinearMap R x hx) := by
  apply LinearMap.ext
  intro s
  simp only [LinearMap.comp_apply, evaluationLinearMap_apply]
  exact T.value_semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s x hx

/-- Dense mapped coefficient values uniquely determine the semilinear section map. -/
theorem semilinearMapOfIntertwining_unique (U : Opens X)
    (ψ : T.sheaf.presheaf.obj (op U) →ₛₗ[σ]
      T'.sheaf.presheaf.obj (op (hj.functor.obj U)))
    (hψ : ∀ s x hx, T'.value (ψ s) (q x) (mem_image_of_mem j hj q hq U x hx) =
      φ (T.value s x hx)) :
    ψ = T.semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U := by
  apply LinearMap.ext
  intro s
  apply T.section_ext_image T' j hj q hq le_rfl
  intro x hx
  have hxU := hj.injective.mem_set_image.mp (hq x ▸ hx)
  exact (hψ s x hxU).trans
    (T.value_semilinearMapOfIntertwining T' R R' j hj q hq φ hchart htransport U s x hxU).symm

end Mei.DenseBasisTransport
