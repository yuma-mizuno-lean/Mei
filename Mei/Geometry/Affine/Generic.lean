/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Exceptional arrangements

A locally finite-dimensional avoidance argument gives generic points on a face.
Exceptional arrangements package the forbidden affine subspaces and transport
them along affine equivalences.
-/

public section

open Set

namespace Mei

section Hyperplane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A set covered by countably many affine subspaces of ambient codimension at least two
has dense complement in a hyperplane: every point of the hyperplane is a limit of points
of the hyperplane outside the set. -/
theorem face_subset_closure_sdiff_of_finrank {ι : Sort*} [Countable ι]
    {ν : V →L[ℝ] ℝ} {b : ℝ} {Z : Set V} (hν : ν ≠ 0)
    (E : ι → AffineSubspace ℝ V) (hZE : Z ⊆ ⋃ i, (E i : Set V))
    (hE : ∀ i, Module.finrank ℝ (E i).direction + 1 < Module.finrank ℝ V) :
    {x | ν x = b} ⊆ closure ({x | ν x = b} \ Z) := by
  intro x hx
  have hx' : ν x = b := hx
  -- The face is the affine subspace through `x` with direction `ker ν`.
  let A : AffineSubspace ℝ V := .mk' x (LinearMap.ker ν.toLinearMap)
  have hA : ∀ y ∈ A, ν y = b := fun y hy => by
    have := AffineSubspace.mem_mk'.mp hy
    simpa [sub_eq_zero, hx'] using this
  have hdir : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ V := by
    rw [AffineSubspace.direction_mk']
    exact Module.Dual.finrank_ker_add_one_of_ne_zero (f := ν.toLinearMap)
      (fun h => hν (ContinuousLinearMap.coe_injective h))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hzE⟩ := A.exists_mem_open_avoid_of_finrank_lt E
    (fun i => by have := hE i; omega) (U := Subtype.val ⁻¹' Metric.ball x ε)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
    ⟨⟨x, AffineSubspace.self_mem_mk' x _⟩, Metric.mem_ball_self hε⟩
  exact ⟨z, ⟨hA z z.2, fun hzZ => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hZE hzZ)
    exact hzE i hi⟩, by simpa [dist_comm] using hz⟩

end Hyperplane

/-- A finite collection of proper affine subspaces to be avoided. Repeated
exceptions are identified. Empty affine subspaces are permitted. -/
structure ExceptionalArrangement (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The finite set of affine subspaces to avoid. -/
  exceptions : Finset (AffineSubspace ℝ V)
  /-- No exception contains the whole ambient space. -/
  proper : ∀ S ∈ exceptions, S ≠ ⊤

namespace ExceptionalArrangement

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A point is generic if it avoids every affine exception. -/
def IsGeneric (E : ExceptionalArrangement V) (x : V) : Prop :=
  ∀ S ∈ E.exceptions, x ∉ S

/-- A point is generic exactly when it avoids every exception. -/
theorem isGeneric_iff {E : ExceptionalArrangement V} {x : V} :
    E.IsGeneric x ↔ ∀ S ∈ E.exceptions, x ∉ S := (Iff.rfl)

/-- Union of the exceptions in two arrangements. -/
noncomputable def union (E F : ExceptionalArrangement V) : ExceptionalArrangement V := by
  classical
  exact ⟨E.exceptions ∪ F.exceptions, fun S h =>
    (Finset.mem_union.mp h).elim (E.proper S) (F.proper S)⟩

open Classical in
/-- The exceptions of a union are the union of the exceptions. -/
@[simp]
theorem exceptions_union (E F : ExceptionalArrangement V) :
    (E.union F).exceptions = E.exceptions ∪ F.exceptions := (rfl)

/-- Genericity for a union is genericity for each arrangement. -/
@[simp]
theorem isGeneric_union {E F : ExceptionalArrangement V} {x : V} :
    (E.union F).IsGeneric x ↔ E.IsGeneric x ∧ F.IsGeneric x := by
  classical
  simp [IsGeneric, union, or_imp, forall_and]

/-- Transport an arrangement by an affine equivalence. -/
noncomputable def map (E : ExceptionalArrangement V) (e : V ≃ᵃ[ℝ] W) :
    ExceptionalArrangement W := by
  classical
  refine ⟨E.exceptions.image (AffineSubspace.map e.toAffineMap), ?_⟩
  intro T hT htop
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  apply E.proper S hS
  apply top_unique
  intro x _
  apply (AffineSubspace.mem_map_iff_mem_of_injective (f := e.toAffineMap) e.injective).mp
  rw [htop]
  trivial

open Classical in
/-- Transport maps the finite set of exceptions by the affine equivalence. -/
@[simp]
theorem exceptions_map (E : ExceptionalArrangement V) (e : V ≃ᵃ[ℝ] W) :
    (E.map e).exceptions = E.exceptions.image (AffineSubspace.map e.toAffineMap) := (rfl)

/-- Transport preserves genericity of the corresponding points. -/
@[simp]
theorem isGeneric_map_iff {E : ExceptionalArrangement V} (e : V ≃ᵃ[ℝ] W) {x : V} :
    (E.map e).IsGeneric (e x) ↔ E.IsGeneric x := by
  classical
  simp [IsGeneric, map]

/-- Pullback under an affine equivalence, expressed by transport under its inverse. -/
noncomputable def comap (E : ExceptionalArrangement W) (e : V ≃ᵃ[ℝ] W) :
    ExceptionalArrangement V :=
  E.map e.symm

open Classical in
/-- Pullback maps the exceptions by the inverse affine equivalence. -/
@[simp]
theorem exceptions_comap (E : ExceptionalArrangement W) (e : V ≃ᵃ[ℝ] W) :
    (E.comap e).exceptions = E.exceptions.image (AffineSubspace.map e.symm.toAffineMap) :=
  (rfl)

/-- A point is generic in a pullback exactly when its image is generic. -/
@[simp]
theorem isGeneric_comap_iff {E : ExceptionalArrangement W} {e : V ≃ᵃ[ℝ] W} {x : V} :
    (E.comap e).IsGeneric x ↔ E.IsGeneric (e x) := by
  simpa [comap] using (isGeneric_map_iff (E := E) e.symm (x := e x))

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem genericLocus_exceptions (E : ExceptionalArrangement V) :
    AffineSubspace.genericLocus (fun S : E.exceptions => S.1) = {x | E.IsGeneric x} := by
  ext x
  simp [IsGeneric]

private theorem genericLocus_family {ι : Type*} (E : ι → ExceptionalArrangement V) :
    AffineSubspace.genericLocus (fun p : Σ i, (E i).exceptions => p.2.1) =
      {x | ∀ i, (E i).IsGeneric x} := by
  ext x
  simp [IsGeneric, Sigma.forall]

variable [FiniteDimensional ℝ V]

/-- Generic points of a finite exceptional arrangement form an open set. -/
theorem isOpen_isGeneric (E : ExceptionalArrangement V) : IsOpen {x | E.IsGeneric x} := by
  simpa only [genericLocus_exceptions] using
    AffineSubspace.isOpen_genericLocus (fun S : E.exceptions => S.1)

/-- Generic points of a finite exceptional arrangement form a dense set. -/
theorem dense_isGeneric (E : ExceptionalArrangement V) : Dense {x | E.IsGeneric x} := by
  simpa only [genericLocus_exceptions] using
    AffineSubspace.dense_genericLocus (fun S : E.exceptions => S.1)
      (fun S => E.proper S.1 S.2)

/-- A countable family of finite arrangements has dense common generic locus. -/
theorem dense_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement V) : Dense {x | ∀ i, (E i).IsGeneric x} := by
  simpa only [genericLocus_family] using
    AffineSubspace.dense_genericLocus
      (fun p : Σ i, (E i).exceptions => p.2.1)
      (fun p => (E p.1).proper p.2.1 p.2.2)

/-- The common generic locus of countably many finite arrangements is a Gδ set. -/
theorem isGδ_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement V) : IsGδ {x | ∀ i, (E i).IsGeneric x} := by
  simpa only [genericLocus_family] using
    AffineSubspace.isGδ_genericLocus (fun p : Σ i, (E i).exceptions => p.2.1)

end Topology

end ExceptionalArrangement

end Mei
