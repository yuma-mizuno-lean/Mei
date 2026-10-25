/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Generic points for affine arrangements

The common complement of countably many proper affine subspaces of a
finite-dimensional real normed space is dense and is a Gδ set. For a finite
family the complement is open. These statements allow arbitrarily small
perturbations avoiding all the prescribed affine exceptions.

For affine obstacles of codimension at least two, a freely chosen intermediate
vertex can avoid all the affine spans with either endpoint. This constructs two
segments avoiding every obstacle while fixing both endpoints. Finite exceptional
arrangements support union and transport by affine equivalences.

For a set covered by such obstacles, the endpoints need only avoid the set
itself, and the vertex may simultaneously avoid additional proper affine
subspaces.
-/

public section

open Set

namespace AffineSubspace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The points avoiding every member of an affine family. -/
def genericLocus {ι : Sort*} (A : ι → AffineSubspace ℝ V) : Set V :=
  {x | ∀ i, x ∉ A i}

/-- Membership in the generic locus means avoiding each exception. -/
@[simp]
theorem mem_genericLocus {ι : Sort*} {A : ι → AffineSubspace ℝ V} {x : V} :
    x ∈ genericLocus A ↔ ∀ i, x ∉ A i := Iff.rfl

/-- The generic locus is the intersection of the complements. -/
theorem genericLocus_eq_iInter {ι : Sort*} (A : ι → AffineSubspace ℝ V) :
    genericLocus A = ⋂ i, (A i : Set V)ᶜ := by
  ext x
  simp

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A proper real affine subspace has empty interior, even without a
finite-dimensionality assumption. -/
theorem interior_eq_empty_of_ne_top (S : AffineSubspace ℝ V) (hS : S ≠ ⊤) :
    interior (S : Set V) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hspan := isOpen_interior.affineSpan_eq_top ⟨x, hx⟩
  have hle : affineSpan ℝ (interior (S : Set V)) ≤ S :=
    affineSpan_le.mpr interior_subset
  exact hS (top_le_iff.mp (hspan ▸ hle))

/-- The complement of a proper affine subspace is dense. -/
theorem dense_compl_of_ne_top (S : AffineSubspace ℝ V) (hS : S ≠ ⊤) :
    Dense (S : Set V)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (S.interior_eq_empty_of_ne_top hS)

variable [FiniteDimensional ℝ V]

/-- Countably many proper affine subspaces have dense common complement. -/
theorem dense_genericLocus {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ V)
    (hA : ∀ i, A i ≠ ⊤) : Dense (genericLocus A) := by
  rw [genericLocus_eq_iInter]
  exact dense_iInter_of_isOpen
    (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)
    (fun i => (A i).dense_compl_of_ne_top (hA i))

/-- The common complement is a countable intersection of open sets. -/
theorem isGδ_genericLocus {ι : Sort*} [Countable ι] (A : ι → AffineSubspace ℝ V) :
    IsGδ (genericLocus A) := by
  rw [genericLocus_eq_iInter]
  exact IsGδ.iInter_of_isOpen (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- For a finite family, the common complement is open. -/
theorem isOpen_genericLocus {ι : Sort*} [Finite ι] (A : ι → AffineSubspace ℝ V) :
    IsOpen (genericLocus A) := by
  rw [genericLocus_eq_iInter]
  exact isOpen_iInter_of_finite (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)

/-- A generic point can be chosen in any prescribed nonempty open set. -/
theorem exists_mem_open_genericLocus {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  obtain ⟨x, hxU, hxA⟩ := (dense_genericLocus A hA).inter_open_nonempty U hU hne
  exact ⟨x, hxU, hxA⟩

/-- Generic points can be chosen arbitrarily close to any point. -/
theorem exists_dist_lt_genericLocus {ι : Sort*} [Countable ι]
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    (x : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, dist y x < ε ∧ ∀ i, y ∉ A i := by
  obtain ⟨y, hy, hA⟩ := exists_mem_open_genericLocus A hA
    Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
  exact ⟨y, hy, hA⟩

end Topology

section Algebra

open scoped Affine

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Adding one point to a subspace of codimension at least two still gives a
proper affine subspace. -/
theorem affineSpan_insert_ne_top_of_finrank (S : AffineSubspace k P)
    (hS : Module.finrank k S.direction + 1 < Module.finrank k V) (x : P) :
    affineSpan k (insert x (S : Set P)) ≠ ⊤ := by
  intro htop
  have hle := finrank_vectorSpan_insert_le S x
  rw [← direction_affineSpan, htop, direction_top, finrank_top] at hle
  exact (not_le_of_gt hS) hle

/-- Outside the span of an affine obstacle and an endpoint, every nonzero
parameter on the line from that endpoint avoids the obstacle. The endpoint
itself need not avoid the obstacle. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (S : AffineSubspace k P)
    {x z : P} (hz : z ∉ affineSpan k (insert x (S : Set P)))
    {t : k} (ht : t ≠ 0) : AffineMap.lineMap x z t ∉ S := by
  intro htS
  apply hz
  have hxspan : x ∈ affineSpan k (insert x (S : Set P)) :=
    subset_affineSpan k _ (mem_insert x _)
  have htspan : AffineMap.lineMap x z t ∈ affineSpan k (insert x (S : Set P)) :=
    subset_affineSpan k _ (mem_insert_of_mem x htS)
  simpa only [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht,
    AffineMap.lineMap_apply_one] using AffineMap.lineMap_mem t⁻¹ hxspan htspan

/-- A vertex outside the affine span of an obstacle and an allowed endpoint
determines a full line avoiding the obstacle. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert (S : AffineSubspace k P)
    {x z : P} (hx : x ∉ S) (hz : z ∉ affineSpan k (insert x (S : Set P)))
    (t : k) : AffineMap.lineMap x z t ∉ S := by
  by_cases ht : t = 0
  · simpa [ht] using hx
  · exact S.lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero hz ht

end Algebra

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Between endpoints outside countably many affine obstacles of codimension at
least two, an intermediate vertex can be chosen in any nonempty open set so
that both full lines, and hence both segments, avoid every obstacle.

Only the vertex is varied: both endpoints remain fixed. -/
theorem exists_mem_open_two_lineMaps_avoid {ι : Type*} [Countable ι]
    (S : ι → AffineSubspace ℝ V)
    (hS : ∀ i, Module.finrank ℝ (S i).direction + 1 < Module.finrank ℝ V)
    {x y : V} (hx : ∀ i, x ∉ S i) (hy : ∀ i, y ∉ S i)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, ∀ i (t : ℝ),
      AffineMap.lineMap x z t ∉ S i ∧ AffineMap.lineMap y z t ∉ S i := by
  let A : ι ⊕ ι → AffineSubspace ℝ V := Sum.elim
    (fun i => affineSpan ℝ (insert x (S i : Set V)))
    (fun i => affineSpan ℝ (insert y (S i : Set V)))
  have hA : ∀ i, A i ≠ ⊤ := by
    intro i
    cases i with
    | inl i => exact (S i).affineSpan_insert_ne_top_of_finrank (hS i) x
    | inr i => exact (S i).affineSpan_insert_ne_top_of_finrank (hS i) y
  obtain ⟨z, hzU, hz⟩ := exists_mem_open_genericLocus A hA hU hne
  exact ⟨z, hzU, fun i t =>
    ⟨(S i).lineMap_not_mem_of_not_mem_affineSpan_insert (hx i) (hz (.inl i)) t,
      (S i).lineMap_not_mem_of_not_mem_affineSpan_insert (hy i) (hz (.inr i)) t⟩⟩

/-- A set covered by countably many affine subspaces of codimension at least
two can be avoided by both full lines from two fixed allowed endpoints to a
vertex in any nonempty open set. The vertex may simultaneously avoid any
additional countable family of proper affine subspaces.

The endpoints are required to avoid the actual set only; they may lie in its
affine cover. The prescribed open set constrains the vertex, not the lines. -/
theorem exists_mem_open_two_lineMaps_avoid_set {ι κ : Type*} [Countable ι] [Countable κ]
    (S : κ → AffineSubspace ℝ V)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    {E : Set V} (hE : E ⊆ ⋃ k, (S k : Set V))
    {x y : V} (hx : x ∉ E) (hy : y ∉ E)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, z ∉ A i) ∧ ∀ t : ℝ,
      AffineMap.lineMap x z t ∉ E ∧ AffineMap.lineMap y z t ∉ E := by
  let B : (κ ⊕ κ) ⊕ ι → AffineSubspace ℝ V := Sum.elim
    (Sum.elim (fun k => affineSpan ℝ (insert x (S k : Set V)))
      (fun k => affineSpan ℝ (insert y (S k : Set V)))) A
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i
    rcases i with k | i
    · rcases k with k | k
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) x
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) y
    · exact hA i
  obtain ⟨z, hzU, hz⟩ := exists_mem_open_genericLocus B hB hU hne
  have havoid (p : V) (hp : p ∉ E)
      (hzp : ∀ k, z ∉ affineSpan ℝ (insert p (S k : Set V))) (t : ℝ) :
      AffineMap.lineMap p z t ∉ E := by
    by_cases ht : t = 0
    · simpa [ht] using hp
    · intro htE
      obtain ⟨k, htk⟩ := Set.mem_iUnion.mp (hE htE)
      exact (S k).lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (hzp k) ht htk
  exact ⟨z, hzU, fun i => hz (.inr i), fun t =>
    ⟨havoid x hx (fun k => hz (.inl (.inl k))) t,
      havoid y hy (fun k => hz (.inl (.inr k))) t⟩⟩

end Topology

end AffineSubspace

namespace Mei

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

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Generic points of a finite exceptional arrangement form an open set. -/
theorem isOpen_isGeneric (E : ExceptionalArrangement V) : IsOpen {x | E.IsGeneric x} := by
  simpa [AffineSubspace.genericLocus, IsGeneric] using
    AffineSubspace.isOpen_genericLocus (fun S : E.exceptions => S.1)

/-- Generic points of a finite exceptional arrangement form a dense set. -/
theorem dense_isGeneric (E : ExceptionalArrangement V) : Dense {x | E.IsGeneric x} := by
  simpa [AffineSubspace.genericLocus, IsGeneric] using
    AffineSubspace.dense_genericLocus (fun S : E.exceptions => S.1)
      (fun S => E.proper S.1 S.2)

/-- A countable family of finite arrangements has dense common generic locus. -/
theorem dense_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement V) : Dense {x | ∀ i, (E i).IsGeneric x} := by
  simpa [AffineSubspace.genericLocus, IsGeneric, Sigma.forall] using
    AffineSubspace.dense_genericLocus
      (fun p : Σ i, (E i).exceptions => p.2.1)
      (fun p => (E p.1).proper p.2.1 p.2.2)

/-- The common generic locus of countably many finite arrangements is a Gδ set. -/
theorem isGδ_iInter_isGeneric {ι : Type*} [Countable ι]
    (E : ι → ExceptionalArrangement V) : IsGδ {x | ∀ i, (E i).IsGeneric x} := by
  simpa [AffineSubspace.genericLocus, IsGeneric, Sigma.forall] using
    AffineSubspace.isGδ_genericLocus (fun p : Σ i, (E i).exceptions => p.2.1)

end Topology

end ExceptionalArrangement

end Mei
