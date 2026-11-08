/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.LocalCrossing.Constancy
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Tangent
public import Mei.Geometry.Convex.Polyhedron.Tangent.SingularSupport

/-!
# The tangent diagram at a point

The tangent diagram of a directed diagram at a point `x` retains the walls whose support
contains `x`, each replaced by its tangent wall. Its supports are cones with apex `0`, and
need not be full hyperplanes. For each fixed cutoff `k`, closedness and finiteness of the
active walls give a neighbourhood of `x` on which active walls missing `x` contribute nothing.
This neighbourhood may depend on `k`.

A wall through `x` is active at a cutoff in the tangent diagram exactly when it is active in the
diagram. For each fixed cutoff `k`, on a neighbourhood of `x` depending on `k`, the active
supports are the translates of the tangent supports. At a point in this neighbourhood that is
regular for the diagram, its displacement is regular for the tangent diagram and the combined
labels at cutoff `k` agree in each crossing direction. The singular supports themselves agree
under translation locally. On every bounded set of tangent displacements this comparison holds
uniformly under sufficiently small positive rescaling.
These local identifications compare the crossings of a diagram near a joint with those of its
tangent diagram. Consistency of the tangent diagram is not asserted here.
-/

public section

noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι) (x : V)

/-- The walls through `x`, each replaced by its tangent wall at `x`. -/
def tangentAt : DirectedDiagram (d := d) h H {j | x ∈ (D.wall j).support} where
  wall j := (D.wall j.1).tangentAt x j.2
  finite_active := by
    simpa only [restrict_wall, DirectedWall.tangentAt_label] using
      (D.restrict {j | x ∈ (D.wall j).support}).finite_active

@[simp]
theorem tangentAt_wall (j : {j | x ∈ (D.wall j).support}) :
    (D.tangentAt x).wall j = (D.wall j.1).tangentAt x j.2 := (rfl)

/-- A wall through `x` is active in the tangent diagram exactly when it is active in the
diagram. -/
theorem mem_active_tangentAt (k : ℕ) (j : {j | x ∈ (D.wall j).support}) :
    j ∈ (D.tangentAt x).active k ↔ j.1 ∈ D.active k := by
  simp only [mem_active, tangentAt_wall, DirectedWall.tangentAt_label]

variable {x}

/-- Near `x`, an active wall of the diagram contains a point exactly when it passes through `x`
and the tangent wall contains the displacement. -/
theorem eventually_forall_mem_support_iff (k : ℕ) :
    ∀ᶠ y in 𝓝 x, ∀ j : D.active k, y ∈ (D.wall j).support ↔
      ∃ hj : x ∈ (D.wall j).support, y - x ∈ ((D.wall j).tangentAt x hj).support := by
  simpa only [DirectedWall.tangentAt_support] using
    eventually_forall_mem_iff_sub_mem_posTangentConeAt
    (fun j : D.active k => (D.wall j).support) (fun j => (D.wall j).isConvexPolyhedron) x

/-- At each cutoff, translation identifies the actual singular supports of the diagram
and its tangent diagram on a neighbourhood of the base point. -/
theorem eventually_mem_singularSupport_tangentAt_iff (k : ℕ) :
    ∀ᶠ y in 𝓝 x,
      y ∈ singularSupport (fun j : D.active k => (D.wall j).support) ↔
        y - x ∈ singularSupport (fun j : (D.tangentAt x).active k =>
          ((D.tangentAt x).wall j).support) := by
  have := h.finiteDimensional
  let r : {j : D.active k | x ∈ (D.wall j).support} ≃ (D.tangentAt x).active k :=
    { toFun := fun j => ⟨⟨j.1.1, j.2⟩, (D.mem_active_tangentAt x k _).mpr j.1.2⟩
      invFun := fun j => ⟨⟨j.1.1, (D.mem_active_tangentAt x k _).mp j.2⟩, j.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsing : singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support) = singularSupport
        (fun j : {j : D.active k | x ∈ (D.wall j).support} =>
          posTangentConeAt (D.wall j.1).support x) := by
    simpa using (ContinuousAffineEquiv.refl ℝ V).singularSupport_image r
      (fun j => by simp [r])
  filter_upwards [eventually_mem_singularSupport_iff_sub_mem_posTangentConeAt
    (fun j : D.active k => (D.wall j).support)
    (fun j => (D.wall j).isConvexPolyhedron) x] with y hy
  rwa [hsing]

/-- Positive rescaling preserves and reflects singularity in the tangent diagram. -/
@[simp↓]
theorem smul_mem_singularSupport_tangentAt_iff (k : ℕ) {t : ℝ} (ht : 0 < t) (v : V) :
    t • v ∈ singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support) ↔
        v ∈ singularSupport (fun j : (D.tangentAt x).active k =>
          ((D.tangentAt x).wall j).support) := by
  simpa only [tangentAt_wall, DirectedWall.tangentAt_support] using
    smul_mem_singularSupport_posTangentConeAt_iff
      (fun j : (D.tangentAt x).active k => (D.wall j.1.1).support) x ht v

/-- On a bounded set of tangent displacements, the singular-support comparison holds
uniformly for every sufficiently small positive scaling factor. -/
theorem eventually_forall_mem_singularSupport_add_smul_iff (k : ℕ) {K : Set V}
    (hK : Bornology.IsBounded K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ v ∈ K,
      x + t • v ∈ singularSupport (fun j : D.active k => (D.wall j).support) ↔
        v ∈ singularSupport (fun j : (D.tangentAt x).active k =>
          ((D.tangentAt x).wall j).support) := by
  have hlocal := D.eventually_mem_singularSupport_tangentAt_iff (x := x) k
  have huniform := eventually_singleton_add_smul_subset (𝕜 := ℝ) hK hlocal
  filter_upwards [huniform.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
  intro v hv
  have hcompare := ht (Set.add_mem_add (Set.mem_singleton x) (Set.smul_mem_smul_set hv))
  simp only [Set.mem_ofPred_eq, add_sub_cancel_left] at hcompare
  exact hcompare.trans (D.smul_mem_singularSupport_tangentAt_iff k htpos v)

/-- Near `x`, a regular point has regular displacement for the tangent diagram, whose
combined labels in every crossing direction agree with those of the original diagram.
Walls active at the cutoff but missing `x` contribute nothing, and repeated or coincident
indexed walls through `x` keep their separate factors. -/
theorem eventually_combinedLabel_tangentAt (k : ℕ) :
    ∀ᶠ y in 𝓝 x, ∀ (hy : y ∉ singularSupport (fun j : D.active k => (D.wall j).support)),
      ∃ hy' : y - x ∉ singularSupport (fun j : (D.tangentAt x).active k =>
        ((D.tangentAt x).wall j).support), ∀ v : V,
      D.combinedLabel k y v hy = (D.tangentAt x).combinedLabel k (y - x) v hy' := by
  classical
  filter_upwards [D.eventually_forall_mem_support_iff k,
    D.eventually_mem_singularSupport_tangentAt_iff k] with y hyS hyreg hy
  have hy' := fun ht => hy (hyreg.mpr ht)
  refine ⟨hy', fun v => ?_⟩
  let l : List ((D.tangentAt x).active k) :=
    (Set.toFinite {j : (D.tangentAt x).active k |
      y - x ∈ ((D.tangentAt x).wall j).support}).toFinset.toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hm : ∀ j, j ∈ l ↔ y - x ∈ ((D.tangentAt x).wall j).support := by simp [l]
  let e : (D.tangentAt x).active k → D.active k := fun j =>
    ⟨j.1.1, (D.mem_active_tangentAt x k j.1).mp j.2⟩
  have he : Function.Injective e := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun j : D.active k => j.1) hab))
  rw [(D.tangentAt x).combinedLabel_eq_prod k (y - x) v hy' l hl hm,
    D.combinedLabel_eq_prod k y v hy (l.map e) (hl.map he) fun j => ?_]
  · rw [List.map_map]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, e, tangentAt_wall, DirectedWall.tangentAt_label,
      DirectedWall.tangentAt_normal]
  · rw [List.mem_map, hyS j]
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact ⟨j'.1.2, (hm j').mp hj'⟩
    · rintro ⟨hj, hjy⟩
      exact ⟨⟨⟨j.1, hj⟩, (D.mem_active_tangentAt x k ⟨j.1, hj⟩).mpr j.2⟩, (hm _).mpr hjy, rfl⟩

/-- On bounded sets, sufficiently small positive dilations identify active supports
with the incident tangent supports, uniformly in the displacement. -/
theorem eventually_forall_mem_support_add_smul_iff (k : ℕ) {K : Set V}
    (hK : Bornology.IsBounded K) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ v ∈ K, ∀ j : D.active k,
      x + t • v ∈ (D.wall j).support ↔
        ∃ hj : x ∈ (D.wall j).support, v ∈ ((D.wall j).tangentAt x hj).support := by
  simpa only [DirectedWall.tangentAt_support, exists_prop] using
    eventually_forall_add_smul_mem_iff
      (fun j : D.active k => (D.wall j).support)
      (fun j => (D.wall j).isConvexPolyhedron) x hK

/-- Dilating the position by a positive factor preserves the tangent combined label.
The crossing velocity is unchanged. -/
@[simp]
theorem combinedLabel_tangentAt_smul_pos (k : ℕ) (v w : V) {t : ℝ} (ht : 0 < t)
    (htv : t • v ∉ singularSupport (fun j : (D.tangentAt x).active k =>
      ((D.tangentAt x).wall j).support)) :
    (D.tangentAt x).combinedLabel k (t • v) w htv =
      (D.tangentAt x).combinedLabel k v w
        (fun hv => htv ((D.smul_mem_singularSupport_tangentAt_iff k ht v).mpr hv)) := by
  refine (D.tangentAt x).combinedLabel_eq_of_incident_iff_of_pos_iff htv
    (fun hv => htv ((D.smul_mem_singularSupport_tangentAt_iff k ht v).mpr hv))
    (fun j => ?_) (fun _ _ => Iff.rfl)
  exact (D.wall j.1.1).smul_mem_tangentAt_support_iff j.1.2 ht

end Mei.DirectedDiagram
