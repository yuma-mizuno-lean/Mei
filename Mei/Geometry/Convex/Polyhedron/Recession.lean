/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic.Linarith

/-!
# Recession cones of polyhedra

The recession cone consists of vectors preserving a set under every nonnegative
translation. This definition gives the whole space for the empty set. For a
nonempty set defined by affine inequalities, its recession cone is given by the
corresponding homogeneous inequalities on their linear parts. The necessity
uses arbitrarily large parameters, supplied by the Archimedean property of ℝ.

The nonempty assumption matters for homogenization: the closed cone generated
by an empty height-one slice is the zero cone, whereas the recession cone of
the empty set is the whole space by its universal definition.
-/

public section

namespace Mei.Convex

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The directions preserving `P` under all nonnegative translations.
This forms a pointed cone even when the original set is neither convex nor closed. -/
@[expose]
def recessionCone (P : Set V) : PointedCone ℝ V where
  carrier := {v | ∀ x ∈ P, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ P}
  zero_mem' := by
    intro x hx t _
    simpa using hx
  add_mem' := by
    intro u v hu hv x hx t ht
    have h := hv (x + t • u) (hu x hx t ht) t ht
    simpa only [smul_add, add_assoc] using h
  smul_mem' := by
    intro c v hv x hx t ht
    change x + t • ((c : ℝ) • v) ∈ P
    rw [smul_smul]
    exact hv x hx (t * (c : ℝ)) (mul_nonneg ht c.property)

/-- Membership is precisely preservation of all nonnegative rays based in the set. -/
@[simp]
theorem mem_recessionCone {P : Set V} {v : V} :
    v ∈ recessionCone P ↔ ∀ x ∈ P, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ P := Iff.rfl

/-- The recession cone of the empty set is the whole space, by vacuity. -/
@[simp]
theorem recessionCone_empty : recessionCone (∅ : Set V) = ⊤ := by
  ext v
  simp [mem_recessionCone]

/-- Every vector preserves the whole ambient space. -/
@[simp]
theorem recessionCone_univ : recessionCone (Set.univ : Set V) = ⊤ := by
  ext v
  simp [mem_recessionCone]

end Algebra

section Inequalities

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

private theorem affine_apply_recession_ray (g : V →ᴬ[ℝ] ℝ) (x v : V) (t : ℝ) :
    g (x + t • v) = g x + t * g.linear v := by
  rw [add_comm x]
  have h := g.map_vadd' x (t • v)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm,
    AffineMap.toFun_eq_coe, ContinuousAffineMap.coe_toAffineMap] using h

/-- For a nonempty family-defined polyhedron, recession membership is equivalent
to the homogeneous inequalities. The index family may be infinite. -/
theorem mem_recessionCone_setOf_forall_iff {g : ι → (V →ᴬ[ℝ] ℝ)}
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) {v : V} :
    v ∈ recessionCone {x : V | ∀ i, g i x ≤ 0} ↔ ∀ i, (g i).linear v ≤ 0 := by
  constructor
  · intro hv i
    obtain ⟨x, hx⟩ := hP
    by_contra hi
    have hpos : 0 < (g i).linear v := lt_of_not_ge hi
    obtain ⟨n, hn⟩ := exists_lt_nsmul hpos (-g i x)
    have hmem := hv x hx (n : ℝ) (Nat.cast_nonneg n)
    have hle := hmem i
    rw [affine_apply_recession_ray] at hle
    simp only [nsmul_eq_mul] at hn
    linarith
  · intro hv x hx t ht i
    rw [affine_apply_recession_ray]
    exact add_nonpos (hx i) (mul_nonpos_of_nonneg_of_nonpos ht (hv i))

/-- The exact recession carrier of a nonempty affine-inequality presentation. -/
theorem recessionCone_setOf_forall_eq (g : ι → (V →ᴬ[ℝ] ℝ))
    (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    (recessionCone {x : V | ∀ i, g i x ≤ 0} : Set V) =
      {v : V | ∀ i, (g i).linear v ≤ 0} := by
  ext v
  exact mem_recessionCone_setOf_forall_iff hP

end Inequalities

section Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recession cone of a closed set is closed, as an intersection of affine
preimages of the original set. No convexity or nonemptiness is needed. -/
theorem isClosed_recessionCone {P : Set V} (hP : IsClosed P) :
    IsClosed (recessionCone P : Set V) := by
  have he : (recessionCone P : Set V) =
      ⋂ x : P, ⋂ t : {t : ℝ // 0 ≤ t}, (fun v : V => (x : V) + (t : ℝ) • v) ⁻¹' P := by
    ext v
    simp only [SetLike.mem_coe, mem_recessionCone, Set.mem_iInter, Set.mem_preimage,
      Subtype.forall]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun t =>
    hP.preimage (continuous_const.add (continuous_id.const_smul (t : ℝ)))

/-- The homogeneous inequalities for a finite affine family are themselves a
convex polyhedron. -/
theorem isConvexPolyhedron_recessionCone_setOf_forall {ι : Type*} [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    TauCeti.IsConvexPolyhedron (recessionCone {x : V | ∀ i, g i x ≤ 0} : Set V) := by
  rw [recessionCone_setOf_forall_eq g hP]
  simpa only [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousAffineMap.coe_contLinear]
    using TauCeti.isConvexPolyhedron_setOf_forall
      (fun i => (g i).contLinear.toContinuousAffineMap)

/-- Every convex polyhedron has a convex polyhedral recession cone. The empty
case has recession cone equal to the whole space. -/
theorem isConvexPolyhedron_recessionCone {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    TauCeti.IsConvexPolyhedron (recessionCone P : Set V) := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    rw [recessionCone_empty]
    exact TauCeti.isConvexPolyhedron_univ
  · obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
    exact isConvexPolyhedron_recessionCone_setOf_forall g hne

end Topology

end Mei.Convex
