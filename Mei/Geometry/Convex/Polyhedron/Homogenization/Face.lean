/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Homogenization.Slice
public import Mei.Geometry.Convex.Polyhedron.Homogenization.Inequalities
public import Mei.Geometry.Convex.Polyhedron.Face
public import Mathlib.Geometry.Convex.Cone.Face.Lattice
public import TauCeti.Geometry.Convex.Cone.Face.Exposed

/-!
# Faces and actual homogenization

Nonempty exposed faces of a polyhedron correspond to the faces of its actual
closed homogenization that meet height one. The correspondence sends a face to
its carrier-defined homogenization and takes the height-one slice in reverse.
Faces entirely at height zero are excluded. Lineality is allowed; finite
generation and finite dimensionality are not assumed.
-/

public section

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Mei.Convex

/-- At height one, the existing homogenized functional recovers the affine row. -/
theorem homogenizedInequality_one (g : V →ᴬ[ℝ] ℝ) (x : V) :
    homogenizedInequality g (x, (1 : ℝ)) = g x := by
  have h := g.map_vadd (0 : V) x
  simpa [homogenizedInequality_apply] using h.symm

/-- A nonpositive affine support remains nonpositive throughout the actual
closed homogenization, including at height zero. -/
theorem homogenizedInequality_nonpos {P : Set V} (g : V →ᴬ[ℝ] ℝ)
    (hg : ∀ x ∈ P, g x ≤ 0) {z : V × ℝ} (hz : z ∈ homogenization P) :
    homogenizedInequality g z ≤ 0 := by
  apply closure_minimal (s :=
      (PointedCone.hull ℝ ((fun p : V => (p, (1 : ℝ))) '' P) : Set (V × ℝ)))
    (t := {z | homogenizedInequality g z ≤ 0}) ?_
    (isClosed_le (homogenizedInequality g).continuous continuous_const) hz
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    change homogenizedInequality g (p, 1) ≤ 0
    rw [homogenizedInequality_one]
    exact hg p hp
  | zero => simp
  | add u v hu hv iu iv =>
    change homogenizedInequality g u ≤ 0 at iu
    change homogenizedInequality g v ≤ 0 at iv
    change homogenizedInequality g (u + v) ≤ 0
    rw [map_add]
    exact add_nonpos iu iv
  | smul c w hw iw =>
    change homogenizedInequality g ((c : ℝ) • w) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos c.property iw

/-- Intersecting a closed convex base with a nonempty affine zero slice commutes
with actual homogenization, including at height zero. -/
theorem _root_.Convex.homogenization_inter_zero_eq_inf_ker {P : Set V}
    (hconv : _root_.Convex ℝ P)
    (hclosed : IsClosed P) (g : V →ᴬ[ℝ] ℝ)
    (hne : {x ∈ P | g x = 0}.Nonempty) :
    homogenization {x ∈ P | g x = 0} = homogenization P ⊓
      PointedCone.ofSubmodule (LinearMap.ker (homogenizedInequality g).toLinearMap) := by
  let D := homogenization P ⊓
    PointedCone.ofSubmodule (LinearMap.ker (homogenizedInequality g).toLinearMap)
  have hDclosed : IsClosed (D : Set (V × ℝ)) :=
    (isClosed_homogenization P).inter
      (isClosed_eq (homogenizedInequality g).continuous continuous_const)
  have hslice : {x : V | (x, (1 : ℝ)) ∈ D} = {x ∈ P | g x = 0} := by
    ext x
    change ((x, (1 : ℝ)) ∈ homogenization P ∧ homogenizedInequality g (x, 1) = 0) ↔ _
    rw [hconv.mem_homogenization_one_iff hclosed, homogenizedInequality_one]
    rfl
  have hDne : {x : V | (x, (1 : ℝ)) ∈ D}.Nonempty := by rwa [hslice]
  have hrec := D.homogenization_slice_one hDclosed
    (fun z hz => homogenization_height_nonneg hz.1) hDne
  rwa [hslice] at hrec

/-- A nonpositive affine support cuts out a genuine cone face after actual homogenization. -/
theorem _root_.Convex.homogenization_zeroFace_isFaceOf {P : Set V}
    (hconv : _root_.Convex ℝ P)
    (hclosed : IsClosed P) (g : V →ᴬ[ℝ] ℝ) (hg : ∀ x ∈ P, g x ≤ 0)
    (hne : {x ∈ P | g x = 0}.Nonempty) :
    (homogenization {x ∈ P | g x = 0}).IsFaceOf (homogenization P) := by
  rw [hconv.homogenization_inter_zero_eq_inf_ker hclosed g hne]
  have hf : ∀ z ∈ homogenization P, 0 ≤ (-(homogenizedInequality g).toLinearMap) z :=
    fun z hz => neg_nonneg.mpr (homogenizedInequality_nonpos g hg hz)
  have hface := PointedCone.isFaceOf_inf_ker hf
  have hker : LinearMap.ker (-(homogenizedInequality g).toLinearMap) =
      LinearMap.ker (homogenizedInequality g).toLinearMap := by ext z; simp
  rwa [hker] at hface

end Mei.Convex

namespace IsExposed

/-- Every nonempty exposed face of a closed convex set homogenizes to a face
of its actual closed homogenization. -/
theorem homogenization_isFaceOf {P F : Set V} (hF : IsExposed ℝ P F)
    (hconv : Convex ℝ P) (hclosed : IsClosed P) (hne : F.Nonempty) :
    (Mei.Convex.homogenization F).IsFaceOf (Mei.Convex.homogenization P) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨l, hl⟩ := hF ⟨p, hp⟩
  have hpmax : p ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by rwa [← hl]
  let g := l.toContinuousAffineMap - ContinuousAffineMap.const ℝ V (l p)
  have hg : ∀ x ∈ P, g x ≤ 0 := by
    intro x hx
    change l x - l p ≤ 0
    exact sub_nonpos.mpr (hpmax.2 x hx)
  have hzero : F = {x ∈ P | g x = 0} := by
    ext x
    rw [hl]
    constructor
    · rintro ⟨hx, hmax⟩
      refine ⟨hx, ?_⟩
      change l x - l p = 0
      exact sub_eq_zero.mpr (le_antisymm (hpmax.2 x hx) (hmax p hpmax.1))
    · rintro ⟨hx, hzero⟩
      have heq : l x = l p := sub_eq_zero.mp hzero
      exact ⟨hx, fun y hy => (hpmax.2 y hy).trans_eq heq.symm⟩
  rw [hzero]
  exact hconv.homogenization_zeroFace_isFaceOf hclosed g hg (hzero ▸ ⟨p, hp⟩)

end IsExposed

namespace PointedCone.IsFaceOf

/-- A cone face of a polyhedral homogenization has an exposed height-one slice. -/
theorem isExposed_slice_one_of_homogenization {P : Set V} {G : PointedCone ℝ (V × ℝ)}
    (hG : G.IsFaceOf (Mei.Convex.homogenization P)) (hP : TauCeti.IsConvexPolyhedron P) :
    IsExposed ℝ P {x : V | (x, (1 : ℝ)) ∈ G} := by
  have hslice : {x : V | (x, (1 : ℝ)) ∈ Mei.Convex.homogenization P} = P := by
    ext x
    exact hP.convex.mem_homogenization_one_iff hP.isClosed
  have hext := hG.isExtreme_slice_one
  rw [hslice] at hext
  have hconv : Convex ℝ {x : V | (x, (1 : ℝ)) ∈ G} :=
    G.convex.affine_preimage ((AffineMap.id ℝ V).prod (AffineMap.const ℝ V (1 : ℝ)))
  exact hext.isExposed_of_isConvexPolyhedron hP hconv

/-- Faces meeting height one are closed because they are convex extreme
subsets of a polyhedral cone. No finite-generation assumption is needed. -/
theorem isClosed_of_homogenization {P : Set V} {G : PointedCone ℝ (V × ℝ)}
    (hG : G.IsFaceOf (Mei.Convex.homogenization P)) (hP : TauCeti.IsConvexPolyhedron P)
    (hne : {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty) : IsClosed (G : Set (V × ℝ)) := by
  obtain ⟨p, hp⟩ := hne
  have hPne : P.Nonempty :=
    ⟨p, (hP.convex.mem_homogenization_one_iff hP.isClosed).mp (hG.le hp)⟩
  exact (hG.isExtreme.isConvexPolyhedron
    (Mei.Convex.isConvexPolyhedron_homogenization hP hPne) G.convex).isClosed

end PointedCone.IsFaceOf

namespace Mei.Convex

/-- Nonempty exposed faces of a polyhedron correspond, in their actual inclusion
orders, to the faces of its closed homogenization that meet height one.

The maps are actual homogenization and height-one slicing. Empty affine faces
and cone faces entirely at height zero are excluded; no salience assumption is made. -/
def nonemptyExposedFaceOrderIso {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V // F.Nonempty ∧ IsExposed ℝ P F} ≃o
      {G : (homogenization P).Face // {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty} where
  toFun F :=
    ⟨⟨homogenization F.val,
      F.property.2.homogenization_isFaceOf hP.convex hP.isClosed F.property.1⟩,
      by
        obtain ⟨p, hp⟩ := F.property.1
        exact ⟨p, mem_homogenization_one hp⟩⟩
  invFun G :=
    ⟨{x : V | (x, (1 : ℝ)) ∈ G.val}, G.property,
      G.val.isFaceOf.isExposed_slice_one_of_homogenization hP⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    exact (F.property.2.convex hP.convex).mem_homogenization_one_iff
      (F.property.2.isClosed hP.isClosed)
  right_inv G := by
    apply Subtype.ext
    apply PointedCone.Face.ext
    intro z
    change z ∈ homogenization {x : V | (x, (1 : ℝ)) ∈ G.val} ↔ z ∈ G.val.toPointedCone
    have heq := G.val.toPointedCone.homogenization_slice_one
      (G.val.isFaceOf.isClosed_of_homogenization hP G.property)
      (fun w hw => homogenization_height_nonneg (G.val.isFaceOf.le hw)) G.property
    simpa only [PointedCone.Face.mem_toPointedCone] using SetLike.ext_iff.mp heq z
  map_rel_iff' := by
    intro F F'
    change homogenization F.val ≤ homogenization F'.val ↔ F.val ⊆ F'.val
    constructor
    · intro h x hx
      exact ((F'.property.2.convex hP.convex).mem_homogenization_one_iff
        (F'.property.2.isClosed hP.isClosed)).mp (h (mem_homogenization_one hx))
    · exact homogenization_mono

/-- The order correspondence sends a face to its actual carrier-defined homogenization. -/
@[simp]
theorem nonemptyExposedFaceOrderIso_apply {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (F : {F : Set V // F.Nonempty ∧ IsExposed ℝ P F}) :
    ((nonemptyExposedFaceOrderIso hP F).val).toPointedCone = homogenization F.val :=
  Eq.trans rfl rfl

/-- The inverse order correspondence takes the exact height-one slice. -/
@[simp]
theorem nonemptyExposedFaceOrderIso_symm_apply {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (G : {G : (homogenization P).Face // {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty}) :
    ((nonemptyExposedFaceOrderIso hP).symm G).val = {x : V | (x, (1 : ℝ)) ∈ G.val} :=
  Eq.trans rfl rfl

end Mei.Convex
