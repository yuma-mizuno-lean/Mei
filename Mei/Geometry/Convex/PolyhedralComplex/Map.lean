/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Map
public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.Rational.Map

/-!
# Integral affine transport of finite polyhedral complexes

Transport every actual cell carrier by an integral affine equivalence. Exposure
is preserved and reflected by composing with the inverse linear part, so all
nonempty faces remain cells. Rational normals are transported by the existing
presentation API; translation vectors and affine offsets may be arbitrary.
Mathlib's dimension invariance under linear equivalences also identifies exact
cell codimensions and the wall carriers of the image complex.
-/

public section

namespace TauCeti

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Integral affine equivalences preserve and reflect nonempty faces. -/
theorem isPolyhedralFace_image_iff {P F : Set V} (e : TauCeti.Toric.IntegralAffineEquiv h h') :
    IsPolyhedralFace (e '' P) (e '' F) ↔ IsPolyhedralFace P F := by
  constructor
  · intro hF
    have hback := hF.image e.symm
    have hP := e.symm_image_image P
    have hFset := e.symm_image_image F
    rwa [hP, hFset] at hback
  · exact fun hF => hF.image e

namespace FinitePolyhedralComplex

/-- Cell transport is the finite image of the original cell carriers. -/
@[simp]
theorem image_cells (C : FinitePolyhedralComplex h) (e : TauCeti.Toric.IntegralAffineEquiv h h') :
    (C.image e).cells = C.cells.image (fun P => e '' P) := by
  classical
  ext P
  rw [mem_cells_image, Finset.mem_image]

variable {N'' U : Type*} [AddCommGroup N''] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i'' : N'' →+ U} {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- Transporting by an equivalence and its inverse recovers the complex. -/
@[simp]
theorem image_symm (C : FinitePolyhedralComplex h) (e : TauCeti.Toric.IntegralAffineEquiv h h') :
    (C.image e).image e.symm = C := by
  rw [image_trans]
  simp

/-- The bijection from original walls to their actual affine image carriers. -/
noncomputable def wallImageEquiv (C : FinitePolyhedralComplex h)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') : C.walls ≃ (C.image e).walls :=
  Equiv.ofBijective
    (fun P => ⟨e '' (P : Set V), (C.mem_cellsOfCodimension_image e 1 _).mpr
      ⟨P, P.property, rfl⟩⟩)
    ⟨fun P Q he => Subtype.ext (e.toAffineEquiv.injective.image_injective
        (congrArg Subtype.val he)),
      fun Q => by
        obtain ⟨P, hP, hPQ⟩ := (C.mem_cellsOfCodimension_image e 1 Q).mp Q.property
        exact ⟨⟨P, hP⟩, Subtype.ext hPQ⟩⟩

@[simp]
theorem wallImageEquiv_coe (C : FinitePolyhedralComplex h)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') (P : C.walls) :
    (C.wallImageEquiv e P : Set W) = e '' (P : Set V) := (rfl)

/-- The inverse wall bijection takes the inverse image carrier. -/
@[simp]
theorem wallImageEquiv_symm_coe (C : FinitePolyhedralComplex h)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') (Q : (C.image e).walls) :
    ((C.wallImageEquiv e).symm Q : Set V) = e.symm '' (Q : Set W) := by
  have he := C.wallImageEquiv_coe e ((C.wallImageEquiv e).symm Q)
  rw [Equiv.apply_symm_apply] at he
  have hi := congrArg (fun P : Set W => e.symm '' P) he
  simpa only [TauCeti.Toric.IntegralAffineEquiv.symm_image_image] using hi.symm

end FinitePolyhedralComplex

end TauCeti
