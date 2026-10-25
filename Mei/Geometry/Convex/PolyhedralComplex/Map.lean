/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

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

namespace Mei

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- Integral affine equivalences preserve nonempty polyhedral faces. -/
theorem IsPolyhedralFace.image {P F : Set V} (hF : IsPolyhedralFace P F)
    (e : Toric.IntegralAffineEquiv h h') : IsPolyhedralFace (e '' P) (e '' F) := by
  obtain ⟨hne, hex⟩ := isPolyhedralFace_iff.mp hF
  exact isPolyhedralFace_iff.mpr ⟨hne.image e, hex.image_integralAffineEquiv e⟩

/-- Integral affine equivalences preserve and reflect nonempty faces. -/
theorem isPolyhedralFace_image_iff {P F : Set V} (e : Toric.IntegralAffineEquiv h h') :
    IsPolyhedralFace (e '' P) (e '' F) ↔ IsPolyhedralFace P F := by
  constructor
  · intro hF
    have hback := hF.image e.symm
    have hP := e.symm_image_image P
    have hFset := e.symm_image_image F
    rwa [hP, hFset] at hback
  · exact fun hF => hF.image e

namespace FinitePolyhedralComplex

/-- Transport the finite collection of actual cells by an integral affine equivalence. -/
noncomputable def image (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    FinitePolyhedralComplex h' := by
  classical
  refine ⟨C.cells.image (fun P => e '' P), ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact (C.nonempty Q hQ).image e
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact (C.rational Q hQ).image e
  · intro P hP F hF
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hFne, hFex⟩ := isPolyhedralFace_iff.mp hF
    have hback : IsExposed ℝ Q (e.symm '' F) := by
      have hh := hFex.image_integralAffineEquiv e.symm
      have heq := e.symm_image_image Q
      rwa [heq] at hh
    have hmem := C.face_closed Q hQ (e.symm '' F)
      (isPolyhedralFace_iff.mpr ⟨hFne.image e.symm, hback⟩)
    apply Finset.mem_image.mpr
    refine ⟨e.symm '' F, hmem, ?_⟩
    exact e.image_symm_image F
  · intro P hP Q hQ hne
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hQ
    have heq : e '' (P₀ ∩ Q₀) = e '' P₀ ∩ e '' Q₀ :=
      Set.image_inter e.toAffineEquiv.injective
    have hbase : (P₀ ∩ Q₀).Nonempty := by
      rw [← heq] at hne
      obtain ⟨y, x, hx, _⟩ := hne
      exact ⟨x, hx⟩
    have hh := (C.inter_face P₀ hP₀ Q₀ hQ₀ hbase).image_integralAffineEquiv e
    rwa [heq] at hh

/-- Cell transport is the finite image of the original cell carriers. -/
@[simp]
theorem image_cells (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    (C.image e).cells = C.cells.image (fun P => e '' P) := by
  classical
  rfl

/-- A transported cell is exactly the image of one original cell. -/
theorem mem_cells_image {C : FinitePolyhedralComplex h} {e : Toric.IntegralAffineEquiv h h'}
    {P : Set W} : P ∈ (C.image e).cells ↔ ∃ Q ∈ C.cells, e '' Q = P := by
  classical
  rw [image_cells, Finset.mem_image]

/-- The support of the transported complex is exactly the affine image of its support. -/
@[simp]
theorem support_image (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    (C.image e).support = e '' C.support := by
  ext x
  simp only [mem_support, mem_cells_image, Set.mem_image]
  aesop

/-- Transport by the integral affine identity recovers the original complex. -/
@[simp]
theorem image_refl (C : FinitePolyhedralComplex h) :
    C.image (Toric.IntegralAffineEquiv.refl h) = C := by
  apply ext
  simp [image_cells]

variable {N'' U : Type*} [AddCommGroup N''] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i'' : N'' →+ U} {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- Transport by successive equivalences agrees with transport by their composition. -/
theorem image_trans (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (f : Toric.IntegralAffineEquiv h' h'') :
    (C.image e).image f = C.image (e.trans f) := by
  classical
  apply ext
  rw [image_cells, image_cells, image_cells, Finset.image_image]
  congr 1
  funext P
  dsimp only [Function.comp_apply]
  rw [Set.image_image]
  congr 1
  funext x
  simp

/-- Transporting by an equivalence and its inverse recovers the complex. -/
@[simp]
theorem image_symm (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    (C.image e).image e.symm = C := by
  rw [image_trans]
  simp

/-- Integral affine transport preserves cellwise weak refinement. -/
theorem IsWeakRefinement.image {C D : FinitePolyhedralComplex h} (hCD : C.IsWeakRefinement D)
    (e : Toric.IntegralAffineEquiv h h') : (C.image e).IsWeakRefinement (D.image e) := by
  rw [isWeakRefinement_iff] at hCD ⊢
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := mem_cells_image.mp hP
  obtain ⟨R, hR, hQR⟩ := hCD Q hQ
  exact ⟨e '' R, mem_cells_image.mpr ⟨R, hR, rfl⟩, Set.image_mono hQR⟩

/-- Integral affine transport preserves subdivisions and their exact support equality. -/
theorem IsSubdivision.image {C D : FinitePolyhedralComplex h} (hCD : C.IsSubdivision D)
    (e : Toric.IntegralAffineEquiv h h') : (C.image e).IsSubdivision (D.image e) := by
  obtain ⟨href, hsupport⟩ := isSubdivision_iff.mp hCD
  apply isSubdivision_iff.mpr
  exact ⟨href.image e, by rw [support_image, support_image, hsupport]⟩

/-- Affine transport preserves every exact ambient cell codimension. -/
theorem mem_cellsOfCodimension_image (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (k : ℕ) (Q : Set W) :
    Q ∈ (C.image e).cellsOfCodimension k ↔
      ∃ P ∈ C.cellsOfCodimension k, e '' P = Q := by
  have hd (P : Set V) : Module.finrank ℝ (affineSpan ℝ (e '' P)).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
    have he : (affineSpan ℝ (e '' P)).direction =
        ((affineSpan ℝ P).direction).map e.toAffineEquiv.linear.toLinearMap := by
      simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe] using
        e.toAffineEquiv.toAffineMap.direction_affineSpan_image P
    rw [he, e.toAffineEquiv.linear.finrank_map_eq]
  have hv := e.toAffineEquiv.linear.finrank_eq
  simp only [mem_cellsOfCodimension, mem_cells_image]
  constructor
  · rintro ⟨⟨P, hP, rfl⟩, hdim⟩
    exact ⟨P, ⟨hP, by rwa [hd, ← hv] at hdim⟩, rfl⟩
  · rintro ⟨P, ⟨hP, hdim⟩, rfl⟩
    exact ⟨⟨P, hP, rfl⟩, by rw [hd, ← hv]; exact hdim⟩

/-- The bijection from original walls to their actual affine image carriers. -/
noncomputable def wallImageEquiv (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') : C.walls ≃ (C.image e).walls :=
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
    (e : Toric.IntegralAffineEquiv h h') (P : C.walls) :
    (C.wallImageEquiv e P : Set W) = e '' (P : Set V) := (rfl)

/-- The inverse wall bijection takes the inverse image carrier. -/
@[simp]
theorem wallImageEquiv_symm_coe (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (Q : (C.image e).walls) :
    ((C.wallImageEquiv e).symm Q : Set V) = e.symm '' (Q : Set W) := by
  have he := C.wallImageEquiv_coe e ((C.wallImageEquiv e).symm Q)
  rw [Equiv.apply_symm_apply] at he
  have hi := congrArg (fun P : Set W => e.symm '' P) he
  simpa only [Mei.Toric.IntegralAffineEquiv.symm_image_image] using hi.symm

end FinitePolyhedralComplex

end Mei
