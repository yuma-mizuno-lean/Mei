/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Filling.Joint

/-!
# Meridian relations for continuous fillings in open regions

For a finite polyhedral complex covering its ambient space, a continuous square
with admissible affine sides has boundary word in the normal closure of the
joint meridians in any open region containing the filling. The region need not
be convex or simply connected. The filling may pass through joints and through
strata of higher codimension; no general-position hypothesis is imposed on it.

This is the continuous-filling relation needed to compare polygonal transports
in an open region. It keeps the actual boundary edges fixed. We use
`Quiver.Path.crossingWord_mem_normalClosure_jointMeridianWords` in small convex
balls contained in the region, and assemble those local relations using
`FinitePolyhedralComplex.crossingWord_boundary_mem_of_cover`. The latter
perturbs only interior vertices of a subdivision of the filling.
-/

public noncomputable section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h) (hC : C.support = univ)
  (ν : C.walls → V →ₗ[ℝ] ℝ)
  (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)

include hC hν

/-- A continuous square filled inside an open region gives a relation generated
by the joint meridians in that region. Its affine admissible boundary is fixed,
and the filling is allowed to meet every stratum of the complex. -/
theorem crossingWord_boundary_mem_normalClosure_jointMeridianWords
    {U : Set V} (hU : IsOpen U)
    (x : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)))
    (e₁ : ∀ b : Fin 2, x (0, b) ⟶ x (1, b))
    (e₂ : ∀ a : Fin 2, x (a, 0) ⟶ x (a, 1))
    (f : C(↥unitInterval × ↥unitInterval, V))
    (hf₁ : ∀ (b : Fin 2) (s : unitInterval),
      f (s, if b = 0 then 0 else 1) =
        AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ))
    (hf₂ : ∀ (a : Fin 2) (s : unitInterval),
      f (if a = 0 then 0 else 1, s) =
        AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ))
    (hfU : ∀ z, f z ∈ U) :
    ((((e₁ 0).toPath.cons (e₂ 1)).cons (Quiver.reverse (e₁ 1))).cons
      (Quiver.reverse (e₂ 0))).crossingWord ν ∈
        Subgroup.normalClosure (C.jointMeridianWords ν U) := by
  -- Small balls admit the convex-region meridian theorem, even at higher strata.
  choose r hr hrU using fun z => Metric.isOpen_iff.mp hU (f z) (hfU z)
  apply C.crossingWord_boundary_mem_of_cover ν hν _ x e₁ e₂ f hf₁ hf₂
    (fun z => Metric.ball (f z) (r z)) (fun _ => Metric.isOpen_ball)
    (fun z => ⟨z, Metric.mem_ball_self (hr z)⟩)
  intro z y p hp
  exact Subgroup.normalClosure_mono (C.jointMeridianWords_mono ν (hrU z))
    (p.crossingWord_mem_normalClosure_jointMeridianWords hC ν hν
      Metric.isOpen_ball (convex_ball _ _) hp)

/-- Killing the meridians in a region makes the two boundary routes of every
continuous filled square have equal images. This applies to arbitrary groups,
without commutativity or endpoint independence on the whole region. -/
theorem map_crossingWord_routes_eq_of_filling
    {H : Type*} [Group H] (φ : FreeGroup C.walls →* H)
    {U : Set V} (hU : IsOpen U)
    (hφ : ∀ g ∈ C.jointMeridianWords ν U, φ g = 1)
    (x : Fin 2 × Fin 2 → WallComplement (fun P : C.walls => (P : Set V)))
    (e₁ : ∀ b : Fin 2, x (0, b) ⟶ x (1, b))
    (e₂ : ∀ a : Fin 2, x (a, 0) ⟶ x (a, 1))
    (f : C(↥unitInterval × ↥unitInterval, V))
    (hf₁ : ∀ (b : Fin 2) (s : unitInterval),
      f (s, if b = 0 then 0 else 1) =
        AffineMap.lineMap (x (0, b)).val (x (1, b)).val (s : ℝ))
    (hf₂ : ∀ (a : Fin 2) (s : unitInterval),
      f (if a = 0 then 0 else 1, s) =
        AffineMap.lineMap (x (a, 0)).val (x (a, 1)).val (s : ℝ))
    (hfU : ∀ z, f z ∈ U) :
    φ (((e₁ 0).toPath.cons (e₂ 1)).crossingWord ν) =
      φ (((e₂ 0).toPath.cons (e₁ 1)).crossingWord ν) := by
  have hm := Subgroup.normalClosure_le_normal
    (N := φ.ker) (fun g hg => MonoidHom.mem_ker.mpr (hφ g hg))
    (C.crossingWord_boundary_mem_normalClosure_jointMeridianWords hC ν hν
      hU x e₁ e₂ f hf₁ hf₂ hfU)
  have he := MonoidHom.mem_ker.mp hm
  simp only [Quiver.Path.crossingWord_cons, Quiver.Hom.toPath,
    Quiver.Path.crossingWord_nil, mul_one, C.segmentCrossingWord_reverse ν hν,
    map_mul, map_inv] at he ⊢
  have he' : (φ (C.segmentCrossingWord ν (e₁ 1)) *
      φ (C.segmentCrossingWord ν (e₂ 0)))⁻¹ *
        (φ (C.segmentCrossingWord ν (e₂ 1)) *
          φ (C.segmentCrossingWord ν (e₁ 0))) = 1 := by
    simpa only [mul_inv_rev, mul_assoc] using he
  exact (inv_mul_eq_one.mp he').symm

end Mei.FinitePolyhedralComplex
