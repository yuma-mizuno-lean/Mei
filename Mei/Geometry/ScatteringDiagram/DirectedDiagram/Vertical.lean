/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Affine.Generic
public import Mei.Geometry.Affine.Codimension
import Mei.Algebra.Group.Hom.Int

/-!
# Regular vertical crossings in the zero slice

At any finite cutoff, a directed diagram in a space with one auxiliary lattice
coordinate admits regular vertical crossings at the zero slice above generic base
endpoints: such a point is outside the singular support, and every wall whose
affine span contains it is transverse to the vertical direction. The statement
allows arbitrary supports and repeated indexed walls; it needs neither consistency
nor a classification of the wall labels.

We pull the finite codimension-two cover of `TauCeti.singularSupport` and the spans
of vertically tangent walls back to the zero slice. Each pullback is a proper affine
subspace of the base, so these pullbacks form an `ExceptionalArrangement`. This
supplies actual regular germs for the coefficient extraction of module probes; the
geometric argument follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

open TauCeti (singularSupport exists_finite_singularSupport_cover)


public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V E ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ (Λ × ℤ)} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) (h.prod h') H ι)

/-- Outside a finite arrangement of base endpoints, the zero-slice point over an
endpoint is regular, and every wall whose affine span contains it is transverse to
the vertical direction. The auxiliary real space can be any integral lattice model
of the added coordinate. -/
theorem exists_regular_vertical_points (k : ℕ) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      (Q, (0 : E)) ∉ singularSupport (fun a : D.active k => (D.wall a).support) ∧
        ∀ a : D.active k, (Q, (0 : E)) ∈ affineSpan ℝ (D.wall a).support →
          (h.prod h').realCharacter (D.wall a).normal (0, j 1) ≠ 0 := by
  classical
  let := h.finiteDimensional
  let := h'.finiteDimensional
  -- The zero slice has codimension one, so singular-cover members pull back properly.
  let f : V →ₗ[ℝ] V × E := LinearMap.inl ℝ V E
  have hf (x : V) : f x = (x, 0) := rfl
  have hrank : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ V :=
    LinearMap.finrank_range_of_inj LinearMap.inl_injective
  have hE : Module.finrank ℝ E = 1 := by
    rw [← h'.finrank_eq, Module.finrank_self]
  let := Fintype.ofFinite (D.active k)
  obtain ⟨S, hcover, hdim⟩ := exists_finite_singularSupport_cover
    (fun a : D.active k => (D.wall a).support)
    (fun a => (D.wall a).isConvexPolyhedron) (fun a => (D.wall a).finrank_direction_add_one)
  have hproper (B : AffineSubspace ℝ (V × E)) (hB : B ∈ S) :
      B.comap f.toAffineMap ≠ ⊤ := by
    apply B.comap_ne_top_of_finrank_lt f.toAffineMap
    have hb := hdim B hB
    simp only [Module.finrank_prod, hE] at hb
    rw [LinearMap.toAffineMap_linear, hrank]
    omega
  -- A vertically tangent wall cannot contain the entire zero slice: its normal
  -- would vanish on the base lattice and on the auxiliary generator.
  let T := (Finset.univ : Finset (D.active k)).filter fun a : D.active k =>
    (h.prod h').realCharacter (D.wall a).normal (0, j 1) = 0
  have htangent (a : D.active k) (ha : a ∈ T) :
      (affineSpan ℝ (D.wall a).support).comap f.toAffineMap ≠ ⊤ := by
    intro he
    let B := affineSpan ℝ (D.wall a).support
    have hmem (x : V) : f x ∈ B := by
      have hx : x ∈ B.comap f.toAffineMap := by rw [he]; trivial
      exact hx
    have hz (x : V) :
        (h.prod h').realCharacter (D.wall a).normal (f x) = 0 := by
      have hv := B.vsub_mem_direction (hmem x) (hmem 0)
      rw [(D.wall a).direction_support, LinearMap.mem_ker] at hv
      simpa only [map_zero, vsub_eq_sub, sub_zero] using hv
    apply (D.wall a).normal_ne_zero
    ext n
    obtain ⟨v, l⟩ := n
    have hbase := hz (i v)
    have hvertical := (Finset.mem_filter.mp ha).2
    have hb : (D.wall a).normal (v, 0) = 0 := by
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (v, 0)
      simp only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero] at heval
      rw [hf] at hbase
      exact_mod_cast heval.symm.trans hbase
    have hl : (D.wall a).normal (0, 1) = 0 := by
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (0, 1)
      simp only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero] at heval
      exact_mod_cast heval.symm.trans hvertical
    simpa [hb, hl] using ((D.wall a).normal.apply_prod_int v l)
  refine ⟨⟨S.image (fun B => B.comap f.toAffineMap) ∪
      T.image (fun a : D.active k => (affineSpan ℝ (D.wall a).support).comap f.toAffineMap), by
      intro B hB
      rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
        exact hproper C hC
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hB
        exact htangent a ha⟩, fun Q hQ => ⟨fun hs => ?_, fun a ha hv => ?_⟩⟩
  · obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact ExceptionalArrangement.isGeneric_iff.mp hQ (C.comap f.toAffineMap)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)) hxC
  · exact ExceptionalArrangement.isGeneric_iff.mp hQ
      ((affineSpan ℝ (D.wall a).support).comap f.toAffineMap)
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩))
      ha

end Mei.DirectedDiagram
