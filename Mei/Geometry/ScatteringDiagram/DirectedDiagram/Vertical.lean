/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Affine.Vertical

/-!
# Regular vertical crossings in a slice

At any finite cutoff, a directed diagram in a space with two auxiliary lattice
coordinates admits regular vertical crossings above generic base endpoints.
Only finitely many heights can be singular or tangent to an incident wall.
The statement allows arbitrary supports and repeated indexed walls; it needs
neither consistency nor a classification of the wall labels.

We pull the finite codimension-two cover of `Convex.singularSupport` back to the
zero slice of the last coordinate, add the spans of vertically tangent walls,
and apply `ExceptionalArrangement.verticalProjection`. This supplies actual
regular germs for the coefficient extraction of module probes. The geometric
argument follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V E ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ρ : Γ →+ (Λ × ℤ × ℤ)} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) (h.prod h') H ι)

/-- Outside a finite arrangement of base endpoints, only finitely many heights
in the zero slice are singular or fail vertical transversality. The auxiliary
real space can be any integral lattice model of the two added coordinates. -/
theorem exists_finite_bad_vertical_heights (k : ℕ) :
    ∃ A : ExceptionalArrangement V, ∀ Q, A.IsGeneric Q →
      {y : ℝ | (Q, y • j (1, 0)) ∈
          singularSupport (fun a : D.active k => (D.wall a).support) ∨
        ∃ a : D.active k, (Q, y • j (1, 0)) ∈ (D.wall a).support ∧
          (h.prod h').realCharacter (D.wall a).normal (0, j (0, 1)) = 0}.Finite := by
  classical
  let := h.finiteDimensional
  let := h'.finiteDimensional
  -- The zero slice has codimension one, so singular-cover members pull back properly.
  let f : V × ℝ →ₗ[ℝ] V × E :=
    (LinearMap.id : V →ₗ[ℝ] V).prodMap (LinearMap.toSpanSingleton ℝ E (j (1, 0)))
  have hf (x : V × ℝ) : f x = (x.1, x.2 • j (1, 0)) := rfl
  have hj : j (1, 0) ≠ 0 := by
    intro he
    have he' := h'.injective (he.trans (map_zero j).symm)
    exact one_ne_zero (congrArg Prod.fst he')
  have hinj : Function.Injective f := by
    intro x y he
    rw [hf, hf] at he
    apply Prod.ext
    · exact (Prod.mk.inj he).1
    · exact smul_left_injective ℝ hj (Prod.mk.inj he).2
  have hrank : Module.finrank ℝ (LinearMap.range f) = Module.finrank ℝ V + 1 := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self]
  have hE : Module.finrank ℝ E = 2 := by
    rw [← h'.finrank_eq, Module.finrank_prod, Module.finrank_self]
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
  -- A vertically tangent wall cannot contain the entire zero slice: its
  -- normal would vanish on the base lattice and on both auxiliary generators.
  let T := (Finset.univ : Finset (D.active k)).filter fun a : D.active k =>
    (h.prod h').realCharacter (D.wall a).normal (0, j (0, 1)) = 0
  have htangent (a : D.active k) (ha : a ∈ T) :
      (affineSpan ℝ (D.wall a).support).comap f.toAffineMap ≠ ⊤ := by
    intro he
    let B := affineSpan ℝ (D.wall a).support
    have hmem (x : V × ℝ) : f x ∈ B := by
      have hx : x ∈ B.comap f.toAffineMap := by rw [he]; trivial
      exact hx
    have hz (x : V × ℝ) :
        (h.prod h').realCharacter (D.wall a).normal (f x) = 0 := by
      have hv := B.vsub_mem_direction (hmem x) (hmem 0)
      rw [(D.wall a).direction_support, LinearMap.mem_ker] at hv
      simpa only [map_zero, vsub_eq_sub, sub_zero] using hv
    apply (D.wall a).normal_ne_zero
    ext n
    obtain ⟨v, c, l⟩ := n
    have hbase := hz (i v, 0)
    have hheight := hz (0, 1)
    have hvertical := (Finset.mem_filter.mp ha).2
    have hb : (D.wall a).normal (v, 0, 0) = 0 := by
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (v, 0, 0)
      simp only [AddMonoidHom.coe_prodMap, Prod.map_apply, Prod.mk_zero_zero, map_zero] at heval
      rw [hf, zero_smul] at hbase
      exact_mod_cast heval.symm.trans hbase
    have hc : (D.wall a).normal (0, 1, 0) = 0 := by
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (0, 1, 0)
      simp only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero] at heval
      rw [hf, one_smul] at hheight
      exact_mod_cast heval.symm.trans hheight
    have hl : (D.wall a).normal (0, 0, 1) = 0 := by
      have heval := (h.prod h').realCharacter_apply (D.wall a).normal (0, 0, 1)
      simp only [AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero] at heval
      exact_mod_cast heval.symm.trans hvertical
    simpa [hb, hc, hl] using ((D.wall a).normal.apply_prod_int_int v c l)
  -- Project the slice arrangement and discard its remaining finitely many bad heights.
  let B : ExceptionalArrangement (V × ℝ) :=
    ⟨S.image (fun B => B.comap f.toAffineMap) ∪
      T.image (fun a : D.active k => (affineSpan ℝ (D.wall a).support).comap f.toAffineMap), by
      intro B hB
      rcases Finset.mem_union.mp hB with hB | hB
      · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
        exact hproper C hC
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hB
        exact htangent a ha⟩
  refine ⟨B.verticalProjection, fun Q hQ => ?_⟩
  apply ((B.isGeneric_verticalProjection_iff_finite Q).mp hQ).subset
  intro y hy hgood
  have hgood := ExceptionalArrangement.isGeneric_iff.mp hgood
  rcases hy with hs | ⟨a, ha, hv⟩
  · obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact hgood (C.comap f.toAffineMap)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)) hxC
  · exact hgood ((affineSpan ℝ (D.wall a).support).comap f.toAffineMap)
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩))
      (subset_affineSpan ℝ _ ha)

end Mei.DirectedDiagram
