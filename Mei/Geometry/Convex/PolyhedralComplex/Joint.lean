/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.Rational.Direction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Isolating neighborhoods and transverse slices at joints

At a relative interior point of a joint, a sufficiently small ball meets only
cells containing the joint and misses its relative boundary. The skeleton of
codimension at least two agrees with the joint throughout that ball. A chosen
complement to the joint direction gives a two-dimensional transverse slice
whose intersection with that skeleton is exactly the center.

The joint direction is also the common kernel of two real extensions of
integral characters. Evaluating these equations on lattice vectors gives the
integral tangent kernel used in homogeneous wall-space calculations. The two
characters can be chosen with linearly independent real extensions, by
`FinitePolyhedralComplex.exists_linearIndependent_joint_direction_eq_inf_ker`.
Contracting the equations against a transverse lattice vector gives a nonzero integral
normal to the sum of the joint direction and that vector's line.

These are the isolation and transversality conditions needed before constructing
small polygonal meridians: any filled polygon in the ball and slice misses every
other joint and the boundary of the chosen joint. The result constructs the slice
and neighborhood, without assuming a transverse plane as input. Cells may be
unbounded or have lineality.

The construction uses the common-face incidence theorem
`FinitePolyhedralComplex.eventually_subset_of_mem_cell`, Mathlib's
`Submodule.exists_isCompl`, and
`AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl`.
-/

public section

open Set Filter Topology

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The tangent space of a joint is the common kernel of two integral
characters extended to the ambient real space. -/
theorem exists_joint_direction_eq_inf_ker (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) :
    ∃ f g : N →+ ℤ, (affineSpan ℝ J).direction =
      (h.realCharacter f).ker ⊓ (h.realCharacter g).ker := by
  obtain ⟨hJC, hdim⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  obtain ⟨f, g, hfg⟩ := (C.rational J hJC).exists_direction_eq_inf_ker
    (C.nonempty J hJC) hdim
  exact ⟨f.toAddMonoidHom, g.toAddMonoidHom, hfg⟩

/-- The direction of an actual joint is cut out by two independent integral
characters. The joint need not contain any lattice point, since its offsets
may be arbitrary real numbers. -/
theorem exists_linearIndependent_joint_direction_eq_inf_ker
    (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) :
    ∃ f g : N →+ ℤ, LinearIndependent ℝ ![h.realCharacter f, h.realCharacter g] ∧
      (affineSpan ℝ J).direction = (h.realCharacter f).ker ⊓ (h.realCharacter g).ker := by
  obtain ⟨hcell, hdim⟩ := (C.mem_cellsOfCodimension 2 J).mp hJ
  obtain ⟨m, hlin, hdir⟩ := (C.rational J hcell).exists_direction_eq_iInf_ker
    (C.nonempty J hcell) hdim
  have heq : (fun j => h.realCharacter (m j).toAddMonoidHom) =
      ![h.realCharacter (m 0).toAddMonoidHom, h.realCharacter (m 1).toAddMonoidHom] := by
    ext j
    fin_cases j <;> rfl
  refine ⟨(m 0).toAddMonoidHom, (m 1).toAddMonoidHom, heq ▸ hlin, ?_⟩
  rw [hdir]
  ext v
  simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, Fin.forall_fin_two]

/-- At a degree transverse to a joint, contracting two integral joint equations
gives a nonzero integral normal. Its real kernel is exactly the joint direction
plus the line through that degree. -/
theorem exists_joint_transverse_normal (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) (v : N) (hv : i v ∉ (affineSpan ℝ J).direction) :
    ∃ f g : N →+ ℤ,
      (affineSpan ℝ J).direction = (h.realCharacter f).ker ⊓ (h.realCharacter g).ker ∧
      f v • g - g v • f ≠ 0 ∧
      (h.realCharacter (f v • g - g v • f)).ker =
        (affineSpan ℝ J).direction ⊔ ℝ ∙ i v := by
  let := h.finiteDimensional
  obtain ⟨f, g, hfg⟩ := C.exists_joint_direction_eq_inf_ker hJ
  have hreal : h.realCharacter (f v • g - g v • f) =
      h.realCharacter f (i v) • h.realCharacter g -
        h.realCharacter g (i v) • h.realCharacter f := by
    ext w
    simp
  have hker : (h.realCharacter (f v • g - g v • f)).ker =
      (affineSpan ℝ J).direction ⊔ ℝ ∙ i v := by
    rw [hreal, LinearMap.ker_apply_smul_sub_apply_smul _ _ (hfg ▸ hv), ← hfg]
  refine ⟨f, g, hfg, ?_, hker⟩
  intro he
  have htop : (affineSpan ℝ J).direction ⊔ ℝ ∙ i v = ⊤ := by
    simpa only [he, map_zero, LinearMap.ker_zero] using hker.symm
  have hdim := ((C.mem_cellsOfCodimension 2 J).mp hJ).2
  have hsup := Submodule.finrank_sup_span_singleton hv
  rw [htop, finrank_top] at hsup
  omega

/-- Every relative interior point of a joint admits an isolating ball and a
two-dimensional complementary slice. Within that slice and ball, the whole
codimension-at-least-two skeleton consists of the center alone. The ball misses
the joint's relative boundary and every other joint, and meets only cells containing the joint. -/
theorem exists_isolating_ball_joint (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) {x : V} (hx : x ∈ intrinsicInterior ℝ J) :
    ∃ (r : ℝ) (W : Submodule ℝ V), 0 < r ∧
      IsCompl (affineSpan ℝ J).direction W ∧ Module.finrank ℝ W = 2 ∧
      (Metric.ball x r ∩ (AffineSubspace.mk' x W : Set V)) ∩
        (C.codimensionAtLeast 2).support = {x} ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ J) ∧
      (∀ Q ∈ C.joints, Q ≠ J → Disjoint (Metric.ball x r) Q) ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → J ⊆ Q := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hskeleton, hfrontier, hother, hcells⟩ := C.exists_isolating_ball hJ hx
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (affineSpan ℝ J).direction
  have hdimJ := ((C.mem_cellsOfCodimension 2 J).mp hJ).2
  have hdimW := Submodule.finrank_add_eq_of_isCompl hW
  have hxJ := intrinsicInterior_subset hx
  have hxA := subset_affineSpan ℝ J hxJ
  have hxW : x ∈ (AffineSubspace.mk' x W : Set V) := AffineSubspace.self_mem_mk' x W
  obtain ⟨p, hp⟩ := AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl
    (s₁ := affineSpan ℝ J) (s₂ := AffineSubspace.mk' x W) ⟨x, hxA⟩ ⟨x, hxW⟩
    (by simpa only [AffineSubspace.direction_mk'] using hW)
  have hpx : x = p := Set.mem_singleton_iff.mp (hp ▸ ⟨hxA, hxW⟩)
  subst p
  refine ⟨r, W, hr, hW, by omega, ?_, hfrontier, hother, hcells⟩
  ext y
  constructor
  · rintro ⟨⟨hyball, hyW⟩, hys⟩
    have hyJ : y ∈ Metric.ball x r ∩ J := hskeleton ▸ ⟨hyball, hys⟩
    exact hp ▸ ⟨subset_affineSpan ℝ J hyJ.2, hyW⟩
  · intro hxy
    have hxy : y = x := Set.mem_singleton_iff.mp hxy
    subst y
    have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    have hxs : x ∈ Metric.ball x r ∩ (C.codimensionAtLeast 2).support :=
      hskeleton.symm ▸ ⟨hxball, hxJ⟩
    exact ⟨⟨hxball, hxW⟩, hxs.2⟩

section JointGeometry

open Set Module Mei.Convex

variable {C : FinitePolyhedralComplex h} {J : Set V}

/-- Linear functionals vanishing on the direction of a joint form a pencil. Given one
nonzero such functional `φ`, the affine function `w ↦ φ q - φ w` and a second affine
function generate, up to constants, every such functional. -/
theorem exists_pencil_of_joint (hJ : J ∈ C.joints) (q : V) {φ : V →ₗ[ℝ] ℝ}
    (hφ : ∀ d ∈ (affineSpan ℝ J).direction, φ d = 0) (hφ0 : φ ≠ 0) :
    ∃ ℓ m : V →ᵃ[ℝ] ℝ, (∀ w, ℓ w = φ q - φ w) ∧
      ∀ g : V →ₗ[ℝ] ℝ, (∀ d ∈ (affineSpan ℝ J).direction, g d = 0) →
        ∃ α β : ℝ, ∀ w, g w - g q = α * ℓ w + β * m w := by
  -- Functionals vanishing on the joint direction are combinations of its equations.
  obtain ⟨f₁, f₂, hdir⟩ := C.exists_joint_direction_eq_inf_ker hJ
  have hcomb (g : V →ₗ[ℝ] ℝ) (hg : ∀ d ∈ (affineSpan ℝ J).direction, g d = 0) :
      ∃ c₁ c₂ : ℝ, ∀ v, g v = c₁ * h.realCharacter f₁ v + c₂ * h.realCharacter f₂ v := by
    have hmem := mem_span_of_iInf_ker_le_ker (L := ![h.realCharacter f₁, h.realCharacter f₂])
      (K := g) (by
        intro v hv
        simp only [Submodule.mem_iInf, LinearMap.mem_ker, Fin.forall_fin_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hv
        exact hg v (hdir ▸ ⟨hv.1, hv.2⟩))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    exact ⟨c 0, c 1, fun v => by simp [← hc, Fin.sum_univ_two]⟩
  obtain ⟨a, b, hab⟩ := hcomb φ hφ
  have hnorm : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h0
    have ha : a = 0 := by nlinarith
    have hb : b = 0 := by nlinarith
    exact hφ0 (LinearMap.ext fun v => by simp [hab, ha, hb])
  -- Rotate the equations so that the first generator is `w ↦ φ q - φ w`.
  let g₁ : V →ᵃ[ℝ] ℝ := (h.realCharacter f₁).toAffineMap - AffineMap.const ℝ V
    (h.realCharacter f₁ q)
  let g₂ : V →ᵃ[ℝ] ℝ := (h.realCharacter f₂).toAffineMap - AffineMap.const ℝ V
    (h.realCharacter f₂ q)
  have hg₁ (w : V) : g₁ w = h.realCharacter f₁ (w - q) := by simp [g₁]
  have hg₂ (w : V) : g₂ w = h.realCharacter f₂ (w - q) := by simp [g₂]
  refine ⟨(-a) • g₁ + (-b) • g₂, b • g₁ + (-a) • g₂, fun w => ?_, fun g hg => ?_⟩
  · have := hab (q - w)
    simp only [map_sub] at this
    simp only [AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply, hg₁, hg₂,
      map_sub, smul_eq_mul]
    linarith
  · obtain ⟨c₁, c₂, hc⟩ := hcomb g hg
    refine ⟨-(c₁ * a + c₂ * b) / (a ^ 2 + b ^ 2), (c₁ * b - c₂ * a) / (a ^ 2 + b ^ 2),
      fun w => ?_⟩
    rw [← map_sub, hc]
    simp only [AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply, hg₁, hg₂,
      smul_eq_mul]
    field_simp
    ring

end JointGeometry

end Mei.FinitePolyhedralComplex
