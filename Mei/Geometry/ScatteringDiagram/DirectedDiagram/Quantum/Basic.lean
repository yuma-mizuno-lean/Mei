/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Dilogarithm
public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Quantum scattering diagrams of full hyperplanes

The quantum wall spaces of an integral alternating form `β` satisfy the directed wall-space
laws, so every finitely active input of full affine hyperplanes for them has the outgoing
scattering class `DirectedDiagram.Scat`: the quantum *Scat*. A ring homomorphism `φ : R →+* S`
between rational algebras with `φ(q^β(p,r)) = q'^β(p,r)` preserves the quantum wall spaces, so it
maps quantum diagrams over `R` to quantum diagrams over `S` (`DirectedDiagram.quantumMap`),
retaining supports, normals and rays. It carries every representative of the quantum *Scat* of a
full-hyperplane input to a representative of the quantum *Scat* of the image input
(`DirectedDiagram.toClass_quantumMap_eq_scat`), even when `φ` kills labels. At `q ↦ 1` every
label of the image acts trivially on completed coefficients, by
`QuantumMonoidAlgebra.CoefficientAction.completedBCHAction_atOne`.

A `QuantumHyperplaneInput` consists of full affine hyperplanes `{m_j = c_j}` whose nonzero integral
normals `m_j` have the kernels of `β(n_j,-)`, for degrees `n_j` on supported rays `w_j`. With
labels in the quantum wall groups of `w_j` and `m_j` it is a finite incoming quantum diagram
(`QuantumHyperplaneInput.diagram`); with the quantum dilogarithm labels `exp(log Ψ_q(z^{n_j}))`
it is the quantum dilogarithm input (`QuantumHyperplaneInput.dilogDiagram`). If all pairings
`β(n_a, n_b)` vanish, the dilogarithm labels commute, so the dilogarithm input is consistent and
its quantum *Scat* is its own class (`QuantumHyperplaneInput.scat_dilogDiagram_eq_toClass`).

We use `DirectedWall.ofAffineHyperplane`, `DirectedDiagram.mapRestrictScalars` over `ℚ`,
`QuantumMonoidAlgebra.positiveGradedLieHom_mem_wall`,
`DirectedDiagram.toClass_mapRestrictScalars_eq_scat` and
`DirectedDiagram.consistent_of_commute_of_full`. The quantum scattering diagrams follow Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(iii) and
Theorem 2.6, arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

open QuantumMonoidAlgebra PowerSeries

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {R S : Type u} {Γ V ι : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommGroup Γ] [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {β : LinearMap.BilinForm ℤ Γ} {hβ : β.IsAlt} {d : PositiveDegrees Γ}
  {i : Γ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace DirectedDiagram

variable {q : Rˣ} {q' : Sˣ} (φ : R →+* S)
  (hφ : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β p r)

/-- Change the coefficient ring of a quantum diagram along a ring homomorphism `φ` with
`φ(q^β(p,r)) = q'^β(p,r)`, retaining every index, support, normal and supported ray. The two
coefficient rings lie in one universe. -/
def quantumMap (D : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι) :
    DirectedDiagram (d := d) h (wallSpaces q' β d hβ) ι :=
  D.mapRestrictScalars (K := ℚ)
    (positiveGradedLieHom φ.toRatAlgHom (PositiveDegreeMap.id d) (by simpa using hφ))
    (positiveGradedLieHom_mem_wall φ.toRatAlgHom hφ hβ)

/-- The quantum coefficient change is the scalar-restricted map of the positive quantum Lie
homomorphism of `φ`. -/
theorem quantumMap_def (D : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι) :
    D.quantumMap φ hφ = D.mapRestrictScalars (K := ℚ)
      (positiveGradedLieHom φ.toRatAlgHom (PositiveDegreeMap.id d) (by simpa using hφ))
      (positiveGradedLieHom_mem_wall φ.toRatAlgHom hφ hβ) :=
  (rfl)

/-- The quantum coefficient change retains the support of every wall. -/
@[simp]
theorem support_quantumMap_wall (D : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι)
    (j : ι) : ((D.quantumMap φ hφ).wall j).support = (D.wall j).support := by
  rw [quantumMap_def, mapRestrictScalars_wall, DirectedWall.mapRestrictScalars_support]

/-- The quantum coefficient change retains the normal of every wall. -/
@[simp]
theorem normal_quantumMap_wall (D : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι)
    (j : ι) : ((D.quantumMap φ hφ).wall j).normal = (D.wall j).normal := by
  rw [quantumMap_def, mapRestrictScalars_wall, DirectedWall.mapRestrictScalars_normal]

variable [Module.Free ℤ Γ]

/-- The quantum *Scat* is natural for coefficient maps: `φ` carries every representative of the
quantum scattering class of a full-hyperplane input to a representative of the quantum
scattering class of the image input. The map `φ` can kill labels. -/
theorem toClass_quantumMap_eq_scat {ι κ : Type v}
    (D : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    {E : DirectedDiagram (d := d) h (wallSpaces q β d hβ) κ}
    (hE : E.toClass = D.Scat hfull) :
    (E.quantumMap φ hφ).toClass = (D.quantumMap φ hφ).Scat (by
      simpa only [support_quantumMap_wall, normal_quantumMap_wall] using hfull) :=
  toClass_mapRestrictScalars_eq_scat _ _ D hfull hE

end DirectedDiagram

/-- Full affine hyperplanes `{m_j = c_j}`, `j ∈ ι`, whose nonzero integral normals `m_j` have the
kernels of `β(n_j,-)`, for degrees `n_j` on supported rays `w_j`. -/
@[ext]
structure QuantumHyperplaneInput (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
    (ι : Type*) where
  /-- The supported ray `w_j` of the hyperplane `j`. -/
  ray : ι → SupportedRay d
  /-- The degree `n_j`, on the ray `w_j`. -/
  degree : ι → Γ
  /-- Each degree lies on its supported ray. -/
  degree_mem (j : ι) : degree j ∈ (ray j).rayDegrees
  /-- The integral normal `m_j`. -/
  normal : ι → Γ →+ ℤ
  /-- The normals are nonzero. -/
  normal_ne_zero (j : ι) : normal j ≠ 0
  /-- The normal `m_j` has the kernel of `β(n_j,-)`. -/
  ker_normal (j : ι) : (normal j).ker = (β (degree j)).toAddMonoidHom.ker
  /-- The offset `c_j` of the hyperplane `{m_j = c_j}`. -/
  offset : ι → ℝ

namespace QuantumHyperplaneInput

variable (I : QuantumHyperplaneInput β d ι)

omit [DecidableEq Γ] in
/-- For an alternating form, each normal annihilates the generator of its supported ray. -/
theorem normal_apply_ray_generator (hβ : β.IsAlt) (j : ι) :
    I.normal j (I.ray j).generator = 0 := by
  obtain ⟨-, a, ha, he⟩ := SupportedRay.mem_rayDegrees.mp (I.degree_mem j)
  have hn : I.normal j (I.degree j) = 0 := by
    have hk : I.degree j ∈ (β (I.degree j)).toAddMonoidHom.ker := hβ.self_eq_zero _
    rw [← I.ker_normal j] at hk
    exact hk
  rw [he, map_zsmul, smul_eq_zero] at hn
  exact hn.resolve_left ha.ne'

variable [Finite ι] (h) (q : Rˣ)

/-- The finite incoming quantum diagram of full hyperplanes `{m_j = c_j}` with labels `g_j` in the
quantum wall groups of `w_j` and `m_j`. -/
def diagram (g : ∀ j, (wallSpaces q β d hβ).wallGroup (I.ray j) (I.normal j)) :
    DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι :=
  .ofFinite fun j => DirectedWall.ofAffineHyperplane h _ (I.normal j) (I.normal_ne_zero j)
    (I.offset j) (I.ray j) (I.normal_apply_ray_generator hβ j) (g j)

/-- The wall `j` of the diagram is the full hyperplane `{m_j = c_j}` with label `g_j`. -/
@[simp]
theorem diagram_wall (g : ∀ j, (wallSpaces q β d hβ).wallGroup (I.ray j) (I.normal j)) (j : ι) :
    (I.diagram h q g).wall j = DirectedWall.ofAffineHyperplane h _ (I.normal j)
      (I.normal_ne_zero j) (I.offset j) (I.ray j) (I.normal_apply_ray_generator hβ j) (g j) :=
  DirectedDiagram.ofFinite_wall _ j

/-- Every wall of the diagram is a full affine hyperplane `{m_j = c_j}`. -/
theorem diagram_full (g : ∀ j, (wallSpaces q β d hβ).wallGroup (I.ray j) (I.normal j)) (j : ι) :
    ∃ a : ℝ, ((I.diagram h q g).wall j).support =
      {x | h.realCharacter ((I.diagram h q g).wall j).normal x = a} :=
  ⟨I.offset j, by simp⟩

variable (hβ) (hq : ∀ k : ℕ, IsUnit ((q : R) ^ (k + 1) - (↑q⁻¹ : R) ^ (k + 1)))

/-- The quantum dilogarithm input: the full hyperplanes `{m_j = c_j}` labelled by the quantum
dilogarithm wall labels `exp(log Ψ_q(z^{n_j}))`. -/
def dilogDiagram : DirectedDiagram (d := d) h (wallSpaces q β d hβ) ι :=
  I.diagram h q fun j => quantumDilogLabel q β hβ (I.normal_ne_zero j) (I.ker_normal j) hq
    (I.degree_mem j)

/-- The quantum dilogarithm input is the diagram of the quantum dilogarithm wall labels. -/
theorem dilogDiagram_def :
    I.dilogDiagram hβ h q hq = I.diagram h q fun j =>
      quantumDilogLabel q β hβ (I.normal_ne_zero j) (I.ker_normal j) hq (I.degree_mem j) :=
  (rfl)

/-- Every wall of the quantum dilogarithm input is a full affine hyperplane `{m_j = c_j}`. -/
theorem dilogDiagram_full (j : ι) :
    ∃ a : ℝ, ((I.dilogDiagram hβ h q hq).wall j).support =
      {x | h.realCharacter ((I.dilogDiagram hβ h q hq).wall j).normal x = a} :=
  ⟨I.offset j, by simp [dilogDiagram_def]⟩

variable [Module.Free ℤ Γ]

/-- If all pairings `β(n_a, n_b)` vanish, the quantum dilogarithm input is its own outgoing
completion: its quantum *Scat* is its own class. -/
theorem scat_dilogDiagram_eq_toClass (hcomm : ∀ a b, β (I.degree a) (I.degree b) = 0) :
    (I.dilogDiagram hβ h q hq).Scat (I.dilogDiagram_full hβ h q hq) =
      (I.dilogDiagram hβ h q hq).toClass := by
  apply DirectedDiagram.scat_eq_toClass_of_consistent
  refine DirectedDiagram.consistent_of_commute_of_full _ (I.dilogDiagram_full hβ h q hq)
    fun a b => ?_
  simp only [dilogDiagram_def, diagram_wall, DirectedWall.ofAffineHyperplane_label,
    coe_quantumDilogLabel]
  exact commute_rayExp q β _ _ hβ _ _ (hcomm a b) _ _

end QuantumHyperplaneInput

end Mei
