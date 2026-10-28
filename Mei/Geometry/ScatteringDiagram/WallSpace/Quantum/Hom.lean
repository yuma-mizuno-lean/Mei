/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Quantum.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.RestrictScalars

/-!
# Coefficient maps of quantum wall spaces

Quantum coefficient maps preserve the wall spaces determined by a fixed integral
alternating form. Eligibility uses the integral normal, so this remains true when
specialization enlarges the center of the quantum algebra. Coefficient maps may
have kernels and can kill wall labels.

The positive graded Lie map is linear over a common base ring. Its wall-preservation
theorem supplies the hypothesis of `Mei.GradedLieHom.wallGroupMap` and of the
coefficient maps of directed diagrams and outgoing scattering classes. Over rational
coefficient algebras these apply after restriction to the common rational scalars.

We use the existing quantum coefficient map, positive-support restriction and
integral eligibility characterization. The quantum wall convention follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(iii).
-/

public section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R S Γ : Type*} [CommRing R] [CommRing S] [AddCommGroup Γ]
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ}

/-- Coefficient specialization preserves integral quantum wall eligibility,
including specializations at which the commutator becomes zero. -/
theorem map_mem_wallSubmodule (φ : R →+* S)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β p r)
    {n : Γ} {m : Γ →+ ℤ} {x : QuantumMonoidAlgebra q β}
    (hx : x ∈ wallSubmodule q β n m) :
    map φ (AddMonoidHom.id Γ) h x ∈ wallSubmodule q' β n m := by
  rcases (mem_wallSubmodule_iff q β n m x).mp hx with rfl | ⟨hm, hk, hx⟩
  · simp
  · exact (mem_wallSubmodule_iff q' β n m _).mpr
      (Or.inr ⟨hm, hk, map_mem_grade φ (AddMonoidHom.id Γ) h hx⟩)

variable {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]
  {d : PositiveDegrees Γ}

/-- The positive quantum Lie map preserves every wall space over the common base
ring. Thus it induces maps of wall groups and of outgoing scattering classes. -/
theorem positiveGradedLieHom_mem_wall (φ : R →ₐ[k] S)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β p r)
    (hβ : β.IsAlt) (n : Γ) (m : Γ →+ ℤ)
    (x : positiveLieAlgebra q β d)
    (hx : x ∈ ((wallSpaces q β d hβ).restrictScalars k).wall n m) :
    positiveGradedLieHom φ (PositiveDegreeMap.id d) (by simpa using h) x ∈
      ((wallSpaces q' β d hβ).restrictScalars k).wall n m := by
  simp only [DirectedWallSpaces.restrictScalars_wall, Submodule.restrictScalars_mem,
    wallSpaces_wall, Submodule.mem_comap] at hx ⊢
  have hid : (PositiveDegreeMap.id d).toAddMonoidHom = AddMonoidHom.id Γ :=
    DFunLike.ext _ _ (fun n => PositiveDegreeMap.id_apply n)
  simpa only [LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    coe_positiveGradedLieHom_apply, hid] using
    map_mem_wallSubmodule φ.toRingHom h hx

end Mei.QuantumMonoidAlgebra
