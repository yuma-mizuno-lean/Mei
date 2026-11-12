/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.WallSpace.Basic
import Mei.Algebra.Group.Hom.Int

/-!
# Directions and normals for module probes

The module probe adds a single spatial coordinate `z`, the probe coordinate. The module
charge is a grading coordinate only: an extended degree `(q, c)` has spatial direction
`(ρ q, 0)`, so charge-one directions vanish exactly when the original spatial direction
does. Base normals ignore the probe coordinate; the probe normal reads it.
Their mixed contracted bracket is again a probe normal, with coefficient given by
the base normal evaluated on the coefficient's spatial degree. Two module normals
have zero contracted bracket. These identities supply the normal calculations
for the module-probe wall spaces.
-/

public section

open TauCeti (wallBracketNormal)

namespace Mei.ModuleProbe

variable {Γ Λ : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]

/-- Extended spatial directions: the module charge has no spatial direction, and every
direction has zero probe coordinate. -/
def spatialMap (ρ : Γ →+ Λ) : (Γ × ℤ) →+ (Λ × ℤ) :=
  (AddMonoidHom.inl Λ ℤ).comp (ρ.comp (AddMonoidHom.fst Γ ℤ))

/-- The extended spatial map forgets the charge and has zero probe coordinate. -/
@[simp]
theorem spatialMap_apply (ρ : Γ →+ Λ) (q : Γ) (c : ℤ) :
    spatialMap ρ (q, c) = (ρ q, 0) := (rfl)

/-- An extended direction vanishes exactly when its original spatial direction does,
whatever the module charge. In particular charge-one directions can vanish.
This is not a simp lemma: `spatialMap_apply` and `Prod.mk_eq_zero` already prove it. -/
theorem spatialMap_eq_zero_iff (ρ : Γ →+ Λ) (q : Γ) (c : ℤ) :
    spatialMap ρ (q, c) = 0 ↔ ρ q = 0 := by
  simp [Prod.ext_iff]

/-- A base wall normal ignores the probe coordinate. -/
def baseNormal (m : Λ →+ ℤ) : (Λ × ℤ) →+ ℤ :=
  m.comp (AddMonoidHom.fst Λ ℤ)

/-- A base normal is the pullback along the first spatial projection. -/
theorem baseNormal_def (m : Λ →+ ℤ) :
    baseNormal m = m.comp (AddMonoidHom.fst Λ ℤ) := (rfl)

/-- Evaluate a lifted base normal. -/
@[simp]
theorem baseNormal_apply (m : Λ →+ ℤ) (v : Λ) (l : ℤ) :
    baseNormal m (v, l) = m v := (rfl)

/-- The probe normal reads the probe coordinate. -/
def probeNormal : (Λ × ℤ) →+ ℤ :=
  AddMonoidHom.snd Λ ℤ

/-- Evaluate the probe normal. -/
@[simp]
theorem probeNormal_apply (v : Λ) (l : ℤ) :
    probeNormal (v, l) = l := (rfl)

/-- The two classes of normals intersect only at zero. -/
theorem baseNormal_eq_smul_probeNormal_iff (m : Λ →+ ℤ) (c : ℤ) :
    baseNormal m = c • (probeNormal : (Λ × ℤ) →+ ℤ) ↔ m = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hc := DFunLike.congr_fun h (0, 1)
    have hc0 : c = 0 := by simpa using hc.symm
    refine ⟨?_, hc0⟩
    ext v
    have hv := DFunLike.congr_fun h (v, 0)
    simpa using hv
  · rintro ⟨rfl, rfl⟩
    ext v
    simp [baseNormal]

/-- The probe normal is nonzero. -/
theorem probeNormal_ne_zero : (probeNormal : (Λ × ℤ) →+ ℤ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (0, 1)
  norm_num at this

/-- Base normals are exactly the normals vanishing on the probe coordinate. -/
theorem mem_range_baseNormal (m : (Λ × ℤ) →+ ℤ) :
    m ∈ Set.range (baseNormal (Λ := Λ)) ↔ m (0, 1) = 0 := by
  constructor
  · rintro ⟨m, rfl⟩
    simp
  · intro h
    refine ⟨m.comp (AddMonoidHom.inl Λ ℤ), ?_⟩
    ext ⟨v, l⟩
    -- Evaluate the composite normal on the base inclusion; the product zero is `(0, 0)`.
    change m (v, 0) = m (v, l)
    simpa [h] using (m.apply_prod_int v l).symm

/-- Probe normals are exactly the normals vanishing on the base coordinates; the
integer multiplier is their value on the probe coordinate. -/
theorem mem_range_smul_probeNormal (m : (Λ × ℤ) →+ ℤ) :
    m ∈ Set.range (fun c : ℤ => c • (probeNormal : (Λ × ℤ) →+ ℤ)) ↔
      ∀ v, m (v, 0) = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h
    refine ⟨m (0, 1), ?_⟩
    ext ⟨v, l⟩
    simpa [h, mul_comm] using (m.apply_prod_int v l).symm

/-- Membership in the class of base normals is unchanged by nonzero integral
rescaling, as required by the directed wall-space rescaling law. -/
theorem smul_mem_range_baseNormal (m : (Λ × ℤ) →+ ℤ) {c : ℤ} (hc : c ≠ 0) :
    c • m ∈ Set.range (baseNormal (Λ := Λ)) ↔ m ∈ Set.range (baseNormal (Λ := Λ)) := by
  rw [mem_range_baseNormal, mem_range_baseNormal]
  simp [hc]

/-- Membership in the class of probe normals is unchanged by nonzero integral
rescaling, including for normals outside that class. -/
theorem smul_mem_range_smul_probeNormal (m : (Λ × ℤ) →+ ℤ) {c : ℤ} (hc : c ≠ 0) :
    c • m ∈ Set.range (fun a : ℤ => a • (probeNormal : (Λ × ℤ) →+ ℤ)) ↔
      m ∈ Set.range (fun a : ℤ => a • (probeNormal : (Λ × ℤ) →+ ℤ)) := by
  rw [mem_range_smul_probeNormal, mem_range_smul_probeNormal]
  simp [hc]

/-- Contracting two base normals commutes with their lift. -/
theorem wallBracketNormal_base_base (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) :
    wallBracketNormal (spatialMap ρ) (n, 0) (n', 0)
      (baseNormal m) (baseNormal m') = baseNormal (wallBracketNormal ρ n n' m m') := by
  ext ⟨v, a⟩
  simp

/-- A base wall and a charge-one wall have the expected contracted probe normal. -/
theorem wallBracketNormal_base_probe (ρ : Γ →+ Λ) (n q : Γ) (m : Λ →+ ℤ) (c : ℤ) :
    wallBracketNormal (spatialMap ρ) (n, 0) (q, 1)
      (baseNormal m) (c • probeNormal) =
        (m (ρ q) * c) • (probeNormal : (Λ × ℤ) →+ ℤ) := by
  ext v
  simp [mul_assoc]

/-- Reversing a mixed bracket reverses its contracted normal. -/
theorem wallBracketNormal_probe_base (ρ : Γ →+ Λ) (q n : Γ) (m : Λ →+ ℤ) (c : ℤ) :
    wallBracketNormal (spatialMap ρ) (q, 1) (n, 0)
      (c • probeNormal) (baseNormal m) =
        -(m (ρ q) * c) • (probeNormal : (Λ × ℤ) →+ ℤ) := by
  ext v
  simp [mul_assoc]

/-- Two charge-one probe normals have zero contracted bracket. -/
theorem wallBracketNormal_probe_probe (ρ : Γ →+ Λ) (q q' : Γ) (c c' : ℤ) :
    wallBracketNormal (spatialMap ρ) (q, 1) (q', 1)
      (c • probeNormal) (c' • probeNormal) = 0 := by
  ext v
  simp

end Mei.ModuleProbe
