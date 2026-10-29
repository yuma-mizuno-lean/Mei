/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Basic

/-!
# Directions and normals for module probes

The module probe extends spatial directions by the charge and probe coordinates.
Base normals ignore both coordinates; the probe normal reads the last one.
Their mixed contracted bracket is again a probe normal, with coefficient given by
the base normal evaluated on the coefficient's spatial degree. Two module normals
have zero contracted bracket. These identities supply the normal calculations
for the module-probe wall spaces.
-/

public section

namespace Mei.ModuleProbe

variable {Γ Λ : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]

/-- Extend spatial directions by the module charge and probe coordinates. -/
def spatialMap (ρ : Γ →+ Λ) : (Γ × ℤ × ℤ) →+ (Λ × ℤ × ℤ) :=
  ρ.prodMap (AddMonoidHom.id (ℤ × ℤ))

/-- The extended spatial map preserves both extra coordinates. -/
@[simp]
theorem spatialMap_apply (ρ : Γ →+ Λ) (q : Γ) (c l : ℤ) :
    spatialMap ρ (q, c, l) = (ρ q, c, l) := (rfl)

/-- A charge-one direction is nonzero even when its original spatial part vanishes. -/
theorem spatialMap_chargeOne_ne_zero (ρ : Γ →+ Λ) (q : Γ) :
    spatialMap ρ (q, 1, 0) ≠ 0 := by
  intro h
  have := congrArg (fun a : Λ × ℤ × ℤ => a.2.1) h
  norm_num at this

/-- A base wall normal ignores the module charge and probe coordinates. -/
def baseNormal (m : Λ →+ ℤ) : (Λ × ℤ × ℤ) →+ ℤ :=
  m.comp (AddMonoidHom.fst Λ (ℤ × ℤ))

/-- A base normal is the pullback along the first spatial projection. -/
theorem baseNormal_def (m : Λ →+ ℤ) :
    baseNormal m = m.comp (AddMonoidHom.fst Λ (ℤ × ℤ)) := (rfl)

/-- Evaluate a lifted base normal. -/
@[simp]
theorem baseNormal_apply (m : Λ →+ ℤ) (v : Λ) (c l : ℤ) :
    baseNormal m (v, c, l) = m v := (rfl)

/-- The probe normal reads the last coordinate. -/
def probeNormal : (Λ × ℤ × ℤ) →+ ℤ :=
  (AddMonoidHom.snd ℤ ℤ).comp (AddMonoidHom.snd Λ (ℤ × ℤ))

/-- Evaluate the probe normal. -/
@[simp]
theorem probeNormal_apply (v : Λ) (c l : ℤ) :
    probeNormal (v, c, l) = l := (rfl)

/-- The two classes of normals intersect only at zero. -/
theorem baseNormal_eq_smul_probeNormal_iff (m : Λ →+ ℤ) (c : ℤ) :
    baseNormal m = c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) ↔ m = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hc := DFunLike.congr_fun h (0, 0, 1)
    have hc0 : c = 0 := by simpa using hc.symm
    refine ⟨?_, hc0⟩
    ext v
    have hv := DFunLike.congr_fun h (v, 0, 0)
    simpa using hv
  · rintro ⟨rfl, rfl⟩
    ext v
    simp [baseNormal]

/-- The probe normal is nonzero. -/
theorem probeNormal_ne_zero : (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) ≠ 0 := by
  intro h
  have := DFunLike.congr_fun h (0, 0, 1)
  norm_num at this

/-- An extended normal is determined by its base restriction and its values on
the two extra coordinate vectors. -/
theorem normal_apply_eq (m : (Λ × ℤ × ℤ) →+ ℤ) (v : Λ) (c l : ℤ) :
    m (v, c, l) = m (v, 0, 0) + c * m (0, 1, 0) + l * m (0, 0, 1) := by
  have hc := ((m.comp (AddMonoidHom.inr Λ (ℤ × ℤ))).comp
    (AddMonoidHom.inl ℤ ℤ)).map_zsmul c (1 : ℤ)
  have hl := ((m.comp (AddMonoidHom.inr Λ (ℤ × ℤ))).comp
    (AddMonoidHom.inr ℤ ℤ)).map_zsmul l (1 : ℤ)
  have hc' : m (0, c, 0) = c * m (0, 1, 0) := by simpa using hc
  have hl' : m (0, 0, l) = l * m (0, 0, 1) := by simpa using hl
  rw [← hc', ← hl', ← map_add, ← map_add]
  simp

/-- Base normals are exactly the normals vanishing on both extra coordinates. -/
theorem mem_range_baseNormal (m : (Λ × ℤ × ℤ) →+ ℤ) :
    m ∈ Set.range (baseNormal (Λ := Λ)) ↔ m (0, 1, 0) = 0 ∧ m (0, 0, 1) = 0 := by
  constructor
  · rintro ⟨m, rfl⟩
    simp
  · intro h
    refine ⟨m.comp (AddMonoidHom.inl Λ (ℤ × ℤ)), ?_⟩
    ext ⟨v, c, l⟩
    -- Evaluate the composite normal on the base inclusion; the product zero is (0, 0).
    change m (v, 0, 0) = m (v, c, l)
    simpa [h.1, h.2] using (normal_apply_eq m v c l).symm

/-- Probe normals are exactly the normals vanishing on the base and charge
coordinates; the integer multiplier is their value on the probe coordinate. -/
theorem mem_range_smul_probeNormal (m : (Λ × ℤ × ℤ) →+ ℤ) :
    m ∈ Set.range (fun c : ℤ => c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ)) ↔
      (∀ v, m (v, 0, 0) = 0) ∧ m (0, 1, 0) = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h
    refine ⟨m (0, 0, 1), ?_⟩
    ext ⟨v, c, l⟩
    simpa [h.1, h.2, mul_comm] using (normal_apply_eq m v c l).symm

/-- Membership in the class of base normals is unchanged by nonzero integral
rescaling, as required by the directed wall-space rescaling law. -/
theorem smul_mem_range_baseNormal (m : (Λ × ℤ × ℤ) →+ ℤ) {c : ℤ} (hc : c ≠ 0) :
    c • m ∈ Set.range (baseNormal (Λ := Λ)) ↔ m ∈ Set.range (baseNormal (Λ := Λ)) := by
  rw [mem_range_baseNormal, mem_range_baseNormal]
  simp [hc]

/-- Membership in the class of probe normals is unchanged by nonzero integral
rescaling, including for normals outside that class. -/
theorem smul_mem_range_smul_probeNormal (m : (Λ × ℤ × ℤ) →+ ℤ) {c : ℤ} (hc : c ≠ 0) :
    c • m ∈ Set.range (fun a : ℤ => a • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ)) ↔
      m ∈ Set.range (fun a : ℤ => a • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ)) := by
  rw [mem_range_smul_probeNormal, mem_range_smul_probeNormal]
  simp [hc]

/-- Contracting two base normals commutes with their lift. -/
theorem wallBracketNormal_base_base (ρ : Γ →+ Λ) (n n' : Γ) (m m' : Λ →+ ℤ) :
    wallBracketNormal (spatialMap ρ) (n, 0, 0) (n', 0, 0)
      (baseNormal m) (baseNormal m') = baseNormal (wallBracketNormal ρ n n' m m') := by
  ext ⟨v, a, b⟩
  simp

/-- A base wall and a charge-one wall have the expected contracted probe normal. -/
theorem wallBracketNormal_base_probe (ρ : Γ →+ Λ) (n q : Γ) (m : Λ →+ ℤ) (c : ℤ) :
    wallBracketNormal (spatialMap ρ) (n, 0, 0) (q, 1, 0)
      (baseNormal m) (c • probeNormal) =
        (m (ρ q) * c) • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) := by
  ext v
  simp [mul_assoc]

/-- Reversing a mixed bracket reverses its contracted normal. -/
theorem wallBracketNormal_probe_base (ρ : Γ →+ Λ) (q n : Γ) (m : Λ →+ ℤ) (c : ℤ) :
    wallBracketNormal (spatialMap ρ) (q, 1, 0) (n, 0, 0)
      (c • probeNormal) (baseNormal m) =
        -(m (ρ q) * c) • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) := by
  ext v
  simp [mul_assoc]

/-- Two charge-one probe normals have zero contracted bracket. -/
theorem wallBracketNormal_probe_probe (ρ : Γ →+ Λ) (q q' : Γ) (c c' : ℤ) :
    wallBracketNormal (spatialMap ρ) (q, 1, 0) (q', 1, 0)
      (c • probeNormal) (c' • probeNormal) = 0 := by
  ext v
  simp

end Mei.ModuleProbe
