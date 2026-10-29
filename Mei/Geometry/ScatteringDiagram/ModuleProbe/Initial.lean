/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Group
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Cylinder
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Limit

/-!
# Initial walls of a module probe

Base walls lift to cylinders with charge-zero labels in the semidirect probe
group. A homogeneous incoming coefficient gives the full probe hyperplane with
label its charge-one exponential. Adjoining this wall to the cylinders preserves
finite activity at every cutoff. Incoming base walls remain incoming, so a
full-hyperplane input gives a full-hyperplane input for the probe and admits a
consistent outgoing completion. This does not yet identify the charge-zero
part of that completion with a prescribed completed base diagram.

The auxiliary real space may be any integral lattice model of `ℤ × ℤ`; the
probe hyperplane is the kernel of the real extension of the last coordinate.
We use `DirectedWall.cylinder`, `GradedLieHom.completedMap_mem_wallGroup` and
`ModuleProbe.moduleWallGroupEquiv`. The construction follows Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)

section Base

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

private def baseProjectedWall (W : DirectedWall (d := d) h H) :
    DirectedWall (d := positiveDegrees d p) h
      ((wallSpaces d ℳ p ℒ H).project (AddMonoidHom.fst Λ (ℤ × ℤ))) where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := baseRay d p W.ray
  normal_direction := by simpa using W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := (baseGradedLieHom d ℳ p ℒ).completedMap W.label
  label_mem := (baseGradedLieHom d ℳ p ℒ).completedMap_mem_wallGroup
    (H := H) (H' := (wallSpaces d ℳ p ℒ H).project (AddMonoidHom.fst Λ (ℤ × ℤ)))
    (w := W.ray) (v := baseRay d p W.ray) (m := W.normal) (m' := W.normal)
    (fun n hn => by simpa using hn)
    (fun n _ x hx => by
      simp only [DirectedWallSpaces.project_wall, baseMap_apply,
        wallSpaces_wall]
      rw [← baseNormal_def, wallSubmodule_base]
      exact Submodule.mem_map.mpr ⟨x, hx, by simp⟩) W.label_mem

/-- Lift a base wall to its cylinder and include its label in charge zero. -/
def baseCylinder (W : DirectedWall (d := d) h H) :
    DirectedWall (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) :=
  (baseProjectedWall d ℳ p ℒ H h W).cylinder h'

@[simp]
theorem baseCylinder_normal (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).normal = baseNormal W.normal := by
  simp [baseCylinder, baseProjectedWall, baseNormal_def]

@[simp]
theorem baseCylinder_ray (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).ray = baseRay d p W.ray := by
  simp [baseCylinder, baseProjectedWall]

@[simp]
theorem baseCylinder_support (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).support = W.support ×ˢ (Set.univ : Set E) := by
  simp [baseCylinder, baseProjectedWall]

@[simp]
theorem baseCylinder_label (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).label =
      (baseGradedLieHom d ℳ p ℒ).completedMap W.label := by
  simp [baseCylinder, baseProjectedWall]

/-- The unrestricted coordinates impose no additional incomingness condition. -/
@[simp]
theorem baseCylinder_incoming_iff (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).Incoming ↔ W.Incoming := by
  rw [baseCylinder, DirectedWall.cylinder_incoming_iff,
    DirectedWall.incoming_iff, DirectedWall.incoming_iff]
  simp [baseProjectedWall]

/-- Outgoing base walls remain outgoing after inclusion in the probe. -/
@[simp]
theorem baseCylinder_outgoing_iff (W : DirectedWall (d := d) h H) :
    (baseCylinder d ℳ p ℒ H h h' W).Outgoing ↔ W.Outgoing := by
  rw [baseCylinder, DirectedWall.cylinder_outgoing_iff,
    DirectedWall.outgoing_iff, DirectedWall.outgoing_iff]
  simp [baseProjectedWall]

/-- A cylinder over a full affine hyperplane is again the full affine hyperplane
of its pulled-back normal, with the same offset. -/
theorem baseCylinder_support_eq_hyperplane (W : DirectedWall (d := d) h H) {c : ℝ}
    (hW : W.support = {x | h.realCharacter W.normal x = c}) :
    (baseCylinder d ℳ p ℒ H h h' W).support =
      {x | (h.prod h').realCharacter (baseCylinder d ℳ p ℒ H h h' W).normal x = c} := by
  have hn : (h.prod h').realCharacter (baseCylinder d ℳ p ℒ H h h' W).normal =
      (h.realCharacter W.normal).comp (LinearMap.fst ℝ V E) := by
    rw [baseCylinder_normal, baseNormal_def]
    exact (h.prod h').realCharacter_comp h (AddMonoidHom.fst Λ (ℤ × ℤ))
      (LinearMap.fst ℝ V E) (fun _ => rfl) W.normal
  ext x
  rw [hn]
  simp [baseCylinder_support, hW]

end Base

private def initialCoefficient (a : ℳ p) :
    shiftedGrading ℳ d.monoid p (p - p) :=
  ⟨⟨a, le_shiftedSubmodule ℳ d.monoid p (n := 0) (zero_mem _) (by simp)⟩,
    (mem_shiftedGrading ℳ d.monoid p).mpr (by simp)⟩

/-- The full probe hyperplane, labelled by the exponential of the incoming coefficient. -/
def probeWall (a : ℳ p) :
    DirectedWall (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) :=
  DirectedWall.ofLinearHyperplane (h.prod h') (wallSpaces d ℳ p ℒ H)
    probeNormal probeNormal_ne_zero (moduleRay d p p (by simp)) (by simp)
    (moduleWallGroupEquiv d ℳ p ℒ H p (by simp)
      (Multiplicative.ofAdd (initialCoefficient d ℳ p a)))

@[simp]
theorem probeWall_normal (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).normal = probeNormal := by simp [probeWall]

@[simp]
theorem probeWall_ray (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).ray = moduleRay d p p (by simp) := by simp [probeWall]

@[simp]
theorem probeWall_support (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).support =
      ((h.prod h').realCharacter probeNormal).ker := by simp [probeWall]

/-- The label is the completed exponential of the original homogeneous coefficient
included in the abelian ideal of the probe. -/
theorem probeWall_label (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).label =
      (positiveDegrees d p).expToCompletion (grading d ℳ p ℒ)
        (moduleInclusion d ℳ p ℒ ((moduleCoefficientsEquiv d ℳ p).symm
          ⟨a, le_shiftedSubmodule ℳ d.monoid p (n := 0) (zero_mem _)
            (by simp)⟩)) := by
  simp only [probeWall, DirectedWall.ofLinearHyperplane_label, coe_moduleWallGroupEquiv,
    toAdd_ofAdd, initialCoefficient]

/-- The probe wall is incoming, even when the original coefficient has zero velocity. -/
@[simp]
theorem probeWall_incoming (a : ℳ p) : (probeWall d ℳ p ℒ H h h' a).Incoming := by
  exact DirectedWall.ofLinearHyperplane_incoming _ _ _ _ _ _ _

/-- A zero coefficient contributes exactly the identity label. -/
@[simp↓]
theorem probeWall_label_eq_one_iff (a : ℳ p) :
    (probeWall d ℳ p ℒ H h h' a).label = 1 ↔ a = 0 := by
  rw [probeWall, DirectedWall.ofLinearHyperplane_label]
  constructor
  · intro ha
    have he : moduleWallGroupEquiv d ℳ p ℒ H p (by simp)
        (Multiplicative.ofAdd (initialCoefficient d ℳ p a)) = 1 := Subtype.ext ha
    have hz := (map_eq_one_iff _
      (moduleWallGroupEquiv d ℳ p ℒ H p (by simp)).injective).mp he
    exact Subtype.ext (congrArg (fun b => (b.toAdd.val : M)) hz)
  · rintro rfl
    have hz : Multiplicative.ofAdd (initialCoefficient d ℳ p (0 : ℳ p)) = 1 := rfl
    rw [hz, map_one]
    rfl

/-- A nonzero probe coefficient is visible precisely from extended order one onward. -/
@[simp↓]
theorem projection_probeWall_label_eq_one_iff (a : ℳ p) (k : ℕ) :
    CompletedGroup.projection k (probeWall d ℳ p ℒ H h h' a).label = 1 ↔
      a = 0 ∨ k = 0 := by
  have hx := (moduleGradingEquiv d ℳ p ℒ p (initialCoefficient d ℳ p a)).property
  rw [coe_moduleGradingEquiv] at hx
  have he := (positiveDegrees d p).projection_expToCompletion_eq_one_iff
    (grading d ℳ p ℒ) hx k
  have hz : moduleInclusion d ℳ p ℒ
      ((moduleCoefficientsEquiv d ℳ p).symm (initialCoefficient d ℳ p a).val) = 0 ↔
      a = 0 := by
    rw [map_eq_zero_iff _ (LieAlgebra.SemiDirectSum.inl_injective _),
      LinearEquiv.map_eq_zero_iff]
    constructor
    · intro ha
      exact Subtype.ext (congrArg (fun x : shiftedSubmodule ℳ d.monoid p => (x : M)) ha)
    · rintro rfl
      rfl
  have hd : (positiveDegrees d p).degree (p, 1, 0) = 1 := by
    simp only [positiveDegrees_degree, mul_one]
    omega
  rw [hz, hd] at he
  simpa only [probeWall_label, initialCoefficient,
    show (k : ℤ) < 1 ↔ k = 0 by omega] using he

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- Include a finitely active base diagram as charge-zero cylinder walls. -/
def cylinderDiagram {ι : Type*} (D : DirectedDiagram (d := d) h H ι) :
    DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι where
  wall b := baseCylinder d ℳ p ℒ H h h' (D.wall b)
  finite_active := by
    simpa only [baseCylinder_label] using
      (baseGradedLieHom d ℳ p ℒ).hasFiniteSupport_completedMap D.finite_active

@[simp]
theorem cylinderDiagram_wall {ι : Type*} (D : DirectedDiagram (d := d) h H ι) (b : ι) :
    (cylinderDiagram d ℳ p ℒ H h h' D).wall b =
      baseCylinder d ℳ p ℒ H h h' (D.wall b) := (rfl)

/-- The actual finitely active initial family for the module probe: base cylinders
and one full probe wall. The coefficient is allowed to vanish. -/
def initialDiagram {ι : Type*} (D : DirectedDiagram (d := d) h H ι) (a : ℳ p) :
    DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
      (ι ⊕ Unit) :=
  (cylinderDiagram d ℳ p ℒ H h h' D).append
    (DirectedDiagram.ofFinite (fun _ : Unit => probeWall d ℳ p ℒ H h h' a))

@[simp]
theorem initialDiagram_wall_inl {ι : Type*} (D : DirectedDiagram (d := d) h H ι)
    (a : ℳ p) (b : ι) :
    (initialDiagram d ℳ p ℒ H h h' D a).wall (.inl b) =
      baseCylinder d ℳ p ℒ H h h' (D.wall b) := by simp [initialDiagram]

@[simp]
theorem initialDiagram_wall_inr {ι : Type*} (D : DirectedDiagram (d := d) h H ι)
    (a : ℳ p) (b : Unit) :
    (initialDiagram d ℳ p ℒ H h h' D a).wall (.inr b) =
      probeWall d ℳ p ℒ H h h' a := by simp [initialDiagram]

/-- An incoming base input gives an incoming probe input. -/
theorem initialDiagram_incoming {ι : Type*} (D : DirectedDiagram (d := d) h H ι)
    (a : ℳ p) (hD : ∀ b, (D.wall b).Incoming) (b : ι ⊕ Unit) :
    ((initialDiagram d ℳ p ℒ H h h' D a).wall b).Incoming := by
  cases b <;> simp [hD]

/-- Full affine hyperplanes remain full affine hyperplanes after adjoining the probe. -/
theorem initialDiagram_support_eq_hyperplane {ι : Type*}
    (D : DirectedDiagram (d := d) h H ι) (a : ℳ p)
    (hfull : ∀ b, ∃ c : ℝ, (D.wall b).support = {x | h.realCharacter (D.wall b).normal x = c})
    (b : ι ⊕ Unit) :
    ∃ c : ℝ, ((initialDiagram d ℳ p ℒ H h h' D a).wall b).support =
      {x | (h.prod h').realCharacter
        ((initialDiagram d ℳ p ℒ H h h' D a).wall b).normal x = c} := by
  cases b with
  | inl b =>
    obtain ⟨c, hc⟩ := hfull b
    exact ⟨c, by simpa only [initialDiagram_wall_inl] using
      baseCylinder_support_eq_hyperplane d ℳ p ℒ H h h' (D.wall b) hc⟩
  | inr b =>
    refine ⟨0, ?_⟩
    ext x
    simp

/-- The cylinder input together with its homogeneous probe admits a consistent
outgoing completion. The extra walls have a countable index type. -/
theorem exists_initialDiagram_outgoingCompletion [Module.Free ℤ Γ] {ι : Type*}
    (D : DirectedDiagram (d := d) h H ι) (a : ℳ p)
    (hfull : ∀ b, ∃ c : ℝ, (D.wall b).support = {x | h.realCharacter (D.wall b).normal x = c}) :
    ∃ (κ : Type) (_ : Countable κ)
      (F : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H)
        ((ι ⊕ Unit) ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (initialDiagram d ℳ p ℒ H h h' D a).wall F := by
  obtain ⟨κ, hκ, F, hF, _⟩ := (initialDiagram d ℳ p ℒ H h h' D a).exists_outgoingCompletion
    (initialDiagram_support_eq_hyperplane d ℳ p ℒ H h h' D a hfull)
  exact ⟨κ, hκ, F, hF⟩

end Mei.ModuleProbe
