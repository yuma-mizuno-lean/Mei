/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Completion
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# The outgoing scattering class under pushforward

Pushing directed diagrams forward along a degree-changing graded Lie map with a compatible
spatial affine equivalence preserves equivalence, so it descends to completed diagram
classes, and at finite order from any source cutoff covering the cutoff modulus. A full
affine hyperplane support stays a full hyperplane cut out by the image normal, with offset
rescaled and translated. Forming the canonical outgoing scattering class commutes with
pushforward. The completion theorem is Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5),
Theorem 2.6.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei

universe u v

variable {Γ Γ' Λ Λ' R V V' : Type*} {L L' : Type v} {ι : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [DecidableEq Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (P : DirectedWall.Pushforward d d' h h' H H')

/-- A full affine hyperplane support is pushed to a full affine hyperplane cut out by the
image normal. -/
theorem DirectedWall.pushforward_support_eq_hyperplane (W : DirectedWall (d := d) h H)
    {a : ℝ} (ha : W.support = {x | h.realCharacter W.normal x = a}) :
    ∃ b : ℝ, (W.pushforward P).support =
      {y | h'.realCharacter (W.pushforward P).normal y = b} := by
  obtain ⟨r, hr0, hr⟩ := P.exists_realCharacter_normalMap_apply W.normal
  let c := h'.realCharacter (P.normalMap W.normal) (P.spatialMap 0)
  have hval (x : V) : h'.realCharacter (P.normalMap W.normal) (P.spatialMap x) =
      r * h.realCharacter W.normal x + c := by
    have hx := P.spatialMap.toAffineEquiv.map_vadd (0 : V) x
    simp only [vadd_eq_add, add_zero, ContinuousAffineEquiv.coe_coe] at hx
    rw [hx, map_add, hr]
  refine ⟨r * a + c, ?_⟩
  rw [pushforward_support, ha, pushforward_normal]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_ofPred_eq, hval, Set.mem_ofPred_eq.mp hx]
  · intro hy
    refine ⟨P.spatialMap.symm y, ?_, P.spatialMap.apply_symm_apply y⟩
    have hv := hval (P.spatialMap.symm y)
    rw [ContinuousAffineEquiv.apply_symm_apply] at hv
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
    simp only [Set.mem_ofPred_eq] at hy ⊢
    apply mul_left_cancel₀ hr'
    linarith

namespace DirectedDiagram

/-- Pushforward preserves full-hyperplane inputs. -/
theorem pushforward_fullHyperplane {ι : Type*} (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a}) :
    ∀ j, ∃ a : ℝ, ((D.pushforward P).wall j).support =
      {x | h'.realCharacter ((D.pushforward P).wall j).normal x = a} := by
  intro j
  obtain ⟨a, ha⟩ := hfull j
  rw [pushforward_wall]
  exact (D.wall j).pushforward_support_eq_hyperplane P ha

/-- Push a completed diagram class forward. -/
def Class.pushforward : Class.{u} (d := d) (h := h) (H := H) →
    Class.{u} (d := d') (h := h') (H := H') :=
  Class.lift (fun D => (D.pushforward P).toClass)
    (fun _ _ hDF => (toClass_eq_iff _ _).mpr hDF.pushforward)

/-- Push a finite-order class forward from any source cutoff covering the target modulus. -/
def LevelClass.pushforward (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    LevelClass.{u} (d := d) (h := h) (H := H) a →
      LevelClass.{u} (d := d') (h := h') (H := H') k :=
  LevelClass.lift a (fun D => (D.pushforward P).toLevelClass k)
    (fun _ _ hDF => (toLevelClass_eq_iff _ _ k).mpr (hDF.pushforward ha))

/-- The class pushforward is computed on any representative. -/
@[simp]
theorem Class.pushforward_toClass (D : DirectedDiagram (d := d) h H ι) :
    Class.pushforward P D.toClass = (D.pushforward P).toClass := by
  simp only [pushforward, lift_toClass]

/-- The finite-order class pushforward is computed on any representative. -/
@[simp]
theorem LevelClass.pushforward_toLevelClass (D : DirectedDiagram (d := d) h H ι) (k : ℕ)
    {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    LevelClass.pushforward P k ha (D.toLevelClass a) = (D.pushforward P).toLevelClass k := by
  simp only [pushforward, lift_toLevelClass]

/-- Completed pushforward is computed at any sufficiently fine source projection. -/
theorem Class.projection_pushforward_of_le (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (x : Class.{u} (d := d) (h := h) (H := H)) :
    (pushforward P x).projection k = LevelClass.pushforward P k ha (x.projection a) := by
  induction x using Class.inductionOn with | _ D =>
    simp only [pushforward_toClass, projection_toClass, LevelClass.pushforward_toLevelClass]

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ'] (D : DirectedDiagram (d := d) h H ι)
  (hfull : ∀ j, ∃ a : ℝ,
    (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})

/-- Forming the canonical outgoing scattering class commutes with pushforward. -/
theorem pushforward_scat :
    Class.pushforward P (D.Scat hfull) =
      (D.pushforward P).Scat (D.pushforward_fullHyperplane P hfull) := by
  obtain ⟨η, F, hF, hcF⟩ := D.scat_spec hfull
  rw [hcF, Class.pushforward_toClass]
  symm
  apply scat_eq_toClass
  have hinput : (D.pushforward P).wall = fun j => (D.wall j).pushforward P :=
    funext (pushforward_wall D P)
  rw [hinput]
  exact hF.pushforward

/-- The order-`k` scattering class is pushed forward from any source order covering the
modulus. -/
theorem projection_pushforward_scat (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    ((D.pushforward P).Scat (D.pushforward_fullHyperplane P hfull)).projection k =
      LevelClass.pushforward P k ha ((D.Scat hfull).projection a) := by
  rw [← D.pushforward_scat P hfull, Class.projection_pushforward_of_le P k ha]

end DirectedDiagram
end Mei
