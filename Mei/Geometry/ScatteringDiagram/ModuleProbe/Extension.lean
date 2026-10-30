/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Limit
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Chamber

/-!
# Probe coefficients at every allowed base endpoint

At a fixed cutoff the generic probe coefficient extends uniquely by consistent
base transport to every endpoint outside the active base supports. Different
cutoffs may use different generic points. Their extensions commute with
truncation, giving completed coefficients without genericity at the endpoint.

These are probe-derived parallel coefficients. Identification with sums of
broken lines is a separate theorem.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ)

local notation "F" => d.shiftedFiltration ℳ p
local notation "A" => d.shiftedLieFiltration ℒ ℳ p

/-- Any finite exceptional arrangement has a generic point allowed by the base
diagram at the prescribed cutoff. An existing allowed endpoint witnesses that
the open base complement is nonempty. -/
private theorem exists_generic_allowed (k : ℕ) (T : ExceptionalArrangement V)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    ∃ z : WallComplement (fun c : B.active k => (B.wall c).support), T.IsGeneric z.val := by
  let := h.finiteDimensional
  have hopen : IsOpen {z : V | ∀ c : B.active k, z ∉ (B.wall c).support} := by
    simpa only [ofPred_forall, compl_def] using
      isOpen_iInter_of_finite
        (fun c : B.active k => (B.wall c).isConvexPolyhedron.isClosed.isOpen_compl)
  obtain ⟨z, hz, hT⟩ := T.dense_isGeneric.inter_open_nonempty _ hopen ⟨x.val, x.notMem⟩
  exact ⟨⟨z, hz⟩, hT⟩

private def coefficientAnchor (k : ℕ)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :=
  (exists_generic_allowed (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k
    (coefficientArrangement d ℳ p ℒ H h h' D k) x).choose

private theorem coefficientAnchor_generic (k : ℕ)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) :
    (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric
      (coefficientAnchor d ℳ p ℒ H h h' D B k x).val :=
  (exists_generic_allowed (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) k
    (coefficientArrangement d ℳ p ℒ H h h' D k) x).choose_spec

/-- The endpoint only witnesses nonemptiness of the allowed locus in a proof of
the same existential proposition. Proof irrelevance makes the chosen anchor
independent of that witness. -/
private theorem coefficientAnchor_eq (k : ℕ)
    (x y : WallComplement (fun c : B.active k => (B.wall c).support)) :
    coefficientAnchor d ℳ p ℒ H h h' D B k x =
      coefficientAnchor d ℳ p ℒ H h h' D B k y := by
  unfold coefficientAnchor
  rfl

/-- The probe coefficient extended to every finite-order allowed base endpoint
by consistent base transport from a generic allowed point. -/
def extendedCoefficientField (k : ℕ) (hBc : B.LevelConsistent k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support)) : (F).quotient k :=
  (A).truncatedBCHAction d ℒ k
    (B.levelTransport k hBc (coefficientAnchor d ℳ p ℒ H h h' D B k x) x)
    (coefficientField d ℳ p ℒ H h h' D k
      (coefficientAnchor d ℳ p ℒ H h h' D B k x).val
      (coefficientAnchor_generic d ℳ p ℒ H h h' D B k x))

/-- Every generic allowed point can compute the extension. In particular its
value is independent of the generic point chosen in its definition. -/
theorem extendedCoefficientField_eq_action (k : ℕ) (hBc : B.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (x z : WallComplement (fun c : B.active k => (B.wall c).support))
    (hz : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric z.val) :
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x =
      (A).truncatedBCHAction d ℒ k (B.levelTransport k hBc z x)
        (coefficientField d ℳ p ℒ H h h' D k z.val hz) := by
  let a := coefficientAnchor d ℳ p ℒ H h h' D B k x
  obtain ⟨γ⟩ := B.exists_level_path k a z
  have he := coefficientField_eq_truncatedBCHAction_levelPathProduct
    d ℳ p ℒ H h h' D B k hD hB γ
    (coefficientAnchor_generic d ℳ p ℒ H h h' D B k x) hz
  rw [← B.levelTransport_eq_levelPathProduct hBc γ] at he
  unfold extendedCoefficientField
  rw [he, ← LinearEquiv.mul_apply, ← MonoidHom.map_mul]
  rw [← B.levelTransport_comp]

/-- The extension recovers the original finite probe coefficient wherever that
coefficient was defined. -/
theorem extendedCoefficientField_eq_coefficientField (k : ℕ) (hBc : B.LevelConsistent k)
    (hD : D.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (x : WallComplement (fun c : B.active k => (B.wall c).support))
    (hx : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val) :
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x =
      coefficientField d ℳ p ℒ H h h' D k x.val hx := by
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBc hD hB x x hx]
  simp

/-- The extended coefficients obey the base transport equation at all allowed
endpoints. This follows from their common anchor and consistent base transport;
agreement with the generic probe field requires the separate probe hypotheses. -/
theorem extendedCoefficientField_eq_transport (k : ℕ) (hBc : B.LevelConsistent k)
    (x y : WallComplement (fun c : B.active k => (B.wall c).support)) :
    extendedCoefficientField d ℳ p ℒ H h h' D B k hBc y =
      (A).truncatedBCHAction d ℒ k (B.levelTransport k hBc x y)
        (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc x) := by
  unfold extendedCoefficientField
  simp only [coefficientAnchor_eq d ℳ p ℒ H h h' D B k x y]
  rw [← LinearEquiv.mul_apply, ← MonoidHom.map_mul, ← B.levelTransport_comp]

/-- The extension is the unique family obeying base transport and recovering
the actual generic probe coefficients. -/
theorem extendedCoefficientField_unique (k : ℕ) (hBc : B.LevelConsistent k)
    (f : WallComplement (fun c : B.active k => (B.wall c).support) → (F).quotient k)
    (hf : ∀ x y, f y = (A).truncatedBCHAction d ℒ k (B.levelTransport k hBc x y) (f x))
    (hgeneric : ∀ x (hx : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val),
      f x = coefficientField d ℳ p ℒ H h h' D k x.val hx) :
    f = extendedCoefficientField d ℳ p ℒ H h h' D B k hBc := by
  funext x
  rw [hf (coefficientAnchor d ℳ p ℒ H h h' D B k x) x,
    hgeneric _ (coefficientAnchor_generic d ℳ p ℒ H h h' D B k x)]
  rfl

/-- On the finite active-wall complement, the extended coefficients are locally
constant. The transport equation also specifies their change across base walls. -/
theorem isLocallyConstant_extendedCoefficientField (k : ℕ) (hBc : B.LevelConsistent k) :
    IsLocallyConstant (fun x : {x : V // ∀ c : B.active k, x ∉ (B.wall c).support} =>
      extendedCoefficientField d ℳ p ℒ H h h' D B k hBc ⟨x.val, x.property⟩) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let z : WallComplement (fun c : B.active k => (B.wall c).support) := ⟨x.val, x.property⟩
  have hc := (B.isLocallyConstant_levelTransport hBc z).comp
    (fun g => (A).truncatedBCHAction d ℒ k g
      (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc z))
  have he : (fun y : {y : V // ∀ c : B.active k, y ∉ (B.wall c).support} =>
      extendedCoefficientField d ℳ p ℒ H h h' D B k hBc ⟨y.val, y.property⟩) =
      (fun y : {y : V // ∀ c : B.active k, y ∉ (B.wall c).support} =>
        (A).truncatedBCHAction d ℒ k (B.levelTransport k hBc z ⟨y.val, y.property⟩)
          (extendedCoefficientField d ℳ p ℒ H h h' D B k hBc z)) := by
    funext y
    exact extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k hBc z _
  filter_upwards [hc.eventually_eq x] with y hy
  exact (congrFun he y).trans (hy.trans (congrFun he x).symm)

/-- Lowering the cutoff preserves the extended coefficients. Only a common
finite generic point is needed; the two exceptional arrangements need not nest. -/
@[simp]
theorem transition_extendedCoefficientField {k l : ℕ} (hkl : k ≤ l)
    (hBk : B.LevelConsistent k) (hBl : B.LevelConsistent l)
    (hD : D.LevelConsistent (l + 1))
    (hBk' : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    (hBl' : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) l)
    (x : WallComplement (fun c : B.active l => (B.wall c).support)) :
    (F).transition hkl (extendedCoefficientField d ℳ p ℒ H h h' D B l hBl x) =
      extendedCoefficientField d ℳ p ℒ H h h' D B k hBk
        ((WallComplement.restrictPrefunctor (fun c : B.active l => (B.wall c).support)
          (Set.inclusion (B.active_mono hkl))).obj x) := by
  let r := WallComplement.restrictPrefunctor (fun c : B.active l => (B.wall c).support)
    (Set.inclusion (B.active_mono hkl))
  obtain ⟨z, hz⟩ := exists_generic_allowed (d := d) (ℒ := ℒ) (H := H) (h := h) (B := B) l
    ((coefficientArrangement d ℳ p ℒ H h h' D k).union
      (coefficientArrangement d ℳ p ℒ H h h' D l)) x
  obtain ⟨hzk, hzl⟩ := ExceptionalArrangement.isGeneric_union.mp hz
  rw [extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B l hBl hD
      hBl' x z hzl,
    (A).transition_truncatedBCHAction d ℒ hkl,
    B.truncation_levelTransport hkl hBk hBl,
    transition_coefficientField d ℳ p ℒ H h h' D hkl hD z.val hzk hzl,
    extendedCoefficientField_eq_action d ℳ p ℒ H h h' D B k hBk
      (hD.mono (Nat.add_le_add_right hkl 1)) hBk' (r.obj x) (r.obj z) hzk]
  rfl

/-- Compatible extended coefficients at an all-order allowed endpoint. No
genericity condition on the endpoint is required at any cutoff. -/
def completedExtendedCoefficientField (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B)) (x : B.Point) : (F).completion :=
  ⟨fun k => extendedCoefficientField d ℳ p ℒ H h h' D B k.unop ((B.consistent_iff.mp hBc) k.unop)
      (CommonWallComplement.projection k.unop x),
    ((F).mem_completionSubmodule_iff _).mpr fun k l hkl =>
      transition_extendedCoefficientField d ℳ p ℒ H h h' D B hkl
        ((B.consistent_iff.mp hBc) k) ((B.consistent_iff.mp hBc) l)
        ((D.consistent_iff.mp hD) (l + 1)) ((DirectedDiagram.equivalent_iff _ _).mp hB k)
        ((DirectedDiagram.equivalent_iff _ _).mp hB l)
        (CommonWallComplement.projection l x)⟩

/-- The completed extension projects to its finite-order extension. -/
@[simp]
theorem projection_completedExtendedCoefficientField (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B)) (x : B.Point) (k : ℕ) :
    (F).projection k (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) =
      extendedCoefficientField d ℳ p ℒ H h h' D B k ((B.consistent_iff.mp hBc) k)
        (CommonWallComplement.projection k x) := by
  rw [completedExtendedCoefficientField, ModuleFiltration.projection_mk]

/-- The completed extension agrees with the earlier generic-endpoint
construction wherever the latter was defined. -/
theorem completedExtendedCoefficientField_eq_completedCoefficientField
    (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B)) (x : B.Point)
    (hx : ∀ k, (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val) :
    completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x =
      completedCoefficientField d ℳ p ℒ H h h' D hD x.val hx := by
  apply (F).completion_ext
  intro k
  rw [projection_completedExtendedCoefficientField, projection_completedCoefficientField]
  exact extendedCoefficientField_eq_coefficientField d ℳ p ℒ H h h' D B k
    ((B.consistent_iff.mp hBc) k)
    ((D.consistent_iff.mp hD) (k + 1)) ((DirectedDiagram.equivalent_iff _ _).mp hB k) _ (hx k)

/-- Completed probe coefficients obey base transport between every pair of
all-order allowed endpoints. Auxiliary genericity and height choices disappear. -/
theorem completedExtendedCoefficientField_eq_transport
    (hD : D.Consistent) (hBc : B.Consistent)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).Equivalent
      (cylinderDiagram d ℳ p ℒ H h h' B)) (x y : B.Point) :
    completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB y =
      (A).completedBCHAction d ℒ (B.transport hBc x y)
        (completedExtendedCoefficientField d ℳ p ℒ H h h' D B hD hBc hB x) := by
  apply (F).completion_ext
  intro k
  rw [(A).projection_completedBCHAction, projection_completedExtendedCoefficientField,
    projection_completedExtendedCoefficientField, B.projection_transport_eq_levelTransport]
  exact extendedCoefficientField_eq_transport d ℳ p ℒ H h h' D B k ((B.consistent_iff.mp hBc) k)
    _ _

end Mei.ModuleProbe
