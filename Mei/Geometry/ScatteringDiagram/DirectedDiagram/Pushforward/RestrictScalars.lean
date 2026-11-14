/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Scat
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RestrictScalars

/-!
# Pushing directed diagrams forward across a change of coefficient ring

Let `D` be a directed diagram for wall spaces `H` over a commutative `ℚ`-algebra `R`, let `H'`
be wall spaces over another commutative `ℚ`-algebra `S`, and let `P` be pushforward data
between the restrictions `H.restrictScalars K` and `H'.restrictScalars K` to a common scalar
ring `K`. The degree map of `P` may change the degree lattice and carry a cutoff modulus, and
its spatial map may move the supports. The cross-ring pushforward
`D.pushforwardRestrictScalars P` restricts scalars, pushes every wall forward along `P` and
undoes the restriction over `S` (`DirectedDiagram.pushforwardRestrictScalars_wall`).

Since restriction of scalars preserves and reflects consistency, equivalence and outgoing
completions, the cross-ring pushforward has the properties of `DirectedDiagram.pushforward`:

* consistency at a source cutoff `a` covering the modulus of a target order `k` gives
  consistency at `k` (`DirectedDiagram.LevelConsistent.pushforwardRestrictScalars`), and hence
  consistency is preserved (`DirectedDiagram.Consistent.pushforwardRestrictScalars`); the same
  holds for equivalence (`DirectedDiagram.LevelEquivalent.pushforwardRestrictScalars`,
  `DirectedDiagram.Equivalent.pushforwardRestrictScalars`);
* outgoing completions go to outgoing completions of the pushed input
  (`DirectedDiagram.IsOutgoingCompletion.pushforwardRestrictScalars`), and every outgoing
  completion of the pushed input is equivalent to the pushed completion
  (`DirectedDiagram.IsOutgoingCompletion.equivalent_pushforwardRestrictScalars`);
* the construction descends to completed and finite-order diagram classes
  (`DirectedDiagram.Class.pushforwardRestrictScalars`,
  `DirectedDiagram.LevelClass.pushforwardRestrictScalars`), and it commutes with forming the
  scattering class of a full-hyperplane input, at all orders
  (`DirectedDiagram.pushforwardRestrictScalars_scat`) and at a target order `k` from any source
  order covering its modulus (`DirectedDiagram.projection_pushforwardRestrictScalars_scat`).

Along fixed-degree coefficient data `DirectedWall.Pushforward.ofFixedDegree` the cross-ring
pushforward is the coefficient change `DirectedDiagram.mapRestrictScalars`
(`DirectedDiagram.pushforwardRestrictScalars_ofFixedDegree`); over a single ring, along the
scalar restriction of pushforward data, it is `DirectedDiagram.pushforward`
(`DirectedDiagram.pushforwardRestrictScalars_restrictScalars`); and successive cross-ring
pushforwards compose (`DirectedDiagram.pushforwardRestrictScalars_pushforwardRestrictScalars`).
Thus a coefficient change followed by a degree-changing pushforward is a single cross-ring
pushforward. Naturality of the path products themselves is not stated across the ring change.

This combines the coefficient changes and the pushforwards along tropical pairings of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i)
(arXiv:1503.06183v5); the completions are those of Theorem 2.6 there.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram

universe u v

variable {Γ Γ' Λ Λ' K R S V V' : Type*} {L L' : Type v} {ι κ : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing K] [CommRing R] [CommRing S] [Algebra ℚ K] [Algebra ℚ R] [Algebra ℚ S]
  [SMul K R] [SMul K S]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [IsScalarTower K R L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra K L'] [LieAlgebra ℚ L']
  [IsScalarTower K S L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ S L']
  [DecidableEq Γ] [DecidableEq Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule S L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  (P : DirectedWall.Pushforward d d' h h' (H.restrictScalars K) (H'.restrictScalars K))

section Basic

variable (D : DirectedDiagram (d := d) h H ι)

/-- Push every indexed wall of a directed diagram over `R` forward to wall spaces over `S`,
along pushforward data `P` between the wall spaces restricted to the common scalar ring `K`:
restrict scalars, push forward along `P` and undo the restriction over `S`. -/
def pushforwardRestrictScalars : DirectedDiagram (d := d') h' H' ι :=
  ((D.restrictScalars K).pushforward P).ofRestrictScalars

/-- The cross-ring pushforward is the pushforward of the restricted diagram, read back over the
target coefficient ring. -/
theorem pushforwardRestrictScalars_def :
    D.pushforwardRestrictScalars P = ((D.restrictScalars K).pushforward P).ofRestrictScalars :=
  (rfl)

/-- The cross-ring pushforward of a diagram is the cross-ring pushforward of each wall. -/
@[simp]
theorem pushforwardRestrictScalars_wall (j : ι) :
    (D.pushforwardRestrictScalars P).wall j = (D.wall j).pushforwardRestrictScalars P := by
  rw [pushforwardRestrictScalars_def, ofRestrictScalars_wall, pushforward_wall,
    restrictScalars_wall, DirectedWall.pushforwardRestrictScalars_def]

/-- Restricting the scalars of the cross-ring pushforward gives the pushforward of the
restricted diagram. -/
@[simp]
theorem restrictScalars_pushforwardRestrictScalars :
    (D.pushforwardRestrictScalars P).restrictScalars K = (D.restrictScalars K).pushforward P := by
  rw [pushforwardRestrictScalars_def, restrictScalars_ofRestrictScalars]

/-- A wall active at a target order `k` was active at any source order `a` covering the
modulus of `k`. -/
theorem active_pushforwardRestrictScalars_subset (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a) :
    (D.pushforwardRestrictScalars P).active k ⊆ D.active a := by
  rw [← active_restrictScalars (K := K), restrictScalars_pushforwardRestrictScalars,
    ← D.active_restrictScalars (K := K) a]
  exact (D.restrictScalars K).active_pushforward_subset P k ha

end Basic

section Transport

variable {D : DirectedDiagram (d := d) h H ι} {F : DirectedDiagram (d := d) h H κ} {P}

/-- Consistency at a source order `a` covering the modulus of a target order `k` gives
consistency of the cross-ring pushforward at `k`. -/
theorem LevelConsistent.pushforwardRestrictScalars {k a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (hD : D.LevelConsistent a) : (D.pushforwardRestrictScalars P).LevelConsistent k := by
  rw [← levelConsistent_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars]
  exact (levelConsistent_restrictScalars_iff.mpr hD).pushforward ha

/-- The cross-ring pushforward preserves consistency. -/
theorem Consistent.pushforwardRestrictScalars (hD : D.Consistent) :
    (D.pushforwardRestrictScalars P).Consistent := by
  rw [← consistent_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars]
  exact (consistent_restrictScalars_iff.mpr hD).pushforward

/-- Equivalence at a source order `a` covering the modulus of a target order `k` gives
equivalence of the cross-ring pushforwards at `k`. -/
theorem LevelEquivalent.pushforwardRestrictScalars {k a : ℕ} (ha : P.degreeMap.modulus k ≤ a)
    (hDF : D.LevelEquivalent F a) :
    (D.pushforwardRestrictScalars P).LevelEquivalent (F.pushforwardRestrictScalars P) k := by
  rw [← levelEquivalent_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars,
    restrictScalars_pushforwardRestrictScalars]
  exact (levelEquivalent_restrictScalars_iff.mpr hDF).pushforward ha

/-- The cross-ring pushforward preserves equivalence. -/
theorem Equivalent.pushforwardRestrictScalars (hDF : D.Equivalent F) :
    (D.pushforwardRestrictScalars P).Equivalent (F.pushforwardRestrictScalars P) := by
  rw [← equivalent_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars,
    restrictScalars_pushforwardRestrictScalars]
  exact (equivalent_restrictScalars_iff.mpr hDF).pushforward

variable {ι₀ ι' κ' : Type*} {D₀ : ι₀ → DirectedWall (d := d) h H}

/-- The cross-ring pushforward of an outgoing completion is an outgoing completion of the pushed
input, even when some labels die. -/
theorem IsOutgoingCompletion.pushforwardRestrictScalars
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).pushforwardRestrictScalars P)
      (E.pushforwardRestrictScalars P) := by
  rw [← isOutgoingCompletion_restrictScalars_iff (K := K),
    restrictScalars_pushforwardRestrictScalars]
  simp_rw [DirectedWall.restrictScalars_pushforwardRestrictScalars]
  exact (isOutgoingCompletion_restrictScalars_iff.mpr hE).pushforward

/-- Every outgoing completion of the cross-ring pushforward of an input is equivalent to the
cross-ring pushforward of any outgoing completion of the input. -/
theorem IsOutgoingCompletion.equivalent_pushforwardRestrictScalars
    {E : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {E' : DirectedDiagram (d := d') h' H' (ι₀ ⊕ κ')} (hE : IsOutgoingCompletion D₀ E)
    (hE' : IsOutgoingCompletion (fun j => (D₀ j).pushforwardRestrictScalars P) E') :
    E'.Equivalent (E.pushforwardRestrictScalars P) :=
  outgoingCompletion_unique hE' hE.pushforwardRestrictScalars

end Transport

section Class

/-- The cross-ring pushforward of a full-hyperplane input is a full-hyperplane input. -/
theorem pushforwardRestrictScalars_fullHyperplane (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a}) :
    ∀ j, ∃ a : ℝ, ((D.pushforwardRestrictScalars P).wall j).support =
      {x | h'.realCharacter ((D.pushforwardRestrictScalars P).wall j).normal x = a} := by
  simpa only [pushforwardRestrictScalars_def, ofRestrictScalars_wall,
    DirectedWall.ofRestrictScalars_support, DirectedWall.ofRestrictScalars_normal] using
    (D.restrictScalars K).pushforward_fullHyperplane P (by simpa using hfull)

/-- Push a completed diagram class forward across the change of coefficient ring. -/
def Class.pushforwardRestrictScalars : Class.{u} (d := d) (h := h) (H := H) →
    Class.{u} (d := d') (h := h') (H := H') :=
  Class.lift (fun D => (D.pushforwardRestrictScalars P).toClass)
    (fun _ _ hDF => (toClass_eq_iff _ _).mpr hDF.pushforwardRestrictScalars)

/-- Push a finite-order class forward across the change of coefficient ring, from any source
order `a` covering the modulus of the target order `k`. -/
def LevelClass.pushforwardRestrictScalars (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    LevelClass.{u} (d := d) (h := h) (H := H) a →
      LevelClass.{u} (d := d') (h := h') (H := H') k :=
  LevelClass.lift a (fun D => (D.pushforwardRestrictScalars P).toLevelClass k)
    (fun _ _ hDF => (toLevelClass_eq_iff _ _ k).mpr (hDF.pushforwardRestrictScalars ha))

/-- The class pushforward across the change of coefficient ring is computed on any
representative. -/
@[simp]
theorem Class.pushforwardRestrictScalars_toClass (D : DirectedDiagram (d := d) h H ι) :
    Class.pushforwardRestrictScalars P D.toClass = (D.pushforwardRestrictScalars P).toClass := by
  simp only [pushforwardRestrictScalars, lift_toClass]

/-- The finite-order class pushforward across the change of coefficient ring is computed on any
representative. -/
@[simp]
theorem LevelClass.pushforwardRestrictScalars_toLevelClass (D : DirectedDiagram (d := d) h H ι)
    (k : ℕ) {a : ℕ} (ha : P.degreeMap.modulus k ≤ a) :
    LevelClass.pushforwardRestrictScalars P k ha (D.toLevelClass a) =
      (D.pushforwardRestrictScalars P).toLevelClass k := by
  simp only [pushforwardRestrictScalars, lift_toLevelClass]

/-- The completed class pushforward across the change of coefficient ring is computed at any
source order covering the modulus of the target order. -/
theorem Class.projection_pushforwardRestrictScalars_of_le (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a) (x : Class.{u} (d := d) (h := h) (H := H)) :
    (pushforwardRestrictScalars P x).projection k =
      LevelClass.pushforwardRestrictScalars P k ha (x.projection a) := by
  induction x using Class.inductionOn with | _ D =>
    simp only [pushforwardRestrictScalars_toClass, projection_toClass,
      LevelClass.pushforwardRestrictScalars_toLevelClass]

variable [Module.Free ℤ Γ] [Module.Free ℤ Γ'] (D : DirectedDiagram (d := d) h H ι)
  (hfull : ∀ j, ∃ a : ℝ,
    (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})

/-- Forming the canonical outgoing scattering class commutes with the cross-ring
pushforward. -/
theorem pushforwardRestrictScalars_scat :
    Class.pushforwardRestrictScalars P (D.Scat hfull) =
      (D.pushforwardRestrictScalars P).Scat
        (D.pushforwardRestrictScalars_fullHyperplane P hfull) := by
  obtain ⟨η, F, hF, hcF⟩ := D.scat_spec hfull
  rw [hcF, Class.pushforwardRestrictScalars_toClass]
  symm
  apply scat_eq_toClass
  have hinput : (D.pushforwardRestrictScalars P).wall =
      fun j => (D.wall j).pushforwardRestrictScalars P :=
    funext (pushforwardRestrictScalars_wall P D)
  rw [hinput]
  exact hF.pushforwardRestrictScalars

/-- The order-`k` scattering class of the cross-ring pushforward is pushed forward from any
source order covering the modulus of `k`. -/
theorem projection_pushforwardRestrictScalars_scat (k : ℕ) {a : ℕ}
    (ha : P.degreeMap.modulus k ≤ a) :
    ((D.pushforwardRestrictScalars P).Scat
        (D.pushforwardRestrictScalars_fullHyperplane P hfull)).projection k =
      LevelClass.pushforwardRestrictScalars P k ha ((D.Scat hfull).projection a) := by
  rw [← D.pushforwardRestrictScalars_scat P hfull,
    Class.projection_pushforwardRestrictScalars_of_le P k ha]

end Class

section Comparison

variable (D : DirectedDiagram (d := d) h H ι)

/-- Along fixed-degree coefficient data, the cross-ring pushforward is the coefficient change
`DirectedDiagram.mapRestrictScalars`. -/
@[simp]
theorem pushforwardRestrictScalars_ofFixedDegree {ℳ : Γ → Submodule S L'} [GradedLieAlgebra ℳ]
    [IsPositiveGrading d ℳ] {H' : DirectedWallSpaces ρ ℳ}
    (f : GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars K)
      (fun n => (ℳ n).restrictScalars K))
    (hf : ∀ n m, ∀ x ∈ (H.restrictScalars K).wall n m, f x ∈ (H'.restrictScalars K).wall n m) :
    D.pushforwardRestrictScalars (DirectedWall.Pushforward.ofFixedDegree f hf) =
      D.mapRestrictScalars f hf := by
  rw [pushforwardRestrictScalars_def, pushforward_ofFixedDegree, mapRestrictScalars_def]

omit [CommRing S] [Algebra ℚ S] [SMul K S] [LieAlgebra S L'] [IsScalarTower K S L']
  [IsScalarTower ℚ S L'] in
/-- Over a single coefficient ring, the cross-ring pushforward along the scalar restriction of
pushforward data is the pushforward. -/
@[simp]
theorem pushforwardRestrictScalars_restrictScalars [LieAlgebra R L'] [IsScalarTower K R L']
    [IsScalarTower ℚ R L'] {ℳ : Γ' → Submodule R L'} [GradedLieAlgebra ℳ]
    [IsPositiveGrading d' ℳ] {H' : DirectedWallSpaces ρ' ℳ}
    (P : DirectedWall.Pushforward d d' h h' H H') :
    D.pushforwardRestrictScalars (P.restrictScalars K) = D.pushforward P := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Successive cross-ring pushforwards over a common scalar ring `K` agree with the cross-ring
pushforward along the composite data. -/
@[simp]
theorem pushforwardRestrictScalars_pushforwardRestrictScalars {Γ'' Λ'' T V'' : Type*}
    {L'' : Type v} [AddCommGroup Γ''] [AddCommGroup Λ''] [CommRing T] [Algebra ℚ T] [SMul K T]
    [LieRing L''] [LieAlgebra T L''] [LieAlgebra K L''] [LieAlgebra ℚ L'']
    [IsScalarTower K T L''] [IsScalarTower ℚ K L''] [IsScalarTower ℚ T L''] [DecidableEq Γ'']
    [NormedAddCommGroup V''] [NormedSpace ℝ V''] {ρ'' : Γ'' →+ Λ''}
    {ℋ : Γ'' → Submodule T L''} {d'' : PositiveDegrees Γ''} [GradedLieAlgebra ℋ]
    [IsPositiveGrading d'' ℋ] {i'' : Λ'' →+ V''} {h'' : TauCeti.Toric.IsIntegralLattice i''}
    {H'' : DirectedWallSpaces ρ'' ℋ}
    (Q : DirectedWall.Pushforward d' d'' h' h'' (H'.restrictScalars K) (H''.restrictScalars K)) :
    (D.pushforwardRestrictScalars P).pushforwardRestrictScalars Q =
      D.pushforwardRestrictScalars (Q.comp P) := by
  apply DirectedDiagram.ext
  funext j
  simp

end Comparison

end Mei.DirectedDiagram
