/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Map
public import Mei.Geometry.ScatteringDiagram.WallSpace.RestrictScalars

/-!
# Restriction of scalars for directed walls

Let `H` be directed wall spaces of a positively graded Lie algebra over a commutative
`ℚ`-algebra `R`, and let `K` be a smaller scalar ring. The restricted wall spaces
`H.restrictScalars K` have the same elements, and the scalar-restriction comparison
`PositiveDegrees.completedBCHRestrictScalarsEquiv` identifies the completed BCH groups and their
wall groups (`DirectedWallSpaces.mem_wallGroup_restrictScalars_iff`). Hence a directed wall for
`H` is a directed wall for the restricted wall spaces with the same normal, supported ray and
support (`DirectedWall.restrictScalars`), and conversely (`DirectedWall.ofRestrictScalars`);
the two constructions are mutually inverse.

This allows coefficient maps between different coefficient rings over a common base ring `K`.
A `K`-linear fixed-degree graded Lie homomorphism `f` between the restricted gradings of
algebras over `R` and over `S` that preserves the restricted wall spaces maps a wall for `H` to
a wall for the wall spaces `H'` over `S` (`DirectedWall.mapRestrictScalars`): restrict scalars,
apply the fixed-degree map `DirectedWall.map` and undo the restriction. The normal, supported
ray and support are retained, so incomingness and outgoingness are preserved.

Degree-changing pushforwards combine with these coefficient changes. Pushforward data `P` between
wall spaces over `R` restrict to pushforward data between the restricted wall spaces
(`DirectedWall.Pushforward.restrictScalars`), and restriction of scalars commutes with pushforward
(`DirectedWall.restrictScalars_pushforward`). For pushforward data `P` between
`H.restrictScalars K` and `H'.restrictScalars K`, with `H'` over `S`, the cross-ring pushforward
`W.pushforwardRestrictScalars P` restricts scalars, pushes forward along `P` and undoes the
restriction over `S`. It has the image normal, the reindexed ray and the spatial image of the
support, and it preserves and reflects incomingness and outgoingness
(`DirectedWall.incoming_pushforwardRestrictScalars_iff`,
`DirectedWall.outgoing_pushforwardRestrictScalars_iff`). Along fixed-degree data it is
`DirectedWall.mapRestrictScalars` (`DirectedWall.pushforwardRestrictScalars_ofFixedDegree`), along
the restriction of data over a single ring it is `DirectedWall.pushforward`
(`DirectedWall.pushforwardRestrictScalars_restrictScalars`), and successive cross-ring
pushforwards over `K` compose
(`DirectedWall.pushforwardRestrictScalars_pushforwardRestrictScalars`).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading GradedLieHom)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedWall

universe u

variable {Γ Λ K R V : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing K] [CommRing R] [Algebra ℚ K] [Algebra ℚ R] [SMul K R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [IsScalarTower K R L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}

section Restrict

variable (K) in
/-- Regard a directed wall as a wall for the wall spaces over the smaller scalar ring `K`, with
the same normal, supported ray and support, and the label transported by the inverse
scalar-restriction comparison of completed BCH groups. -/
def restrictScalars (W : DirectedWall (d := d) h H) :
    DirectedWall (d := d) h (H.restrictScalars K) where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := (d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label
  label_mem := (H.mem_wallGroup_restrictScalars_iff W.ray W.normal _).mp (by
    rw [MulEquiv.apply_symm_apply]
    exact W.label_mem)

/-- Regard a directed wall for the restricted wall spaces as a wall for the original wall
spaces, with the label transported by the scalar-restriction comparison. -/
def ofRestrictScalars (W : DirectedWall (d := d) h (H.restrictScalars K)) :
    DirectedWall (d := d) h H where
  normal := W.normal
  normal_ne_zero := W.normal_ne_zero
  ray := W.ray
  normal_direction := W.normal_direction
  support := W.support
  support_nonempty := W.support_nonempty
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := d.completedBCHRestrictScalarsEquiv (R := K) ℒ W.label
  label_mem := (H.mem_wallGroup_restrictScalars_iff W.ray W.normal _).mpr W.label_mem

variable (W : DirectedWall (d := d) h H) (W' : DirectedWall (d := d) h (H.restrictScalars K))

/-- Restricting scalars keeps the normal. -/
@[simp]
theorem restrictScalars_normal : (W.restrictScalars K).normal = W.normal := (rfl)

/-- Restricting scalars keeps the supported ray. -/
@[simp]
theorem restrictScalars_ray : (W.restrictScalars K).ray = W.ray := (rfl)

/-- Restricting scalars keeps the support. -/
@[simp]
theorem restrictScalars_support : (W.restrictScalars K).support = W.support := (rfl)

/-- The restricted label is the inverse scalar-restriction comparison of the label. -/
@[simp]
theorem restrictScalars_label :
    (W.restrictScalars K).label = (d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label :=
  (rfl)

/-- Undoing a restriction of scalars keeps the normal. -/
@[simp]
theorem ofRestrictScalars_normal : W'.ofRestrictScalars.normal = W'.normal := (rfl)

/-- Undoing a restriction of scalars keeps the supported ray. -/
@[simp]
theorem ofRestrictScalars_ray : W'.ofRestrictScalars.ray = W'.ray := (rfl)

/-- Undoing a restriction of scalars keeps the support. -/
@[simp]
theorem ofRestrictScalars_support : W'.ofRestrictScalars.support = W'.support := (rfl)

/-- The label is transported by the scalar-restriction comparison. -/
@[simp]
theorem ofRestrictScalars_label :
    W'.ofRestrictScalars.label = d.completedBCHRestrictScalarsEquiv (R := K) ℒ W'.label := (rfl)

/-- Undoing a restriction of scalars recovers the wall. -/
@[simp]
theorem ofRestrictScalars_restrictScalars : (W.restrictScalars K).ofRestrictScalars = W := by
  apply DirectedWall.ext <;> simp

/-- Restricting the scalars of a wall obtained from the restricted wall spaces recovers it. -/
@[simp]
theorem restrictScalars_ofRestrictScalars : W'.ofRestrictScalars.restrictScalars K = W' := by
  apply DirectedWall.ext <;> simp

/-- Restricting scalars keeps the label trivial exactly when it was trivial. -/
theorem restrictScalars_label_eq_one_iff : (W.restrictScalars K).label = 1 ↔ W.label = 1 := by
  rw [restrictScalars_label, MulEquiv.map_eq_one_iff]

/-- Restricting scalars keeps the label trivial at a finite order exactly when it was trivial
there. -/
theorem projection_restrictScalars_label_eq_one_iff (k : ℕ) :
    TauCeti.CompletedGroup.projection k (W.restrictScalars K).label = 1 ↔
      TauCeti.CompletedGroup.projection k W.label = 1 := by
  rw [← PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_eq_one_iff,
    restrictScalars_label, MulEquiv.apply_symm_apply]

/-- Restricting scalars preserves and reflects incomingness. -/
@[simp]
theorem incoming_restrictScalars_iff : (W.restrictScalars K).Incoming ↔ W.Incoming := by
  simp only [incoming_iff, restrictScalars_ray, restrictScalars_support]

/-- Restricting scalars preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_restrictScalars_iff : (W.restrictScalars K).Outgoing ↔ W.Outgoing := by
  simp only [outgoing_iff, restrictScalars_ray, restrictScalars_support]

end Restrict

section Map

variable {S : Type*} {L' : Type u} [CommRing S] [Algebra ℚ S] [SMul K S]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra K L'] [LieAlgebra ℚ L']
  [IsScalarTower K S L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ S L']
  {ℳ : Γ → Submodule S L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d ℳ]
  {H' : DirectedWallSpaces ρ ℳ}
  (f : GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars K)
    (fun n => (ℳ n).restrictScalars K))
  (hf : ∀ n m, ∀ x ∈ (H.restrictScalars K).wall n m, f x ∈ (H'.restrictScalars K).wall n m)
  (W : DirectedWall (d := d) h H)

/-- Change the coefficient ring of a directed wall along a `K`-linear fixed-degree graded Lie
homomorphism `f` of the restricted gradings preserving the restricted wall spaces: restrict
scalars, apply `f` to the label and undo the restriction. The normal, supported ray and support
are retained. -/
def mapRestrictScalars : DirectedWall (d := d) h H' :=
  ((W.restrictScalars K).map f hf).ofRestrictScalars

/-- The coefficient change is the fixed-degree map of the restricted wall, read back over the
target coefficient ring. -/
theorem mapRestrictScalars_def :
    W.mapRestrictScalars f hf = ((W.restrictScalars K).map f hf).ofRestrictScalars := (rfl)

/-- Changing the coefficient ring keeps the normal. -/
@[simp]
theorem mapRestrictScalars_normal : (W.mapRestrictScalars f hf).normal = W.normal := by
  rw [mapRestrictScalars_def, ofRestrictScalars_normal, map_normal, restrictScalars_normal]

/-- Changing the coefficient ring keeps the supported ray. -/
@[simp]
theorem mapRestrictScalars_ray : (W.mapRestrictScalars f hf).ray = W.ray := by
  rw [mapRestrictScalars_def, ofRestrictScalars_ray, map_ray, restrictScalars_ray]

/-- Changing the coefficient ring keeps the support. -/
@[simp]
theorem mapRestrictScalars_support : (W.mapRestrictScalars f hf).support = W.support := by
  rw [mapRestrictScalars_def, ofRestrictScalars_support, map_support, restrictScalars_support]

/-- The label is transported by `f` through the two scalar-restriction comparisons. -/
@[simp]
theorem mapRestrictScalars_label :
    (W.mapRestrictScalars f hf).label = d.completedBCHRestrictScalarsEquiv (R := K) ℳ
      (f.completedMap ((d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label)) := by
  rw [mapRestrictScalars_def, ofRestrictScalars_label, map_label, restrictScalars_label]

/-- Restricting the scalars of the coefficient change gives the fixed-degree map of the
restricted wall. -/
@[simp]
theorem restrictScalars_mapRestrictScalars :
    (W.mapRestrictScalars f hf).restrictScalars K = (W.restrictScalars K).map f hf := by
  rw [mapRestrictScalars_def, restrictScalars_ofRestrictScalars]

/-- Changing the coefficient ring preserves and reflects incomingness. -/
@[simp]
theorem incoming_mapRestrictScalars_iff : (W.mapRestrictScalars f hf).Incoming ↔ W.Incoming := by
  simp only [incoming_iff, mapRestrictScalars_ray, mapRestrictScalars_support]

/-- Changing the coefficient ring preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_mapRestrictScalars_iff : (W.mapRestrictScalars f hf).Outgoing ↔ W.Outgoing := by
  simp only [outgoing_iff, mapRestrictScalars_ray, mapRestrictScalars_support]

end Map

section Pushforward

variable {Γ' Γ'' Λ' Λ'' S T V' V'' : Type*} {L' L'' : Type u}
  [AddCommGroup Γ'] [AddCommGroup Γ''] [AddCommGroup Λ'] [AddCommGroup Λ'']
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup V''] [NormedSpace ℝ V'']
  {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''} {d' : PositiveDegrees Γ'} {d'' : PositiveDegrees Γ''}
  {i' : Λ' →+ V'} {i'' : Λ'' →+ V''}
  {h' : TauCeti.Toric.IsIntegralLattice i'} {h'' : TauCeti.Toric.IsIntegralLattice i''}

section Data

omit [Algebra ℚ K] [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L]
  [DecidableEq Γ] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

variable [LieRing L'] [LieAlgebra R L'] [LieAlgebra K L'] [IsScalarTower K R L']
  {ℳ : Γ' → Submodule R L'} {H' : DirectedWallSpaces ρ' ℳ}

variable (K) in
/-- Regard pushforward data between wall spaces over `R` as pushforward data between the wall
spaces restricted to the smaller scalar ring `K`, with the scalar restriction of the Lie map and
the same degree, ray, normal and spatial maps. -/
def Pushforward.restrictScalars (P : Pushforward d d' h h' H H') :
    Pushforward d d' h h' (H.restrictScalars K) (H'.restrictScalars K) where
  degreeMap := P.degreeMap
  lieHom := P.lieHom.restrictScalars K
  rayMap := P.rayMap
  mem_rayDegrees_rayMap := P.mem_rayDegrees_rayMap
  normalMap := P.normalMap
  wall_mem n hn m x hx := by simpa using P.wall_mem n hn m x (by simpa using hx)
  spatialMap := P.spatialMap
  map_direction := P.map_direction
  realCharacter_normalMap := P.realCharacter_normalMap

variable (P : Pushforward d d' h h' H H')

/-- Restricting the scalars of pushforward data keeps the degree map. -/
@[simp]
theorem Pushforward.restrictScalars_degreeMap :
    (P.restrictScalars K).degreeMap = P.degreeMap := (rfl)

/-- Restricting the scalars of pushforward data keeps the values of the Lie map. -/
@[simp]
theorem Pushforward.restrictScalars_lieHom_apply (x : L) :
    (P.restrictScalars K).lieHom x = P.lieHom x :=
  GradedLieHom.restrictScalars_apply P.lieHom x

/-- Restricting the scalars of pushforward data keeps the ray map. -/
@[simp]
theorem Pushforward.restrictScalars_rayMap : (P.restrictScalars K).rayMap = P.rayMap := (rfl)

/-- Restricting the scalars of pushforward data keeps the normal map. -/
@[simp]
theorem Pushforward.restrictScalars_normalMap :
    (P.restrictScalars K).normalMap = P.normalMap := (rfl)

/-- Restricting the scalars of pushforward data keeps the spatial map. -/
@[simp]
theorem Pushforward.restrictScalars_spatialMap :
    (P.restrictScalars K).spatialMap = P.spatialMap := (rfl)

end Data

section DataCompletion

variable [LieRing L'] [LieAlgebra R L'] [LieAlgebra K L'] [IsScalarTower K R L']
  [LieAlgebra ℚ L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ R L'] [DecidableEq Γ']
  {ℳ : Γ' → Submodule R L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {H' : DirectedWallSpaces ρ' ℳ} (P : Pushforward d d' h h' H H')
  (W : DirectedWall (d := d) h H)

omit [Algebra ℚ R] [IsScalarTower ℚ R L] [IsScalarTower ℚ R L'] in
/-- The completed Lie map of the restricted data is the completed map of the restricted Lie
map. -/
@[simp]
theorem Pushforward.restrictScalars_lieHom_completedMap :
    (P.restrictScalars K).lieHom.completedMap = (P.lieHom.restrictScalars K).completedMap :=
  -- The Lie map of the restricted data is `P.lieHom.restrictScalars K` by definition.
  (rfl)

/-- Restricting scalars commutes with pushforward along pushforward data over `R`. -/
@[simp]
theorem restrictScalars_pushforward :
    (W.pushforward P).restrictScalars K = (W.restrictScalars K).pushforward
      (P.restrictScalars K) := by
  apply DirectedWall.ext
  · rw [restrictScalars_normal, pushforward_normal, pushforward_normal,
      Pushforward.restrictScalars_normalMap, restrictScalars_normal]
  · rw [restrictScalars_ray, pushforward_ray, pushforward_ray,
      Pushforward.restrictScalars_rayMap, restrictScalars_ray]
  · rw [restrictScalars_support, pushforward_support, pushforward_support,
      Pushforward.restrictScalars_spatialMap, restrictScalars_support]
  · rw [restrictScalars_label, pushforward_label, pushforward_label,
      Pushforward.restrictScalars_lieHom_completedMap, restrictScalars_label,
      MulEquiv.symm_apply_eq]
    -- Scalar restriction of completed BCH groups is natural in graded Lie maps.
    simpa using (DFunLike.congr_fun (P.lieHom.completedMap_restrictScalars (R := K))
      ((d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label)).symm

end DataCompletion

variable [CommRing S] [Algebra ℚ S] [SMul K S]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra K L'] [LieAlgebra ℚ L']
  [IsScalarTower K S L'] [IsScalarTower ℚ K L'] [IsScalarTower ℚ S L'] [DecidableEq Γ']
  {ℳ : Γ' → Submodule S L'} [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {H' : DirectedWallSpaces ρ' ℳ}
  (P : Pushforward d d' h h' (H.restrictScalars K) (H'.restrictScalars K))
  (W : DirectedWall (d := d) h H)

/-- Push a directed wall for wall spaces over `R` forward to wall spaces over `S`, along
pushforward data `P` between the wall spaces restricted to the common scalar ring `K`: restrict
scalars, push forward along `P` and undo the restriction over `S`. The degree map of `P` may
change the degree lattice and carry a cutoff modulus. -/
def pushforwardRestrictScalars : DirectedWall (d := d') h' H' :=
  ((W.restrictScalars K).pushforward P).ofRestrictScalars

/-- The cross-ring pushforward is the pushforward of the restricted wall, read back over the
target coefficient ring. -/
theorem pushforwardRestrictScalars_def :
    W.pushforwardRestrictScalars P = ((W.restrictScalars K).pushforward P).ofRestrictScalars :=
  (rfl)

/-- The cross-ring pushforward has the image normal. -/
@[simp]
theorem pushforwardRestrictScalars_normal :
    (W.pushforwardRestrictScalars P).normal = P.normalMap W.normal := by
  rw [pushforwardRestrictScalars_def, ofRestrictScalars_normal, pushforward_normal,
    restrictScalars_normal]

/-- The cross-ring pushforward has the reindexed ray. -/
@[simp]
theorem pushforwardRestrictScalars_ray :
    (W.pushforwardRestrictScalars P).ray = P.rayMap W.ray := by
  rw [pushforwardRestrictScalars_def, ofRestrictScalars_ray, pushforward_ray,
    restrictScalars_ray]

/-- The cross-ring pushforward has the spatial image of the support. -/
@[simp]
theorem pushforwardRestrictScalars_support :
    (W.pushforwardRestrictScalars P).support = P.spatialMap '' W.support := by
  rw [pushforwardRestrictScalars_def, ofRestrictScalars_support, pushforward_support,
    restrictScalars_support]

/-- The label of the cross-ring pushforward is the completed image of the label through the two
scalar-restriction comparisons. -/
@[simp]
theorem pushforwardRestrictScalars_label :
    (W.pushforwardRestrictScalars P).label = d'.completedBCHRestrictScalarsEquiv (R := K) ℳ
      (P.lieHom.completedMap ((d.completedBCHRestrictScalarsEquiv (R := K) ℒ).symm W.label)) := by
  rw [pushforwardRestrictScalars_def, ofRestrictScalars_label, pushforward_label,
    restrictScalars_label]

/-- Restricting the scalars of the cross-ring pushforward gives the pushforward of the restricted
wall. -/
@[simp]
theorem restrictScalars_pushforwardRestrictScalars :
    (W.pushforwardRestrictScalars P).restrictScalars K = (W.restrictScalars K).pushforward P := by
  rw [pushforwardRestrictScalars_def, restrictScalars_ofRestrictScalars]

/-- The cross-ring pushforward preserves and reflects incomingness. -/
@[simp]
theorem incoming_pushforwardRestrictScalars_iff :
    (W.pushforwardRestrictScalars P).Incoming ↔ W.Incoming := by
  rw [← incoming_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars,
    incoming_pushforward_iff, incoming_restrictScalars_iff]

/-- The cross-ring pushforward preserves and reflects outgoingness. -/
@[simp]
theorem outgoing_pushforwardRestrictScalars_iff :
    (W.pushforwardRestrictScalars P).Outgoing ↔ W.Outgoing := by
  rw [← outgoing_restrictScalars_iff (K := K), restrictScalars_pushforwardRestrictScalars,
    outgoing_pushforward_iff, outgoing_restrictScalars_iff]

/-- Along fixed-degree coefficient data, the cross-ring pushforward is the coefficient change
`DirectedWall.mapRestrictScalars`. -/
@[simp]
theorem pushforwardRestrictScalars_ofFixedDegree {ℳ : Γ → Submodule S L'} [GradedLieAlgebra ℳ]
    [IsPositiveGrading d ℳ] {H' : DirectedWallSpaces ρ ℳ}
    (f : GradedLieHom (PositiveDegreeMap.id d) (fun n => (ℒ n).restrictScalars K)
      (fun n => (ℳ n).restrictScalars K))
    (hf : ∀ n m, ∀ x ∈ (H.restrictScalars K).wall n m, f x ∈ (H'.restrictScalars K).wall n m) :
    W.pushforwardRestrictScalars (Pushforward.ofFixedDegree f hf) = W.mapRestrictScalars f hf := by
  rw [pushforwardRestrictScalars_def, pushforward_ofFixedDegree, mapRestrictScalars_def]

omit [CommRing S] [Algebra ℚ S] [SMul K S] [LieAlgebra S L'] [IsScalarTower K S L']
  [IsScalarTower ℚ S L'] in
/-- Over a single coefficient ring, the cross-ring pushforward along the scalar restriction of
pushforward data is the pushforward. -/
@[simp]
theorem pushforwardRestrictScalars_restrictScalars [LieAlgebra R L'] [IsScalarTower K R L']
    [IsScalarTower ℚ R L'] {ℳ : Γ' → Submodule R L'} [GradedLieAlgebra ℳ]
    [IsPositiveGrading d' ℳ] {H' : DirectedWallSpaces ρ' ℳ}
    (P : Pushforward d d' h h' H H') :
    W.pushforwardRestrictScalars (P.restrictScalars K) = W.pushforward P := by
  rw [pushforwardRestrictScalars_def, ← restrictScalars_pushforward,
    ofRestrictScalars_restrictScalars]

/-- Successive cross-ring pushforwards over a common scalar ring `K` agree with the cross-ring
pushforward along the composite data. -/
@[simp]
theorem pushforwardRestrictScalars_pushforwardRestrictScalars [CommRing T] [Algebra ℚ T]
    [SMul K T] [LieRing L''] [LieAlgebra T L''] [LieAlgebra K L''] [LieAlgebra ℚ L'']
    [IsScalarTower K T L''] [IsScalarTower ℚ K L''] [IsScalarTower ℚ T L''] [DecidableEq Γ'']
    {ℋ : Γ'' → Submodule T L''} [GradedLieAlgebra ℋ] [IsPositiveGrading d'' ℋ]
    {H'' : DirectedWallSpaces ρ'' ℋ}
    (Q : Pushforward d' d'' h' h'' (H'.restrictScalars K) (H''.restrictScalars K)) :
    (W.pushforwardRestrictScalars P).pushforwardRestrictScalars Q =
      W.pushforwardRestrictScalars (Q.comp P) := by
  rw [pushforwardRestrictScalars_def, restrictScalars_pushforwardRestrictScalars,
    pushforward_pushforward, pushforwardRestrictScalars_def]

end Pushforward

end Mei.DirectedWall
