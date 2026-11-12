/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.RestrictScalars
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Equivalence
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# Restriction of scalars for directed diagrams

Let `D` be a directed diagram for wall spaces `H` of a positively graded Lie algebra over a
commutative `ℚ`-algebra `R`, and let `K` be a smaller scalar ring. Restricting the scalars of
every wall gives a diagram `D.restrictScalars K` for `H.restrictScalars K`, with the same
supports, normals and supported rays (`DirectedDiagram.restrictScalars`); the inverse is
`DirectedDiagram.ofRestrictScalars`. At every order both diagrams have the same active walls
(`DirectedDiagram.active_restrictScalars`), and the finite path products correspond under the
finite scalar-restriction comparison of BCH groups
(`DirectedDiagram.levelPathProduct_restrictScalars`). Hence restriction of scalars preserves and
reflects consistency (`DirectedDiagram.consistent_restrictScalars_iff`), equivalence
(`DirectedDiagram.equivalent_restrictScalars_iff`) and outgoing completions
(`DirectedDiagram.isOutgoingCompletion_restrictScalars_iff`).

This permits coefficient changes between different coefficient rings over a common base
ring `K`. For a `K`-linear fixed-degree graded Lie homomorphism `f` of the restricted
gradings, from algebras over `R` to algebras over `S`, that preserves the restricted wall
spaces, `D.mapRestrictScalars f hf` restricts scalars, applies the fixed-degree coefficient map
`DirectedDiagram.map` and undoes the restriction over `S`. It preserves consistency
(`DirectedDiagram.Consistent.mapRestrictScalars`), equivalence
(`DirectedDiagram.Equivalent.mapRestrictScalars`) and outgoing completions
(`DirectedDiagram.IsOutgoingCompletion.mapRestrictScalars`), and it carries every
representative of the scattering class of a full-hyperplane input to a representative of the
scattering class of the image input (`DirectedDiagram.toClass_mapRestrictScalars_eq_scat`). This
is the change of coefficient ring of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, Example 2.1(i) (arXiv:1503.06183v5), with fixed supports and normals.
-/

public section

open TauCeti (WallComplement AdmissiblePLPath GradedLieHom)

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

universe u v

variable {Γ Λ K R V ι : Type*} {L : Type u} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing K] [CommRing R] [Algebra ℚ K] [Algebra ℚ R] [SMul K R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra K L] [LieAlgebra ℚ L]
  [IsScalarTower K R L] [IsScalarTower ℚ K L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {H : DirectedWallSpaces ρ ℒ}

section Restrict

variable (K) in
/-- Restrict the scalars of every wall of a directed diagram, retaining its index. -/
def restrictScalars (D : DirectedDiagram (d := d) h H ι) :
    DirectedDiagram (d := d) h (H.restrictScalars K) ι where
  wall j := (D.wall j).restrictScalars K
  finite_active k := by
    refine (D.finite_active k).subset fun j hj => ?_
    simpa only [Function.mem_mulSupport, ne_eq,
      DirectedWall.projection_restrictScalars_label_eq_one_iff] using hj

/-- Undo the restriction of scalars of every wall of a directed diagram for the restricted wall
spaces. -/
def ofRestrictScalars (D : DirectedDiagram (d := d) h (H.restrictScalars K) ι) :
    DirectedDiagram (d := d) h H ι where
  wall j := (D.wall j).ofRestrictScalars
  finite_active k := by
    refine (D.finite_active k).subset fun j hj => ?_
    simp only [Function.mem_mulSupport, ne_eq, DirectedWall.ofRestrictScalars_label] at hj ⊢
    rwa [PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_eq_one_iff] at hj

variable (D : DirectedDiagram (d := d) h H ι)
  (D' : DirectedDiagram (d := d) h (H.restrictScalars K) ι)

/-- Restricting the scalars of a diagram restricts the scalars of each wall. -/
@[simp]
theorem restrictScalars_wall (j : ι) :
    (D.restrictScalars K).wall j = (D.wall j).restrictScalars K := (rfl)

/-- Undoing a restriction of scalars of a diagram undoes it on each wall. -/
@[simp]
theorem ofRestrictScalars_wall (j : ι) :
    D'.ofRestrictScalars.wall j = (D'.wall j).ofRestrictScalars := (rfl)

/-- Undoing a restriction of scalars recovers the diagram. -/
@[simp]
theorem ofRestrictScalars_restrictScalars : (D.restrictScalars K).ofRestrictScalars = D := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Restricting the scalars of a diagram obtained from the restricted wall spaces recovers it. -/
@[simp]
theorem restrictScalars_ofRestrictScalars : D'.ofRestrictScalars.restrictScalars K = D' := by
  apply DirectedDiagram.ext
  funext j
  simp

/-- Restriction of scalars keeps the active walls at every order. -/
@[simp]
theorem active_restrictScalars (k : ℕ) : (D.restrictScalars K).active k = D.active k := by
  ext j
  rw [mem_active, mem_active, restrictScalars_wall, ne_eq,
    DirectedWall.projection_restrictScalars_label_eq_one_iff]

variable (K) in
/-- Paths avoiding the active walls of `D` avoid the active walls of its restriction, with the
same vertices. -/
def levelPathRestrictScalars (k : ℕ) :
    WallComplement (fun j : D.active k => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.restrictScalars K).active k =>
        ((D.restrictScalars K).wall j).support) :=
  (ContinuousAffineEquiv.refl ℝ V).wallComplementMap
    (Set.equivOfEq (D.active_restrictScalars k).symm) fun j => by
      rw [ContinuousAffineEquiv.coe_refl, Set.image_id, Set.equivOfEq_apply, restrictScalars_wall,
        DirectedWall.restrictScalars_support]

variable (K) in
/-- Paths avoiding the active walls of the restriction of `D` avoid the active walls of `D`, with
the same vertices. -/
def levelPathOfRestrictScalars (k : ℕ) :
    WallComplement (fun j : (D.restrictScalars K).active k =>
        ((D.restrictScalars K).wall j).support) ⥤q
      WallComplement (fun j : D.active k => (D.wall j).support) :=
  (ContinuousAffineEquiv.refl ℝ V).wallComplementMap
    (Set.equivOfEq (D.active_restrictScalars k)) fun j => by
      rw [ContinuousAffineEquiv.coe_refl, Set.image_id, Set.equivOfEq_apply, restrictScalars_wall,
        DirectedWall.restrictScalars_support]

/-- Transported paths keep their vertices. -/
@[simp]
theorem levelPathRestrictScalars_obj_val (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ((D.levelPathRestrictScalars K k).obj x).val = x.val :=
  ContinuousAffineEquiv.wallComplementMap_obj_val _ _ _ x

/-- Transported paths keep their vertices. -/
@[simp]
theorem levelPathOfRestrictScalars_obj_val (k : ℕ)
    (x : WallComplement (fun j : (D.restrictScalars K).active k =>
      ((D.restrictScalars K).wall j).support)) :
    ((D.levelPathOfRestrictScalars K k).obj x).val = x.val :=
  ContinuousAffineEquiv.wallComplementMap_obj_val _ _ _ x

/-- A transported path has the vertex list of the original path. -/
theorem vertices_levelPathRestrictScalars (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((D.levelPathRestrictScalars K k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    levelPathRestrictScalars_obj_val]

/-- A transported path has the vertex list of the original path. -/
theorem vertices_levelPathOfRestrictScalars (k : ℕ)
    {x y : WallComplement (fun j : (D.restrictScalars K).active k =>
      ((D.restrictScalars K).wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((D.levelPathOfRestrictScalars K k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    levelPathOfRestrictScalars_obj_val]

/-- The finite scalar-restriction comparison sends the projected label of a restricted wall to
the projected label of the original wall. -/
theorem bchGroupEquiv_projection_restrictScalars_wall_label (k : ℕ) (j : ι) :
    (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv
        (TauCeti.CompletedGroup.projection k ((D.restrictScalars K).wall j).label) =
      TauCeti.CompletedGroup.projection k (D.wall j).label := by
  rw [restrictScalars_wall, DirectedWall.restrictScalars_label]
  exact PositiveDegrees.bchGroupEquiv_projection_completedBCHRestrictScalarsEquiv_symm _ _ k _

/-- The finite path product of the restriction along a transported path is the image of the
original product under the inverse finite scalar-restriction comparison. -/
theorem levelPathProduct_restrictScalars (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.restrictScalars K).levelPathProduct k ((D.levelPathRestrictScalars K k).mapPath p) =
      (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv.symm
        (D.levelPathProduct k p) := by
  rw [levelPathProduct_eq_wallPathProduct _ k _ ((D.restrictScalars K).activeLabels_commute k),
    D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact p.wallPathProduct_wallComplementMap (ContinuousAffineEquiv.refl ℝ V)
    (Set.equivOfEq (D.active_restrictScalars k).symm) _ _ _ (fun j => by ext v; simp) _ _ _ _
    (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv.symm.toMonoidHom fun j =>
      (MulEquiv.eq_symm_apply _).mpr (D.bchGroupEquiv_projection_restrictScalars_wall_label k j)

/-- A finite path product of the restriction is computed by the corresponding path of `D`. -/
theorem levelPathProduct_restrictScalars_eq (k : ℕ)
    {x y : WallComplement (fun j : (D.restrictScalars K).active k =>
      ((D.restrictScalars K).wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.restrictScalars K).levelPathProduct k p =
      (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv.symm
        (D.levelPathProduct k ((D.levelPathOfRestrictScalars K k).mapPath p)) := by
  rw [← levelPathProduct_restrictScalars]
  apply levelPathProduct_eq_of_vertices_eq
  rw [vertices_levelPathRestrictScalars, vertices_levelPathOfRestrictScalars]

variable {D}

/-- Restriction of scalars preserves and reflects consistency at every order. -/
theorem levelConsistent_restrictScalars_iff {k : ℕ} :
    (D.restrictScalars K).LevelConsistent k ↔ D.LevelConsistent k := by
  rw [levelConsistent_def, levelConsistent_def]
  refine ⟨fun hD x y p q => ?_, fun hD x y p q => ?_⟩
  · apply (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv.symm.injective
    rw [← levelPathProduct_restrictScalars, ← levelPathProduct_restrictScalars]
    exact hD _ _
  · rw [levelPathProduct_restrictScalars_eq, levelPathProduct_restrictScalars_eq, hD]

/-- Restriction of scalars preserves and reflects consistency. -/
theorem consistent_restrictScalars_iff : (D.restrictScalars K).Consistent ↔ D.Consistent := by
  rw [consistent_iff, consistent_iff]
  exact forall_congr' fun _ => levelConsistent_restrictScalars_iff

/-- Restriction of scalars preserves and reflects finite-order equivalence. -/
theorem levelEquivalent_restrictScalars_iff {κ : Type*} {E : DirectedDiagram (d := d) h H κ}
    {k : ℕ} :
    (D.restrictScalars K).LevelEquivalent (E.restrictScalars K) k ↔ D.LevelEquivalent E k := by
  rw [levelEquivalent_def, levelEquivalent_def]
  refine ⟨fun hDE x y x' y' p q hpq => ?_, fun hDE x y x' y' p q hpq => ?_⟩
  · apply (d.lieTruncationRestrictScalarsEquiv (R := K) ℒ k).bchGroupEquiv.symm.injective
    rw [← levelPathProduct_restrictScalars, ← levelPathProduct_restrictScalars]
    apply hDE
    rw [vertices_levelPathRestrictScalars, vertices_levelPathRestrictScalars, hpq]
  · rw [levelPathProduct_restrictScalars_eq, levelPathProduct_restrictScalars_eq]
    congr 1
    apply hDE
    rw [vertices_levelPathOfRestrictScalars, vertices_levelPathOfRestrictScalars, hpq]

/-- Restriction of scalars preserves and reflects equivalence. -/
theorem equivalent_restrictScalars_iff {κ : Type*} {E : DirectedDiagram (d := d) h H κ} :
    (D.restrictScalars K).Equivalent (E.restrictScalars K) ↔ D.Equivalent E := by
  rw [equivalent_iff, equivalent_iff]
  exact forall_congr' fun _ => levelEquivalent_restrictScalars_iff

/-- Restriction of scalars preserves and reflects outgoing completions of an input. -/
theorem isOutgoingCompletion_restrictScalars_iff {ι₀ ι' : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')} :
    IsOutgoingCompletion (fun j => (D₀ j).restrictScalars K) (E.restrictScalars K) ↔
      IsOutgoingCompletion D₀ E := by
  refine ⟨fun hE => ⟨fun j => ?_, fun j => ?_, ?_⟩, fun hE => ⟨fun j => ?_, fun j => ?_, ?_⟩⟩
  · simpa using congrArg DirectedWall.ofRestrictScalars (hE.wall_inl j)
  · simpa using hE.outgoing_inr j
  · exact consistent_restrictScalars_iff.mp hE.consistent
  · rw [restrictScalars_wall, hE.wall_inl j]
  · simpa using hE.outgoing_inr j
  · exact consistent_restrictScalars_iff.mpr hE.consistent

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
  (D : DirectedDiagram (d := d) h H ι)

/-- Change the coefficient ring of every wall along a `K`-linear fixed-degree graded Lie
homomorphism `f` of the restricted gradings preserving the restricted wall spaces, retaining
every index, support, normal and supported ray. -/
def mapRestrictScalars : DirectedDiagram (d := d) h H' ι :=
  ((D.restrictScalars K).map f hf).ofRestrictScalars

/-- The coefficient change is the fixed-degree map of the restricted diagram, read back over the
target coefficient ring. -/
theorem mapRestrictScalars_def :
    D.mapRestrictScalars f hf = ((D.restrictScalars K).map f hf).ofRestrictScalars := (rfl)

/-- Changing the coefficient ring of a diagram changes it on each wall. -/
@[simp]
theorem mapRestrictScalars_wall (j : ι) :
    (D.mapRestrictScalars f hf).wall j = (D.wall j).mapRestrictScalars f hf := by
  rw [mapRestrictScalars_def, ofRestrictScalars_wall, map_wall, restrictScalars_wall,
    DirectedWall.mapRestrictScalars_def]

/-- Restricting the scalars of the coefficient change gives the fixed-degree map of the
restricted diagram. -/
@[simp]
theorem restrictScalars_mapRestrictScalars :
    (D.mapRestrictScalars f hf).restrictScalars K = (D.restrictScalars K).map f hf := by
  rw [mapRestrictScalars_def, restrictScalars_ofRestrictScalars]

variable {D}

/-- Changing the coefficient ring preserves consistency. -/
theorem Consistent.mapRestrictScalars (hD : D.Consistent) :
    (D.mapRestrictScalars f hf).Consistent := by
  rw [← consistent_restrictScalars_iff (K := K), restrictScalars_mapRestrictScalars]
  exact Consistent.map _ f hf (consistent_restrictScalars_iff.mpr hD)

/-- Changing the coefficient ring sends an outgoing completion to an outgoing completion of the
image input, even when some labels vanish. -/
theorem IsOutgoingCompletion.mapRestrictScalars {ι₀ ι' : Type*}
    {D₀ : ι₀ → DirectedWall (d := d) h H} {E : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hE : IsOutgoingCompletion D₀ E) :
    IsOutgoingCompletion (fun j => (D₀ j).mapRestrictScalars f hf) (E.mapRestrictScalars f hf) := by
  rw [← isOutgoingCompletion_restrictScalars_iff (K := K), restrictScalars_mapRestrictScalars]
  simp_rw [DirectedWall.restrictScalars_mapRestrictScalars]
  exact (isOutgoingCompletion_restrictScalars_iff.mpr hE).map f hf

/-- Changing the coefficient ring preserves equivalence. -/
theorem Equivalent.mapRestrictScalars {κ : Type*} {E : DirectedDiagram (d := d) h H κ}
    (hDE : D.Equivalent E) :
    (D.mapRestrictScalars f hf).Equivalent (E.mapRestrictScalars f hf) := by
  rw [← equivalent_restrictScalars_iff (K := K), restrictScalars_mapRestrictScalars,
    restrictScalars_mapRestrictScalars]
  exact (equivalent_restrictScalars_iff.mpr hDE).map f hf

variable [Module.Free ℤ Γ]

/-- Changing the coefficient ring carries every representative of the scattering class of a
full-hyperplane input to a representative of the scattering class of the image input. -/
theorem toClass_mapRestrictScalars_eq_scat {ι : Type v} (D : DirectedDiagram (d := d) h H ι)
    (hfull : ∀ j, ∃ a : ℝ,
      (D.wall j).support = {x | h.realCharacter (D.wall j).normal x = a})
    {κ : Type v} {E : DirectedDiagram (d := d) h H κ} (hE : E.toClass = D.Scat hfull) :
    (E.mapRestrictScalars f hf).toClass = (D.mapRestrictScalars f hf).Scat (by
      simpa only [mapRestrictScalars_wall, DirectedWall.mapRestrictScalars_support,
        DirectedWall.mapRestrictScalars_normal] using hfull) := by
  obtain ⟨η, F, hF, hc⟩ := D.scat_spec hfull
  have hF' : IsOutgoingCompletion (D.mapRestrictScalars f hf).wall (F.mapRestrictScalars f hf) := by
    simpa only [← mapRestrictScalars_wall] using hF.mapRestrictScalars f hf
  rw [scat_eq_toClass _ _ hF', toClass_eq_iff]
  exact ((toClass_eq_iff E F).mp (hE.trans hc)).mapRestrictScalars f hf

end Map

end Mei.DirectedDiagram
