/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Cylinder
public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall
public import Mei.Geometry.Convex.Polyhedron.Path.Preimage

/-!
# KS walls of a skew lattice datum as principal cylinders

Let `D` be a skew lattice datum with character lattice `M° = Hom(N°, ℤ)`, positive degrees
`d` on `N_uf` and the positive skew Lie algebra graded by `N_uf`. A KS space `U` of `N_uf`
models `Hom(N_uf, ℝ)`. A `KSRestriction` is a surjective real-linear map `A : M°_ℝ → U`
restricting characters: for `m ∈ M°` and `n ∈ N_uf ∩ N°`, the character `A(m)` takes the
value `m(n)` at `n`. It is rational for the two lattices, and it pulls the KS normal of `n`
back to `κ(n)⁻¹` times the normalized projected principal normal `κ(n)⟨n,-⟩`. The point
`A(p₁*(n))` is the character `{n,-}` of `N_uf`.

An indexed KS wall `𝔡 ⊆ n⊥` on the supported ray of a primitive `n` becomes a projected
principal wall: its support is `A⁻¹(𝔡)`, its normal is `κ(n)⟨n,-⟩`, its degree ray is the
principal ray through `r(n) = (p₁*(n), n)`, and its label is the image of the KS label under
the completed graph comparison from `P_N` to `P_pr` along `r`, of identity modulus. Its
principal cylinder is `A⁻¹(𝔡) × (N_uf)_ℝ` with normal `κ(n)ν_n`. Both walls are incoming
exactly when the KS wall contains `A(p₁*(n))`, that is, when the KS wall is KS-incoming.

An indexed KS presentation becomes a projected principal diagram with the same active walls
at every cutoff. Its finite-order path products are the images, under the finite graph
comparison, of the KS path products along the image paths in `U`; on the principal cylinder
the same holds after the `M°_ℝ`-projection. Every KS path lifts, so the projected diagram is
consistent at a cutoff exactly when all KS path products between common endpoints agree
there, and the projected diagram and its principal cylinder are consistent exactly when this
holds at every cutoff.

The principal realization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1 and Appendix B, arXiv:1411.1394v2, and the abelian-ray KS walls follow
§1.1 there. We use `IndexedWallPresentation.levelPathProduct`,
`SkewLatticeDatum.projectedPrincipalGraphWallSpaces`, `PositiveDegrees.graphBCHGroupEquiv`,
`DirectedWall.cylinder` and `WallComplement.preimageProjection`.
-/

public section

open TauCeti.CompletedGroup (projection HasFiniteSupport)

open TauCeti (WallComplement AdmissiblePLPath)

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

open Set Mei.Convex

namespace Mei.SkewLatticeDatum

variable {N V U : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U]
  (D : SkewLatticeDatum N)

variable {i : Module.Dual ℤ D.sublattice →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (D.unfrozen →+ ℤ) →+ U} {hj : TauCeti.Toric.IsIntegralLattice j} (s : KSSpace hj)

/-- A comparison from the real character space `M°_ℝ` of `N°` to a KS space of `N_uf`
restricting characters: the image of `m ∈ M°` takes the value `m(n)` at every
`n ∈ N_uf ∩ N°`. Like restriction `Hom(N, ℝ) → Hom(N_uf, ℝ)`, it is surjective. The
integral lattice `h` of `M°_ℝ` is part of the data compared. -/
structure KSRestriction (h : TauCeti.Toric.IsIntegralLattice i) (s : KSSpace hj) where
  /-- The underlying real-linear map. -/
  toLinearMap : V →ₗ[ℝ] U
  /-- Every KS point is the restriction of a point of `M°_ℝ`. -/
  surjective : Function.Surjective toLinearMap
  /-- On `N_uf ∩ N°`, restriction is evaluation of the integral character. -/
  evaluation_apply (m : Module.Dual ℤ D.sublattice) (n : D.unfrozen)
    (hn : (n : N) ∈ D.sublattice) : s.evaluation (toLinearMap (i m)) n = m ⟨n, hn⟩

namespace KSRestriction

variable {D h s} (A : D.KSRestriction h s)

/-- The real projected principal normal `κ(n)⟨n,-⟩` is `κ(n)` times the pullback of the KS
normal of `n`. This includes `n = 0` and radical degrees. -/
theorem realCharacter_projectedPrincipalNormal (n : D.unfrozen) :
    h.realCharacter (D.projectedPrincipalNormal n).toAddMonoidHom =
      (D.sublattice.toAddSubgroup.rayIndex (n : N) : ℝ) • (s.normal n).comp A.toLinearMap := by
  symm
  apply h.eq_realCharacter
  intro m
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, KSSpace.normal_apply, smul_eq_mul,
    LinearMap.toAddMonoidHom_coe, projectedPrincipalNormal_apply]
  rw [← D.map_rayVector_unfrozen (s.evaluation (A.toLinearMap (i m))) n,
    A.evaluation_apply m _ (D.rayVector_mem_unfrozen_inf_sublattice n.property).2]
  -- Both sides evaluate `m` at the same element of `N°`, up to subtype eta.
  rfl

omit [Module.Free ℤ N] in
/-- The restriction is rational for the integral lattices `M°` and `Hom(N_uf, ℤ)`. -/
theorem isRationalLinearMap : TauCeti.Toric.IsRationalLinearMap h hj A.toLinearMap := by
  set c := D.sublattice.toAddSubgroup.index
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast AddSubgroup.FiniteIndex.index_ne_zero
  let g : D.unfrozen →+ D.sublattice :=
    { toFun n := ⟨c • (n : N), D.sublattice.toAddSubgroup.nsmul_index_mem _⟩
      map_zero' := by ext; simp
      map_add' a b := by ext; simp }
  let u : Module.Dual ℤ D.sublattice →+ (D.unfrozen →+ ℤ) :=
    { toFun m := m.toAddMonoidHom.comp g
      map_zero' := by ext; simp
      map_add' a b := by ext; simp }
  have hu : ∀ m, ((c : ℝ) • A.toLinearMap) (i m) = j (u m) := by
    intro m
    apply s.evaluation.injective
    ext n
    have he := A.evaluation_apply m (c • n) (D.sublattice.toAddSubgroup.nsmul_index_mem _)
    simp only [map_nsmul, nsmul_eq_mul] at he
    simp only [LinearMap.smul_apply, map_smul, AddMonoidHom.smul_apply, smul_eq_mul,
      KSSpace.evaluation_lattice]
    rw [he]
    -- The right side unfolds to `m` evaluated at `c • n`, as in `he`.
    rfl
  rw [TauCeti.Toric.isRationalLinearMap_iff]
  intro f hf
  have hr := (TauCeti.Toric.IsRationalLinearMap.of_integral_compatible h hj u _ hu).map_functional
    hf
  have he : f.comp A.toLinearMap =
      (((c : ℚ)⁻¹ : ℚ) : ℝ) • f.comp ((c : ℝ) • A.toLinearMap) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      Rat.cast_inv, Rat.cast_natCast]
    field_simp
  rw [he]
  exact hr.rat_smul _

omit [Module.Free ℤ N] in
/-- The restriction of `p₁*(n) = {n,-}|N°` is the character `{n,-}` of `N_uf`. -/
theorem evaluation_principalCharacter (n n' : D.unfrozen) :
    s.evaluation (A.toLinearMap (i (D.principalCharacter n))) n' = (D.form n n' : ℝ) := by
  set c := D.sublattice.toAddSubgroup.index
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast AddSubgroup.FiniteIndex.index_ne_zero
  have he := A.evaluation_apply (D.principalCharacter n) (c • n')
    (D.sublattice.toAddSubgroup.nsmul_index_mem _)
  have hq := D.cast_principalCharacter_apply n
    ⟨c • (n' : N), D.sublattice.toAddSubgroup.nsmul_index_mem _⟩
  simp only [map_nsmul, nsmul_eq_mul] at he hq
  apply mul_left_cancel₀ hc
  rw [he]
  exact_mod_cast hq

/-- The underlying map is continuous, since `M°_ℝ` is finite-dimensional. -/
def toContinuousLinearMap : V →L[ℝ] U :=
  let := h.finiteDimensional
  LinearMap.toContinuousLinearMap A.toLinearMap

omit [Module.Free ℤ N] in
/-- The continuous map has the original values. -/
@[simp]
theorem coe_toContinuousLinearMap : ⇑A.toContinuousLinearMap = A.toLinearMap := (rfl)

/-- The preimage of a set through `0` whose supporting direction is the KS hyperplane `n⊥`
has supporting direction the kernel of the projected principal normal `κ(n)⟨n,-⟩`. -/
theorem direction_affineSpan_preimage {S : Set U} (hS : (0 : U) ∈ S) {n : D.unfrozen}
    (hdir : (affineSpan ℝ S).direction = LinearMap.ker (s.normal n)) (hn : n ≠ 0) :
    (affineSpan ℝ (A.toLinearMap ⁻¹' S)).direction =
      LinearMap.ker (h.realCharacter (D.projectedPrincipalNormal n).toAddMonoidHom) := by
  have hκ : (D.sublattice.toAddSubgroup.rayIndex (n : N) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (D.rayIndex_unfrozen_pos hn).ne'
  rw [A.toLinearMap.direction_affineSpan_preimage A.surjective ⟨0, hS⟩, hdir,
    A.realCharacter_projectedPrincipalNormal, LinearMap.ker_smul _ _ hκ, LinearMap.ker_comp]

section Wall

variable {R : Type*} [CommRing R] [Algebra ℚ R] {d : PositiveDegrees D.unfrozen}
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d
local notation "𝓟" => D.projectedPrincipalGraphWallSpaces (R := R) d
local notation "p₁" => D.principalCharacter.toAddMonoidHom

/-- The projected principal wall of an indexed KS wall `𝔡 ⊆ n⊥`, with `n` the primitive
generator of its supported ray: support `A⁻¹(𝔡)`, normal `κ(n)⟨n,-⟩`, degree ray through
`r(n)`, and the KS label transported by the completed graph comparison along `r`. -/
def projectedWall (W : IndexedWall s d ℒ) :
    DirectedWall (d := D.principalPositiveDegrees d) h (𝓟) where
  normal := (D.projectedPrincipalNormal W.ray.generator).toAddMonoidHom
  normal_ne_zero hz := W.ray.generator_ne_zero
    ((D.projectedPrincipalNormal_eq_zero_iff _).mp (LinearMap.toAddMonoidHom_injective hz))
  ray := W.ray.graph p₁
  normal_direction := by simp [SupportedRay.graph_generator]
  support := A.toLinearMap ⁻¹' W.support
  support_nonempty := ⟨0, by simp⟩
  rational_support :=
    -- The continuous affine map has `A` as its linear part.
    W.rational_support.preimage A.toContinuousLinearMap.toContinuousAffineMap
      A.isRationalLinearMap
  direction_support := A.direction_affineSpan_preimage W.zero_mem_support
    W.direction_support W.ray.generator_ne_zero
  label := d.graphBCHGroupEquiv ℒ p₁ W.label
  label_mem := by
    rw [← D.map_completedRaySubgroup_eq_projectedPrincipalGraphWallGroup d W.ray]
    exact ⟨W.label, W.label_mem, rfl⟩

variable (W : IndexedWall s d
  (SkewLieAlgebra.positiveGrading (D.coefficientForm R) (D.isAlt_coefficientForm R) d))

@[simp]
theorem projectedWall_normal :
    (A.projectedWall W).normal = (D.projectedPrincipalNormal W.ray.generator).toAddMonoidHom :=
  (rfl)

@[simp]
theorem projectedWall_ray : (A.projectedWall W).ray = W.ray.graph p₁ := (rfl)

@[simp]
theorem projectedWall_support : (A.projectedWall W).support = A.toLinearMap ⁻¹' W.support :=
  (rfl)

@[simp]
theorem projectedWall_label :
    (A.projectedWall W).label = d.graphBCHGroupEquiv ℒ p₁ W.label := (rfl)

/-- The real normal of the projected wall is `κ(n)` times the pullback of the KS normal
of `n`. -/
theorem realCharacter_projectedWall_normal :
    h.realCharacter (A.projectedWall W).normal =
      (D.sublattice.toAddSubgroup.rayIndex (W.ray.generator : N) : ℝ) •
        (s.normal W.ray.generator).comp A.toLinearMap :=
  A.realCharacter_projectedPrincipalNormal _

/-- The degree of the projected wall is the principal exponent `r(n)` of the KS generator. -/
theorem projectedWall_ray_generator :
    (A.projectedWall W).ray.generator = D.principalEmbedding W.ray.generator := by
  simp [SupportedRay.graph_generator]

/-- The projected wall moves with spatial velocity `-p₁*(n)`. -/
theorem projectedWall_direction :
    (A.projectedWall W).direction = -i (D.principalCharacter W.ray.generator) :=
  projectedPrincipal_direction_eq _ (A.projectedWall_ray_generator W)

/-- The projected wall is incoming exactly when the KS wall contains the restriction of
`p₁*(n)`, the character `{n,-}` of `N_uf`: KS-incoming agrees with incoming. -/
theorem projectedWall_incoming_iff :
    (A.projectedWall W).Incoming ↔
      A.toLinearMap (i (D.principalCharacter W.ray.generator)) ∈ W.support := by
  obtain ⟨σ, hσ⟩ := W.isCone
  rw [DirectedWall.incoming_iff, ← mem_recessionCone, projectedWall_support, ← hσ,
    ← PointedCone.coe_comap,
    PointedCone.recessionCone_coe, SetLike.mem_coe, PointedCone.mem_comap]
  simp [SupportedRay.graph_generator]

/-- The projected wall is outgoing exactly when the KS wall misses the restriction of
`p₁*(n)`. -/
theorem projectedWall_outgoing_iff :
    (A.projectedWall W).Outgoing ↔
      A.toLinearMap (i (D.principalCharacter W.ray.generator)) ∉ W.support := by
  rw [DirectedWall.outgoing_iff, mem_recessionCone, ← DirectedWall.incoming_iff,
    projectedWall_incoming_iff]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : D.unfrozen →+ E}
  (hk : TauCeti.Toric.IsIntegralLattice k)

/-- The principal cylinder of a KS wall has the primitive principal normal `κ(n)ν_n`. -/
theorem cylinder_projectedWall_normal :
    ((A.projectedWall W).cylinder hk).normal =
      (D.principalNormal W.ray.generator).toAddMonoidHom := by
  rw [DirectedWall.cylinder_normal, projectedWall_normal, projectedPrincipalNormal_comp_fst]

/-- The principal cylinder of a KS wall `𝔡` is `A⁻¹(𝔡) × (N_uf)_ℝ`. -/
theorem cylinder_projectedWall_support :
    ((A.projectedWall W).cylinder hk).support =
      (A.toLinearMap ⁻¹' W.support) ×ˢ (univ : Set E) := by
  simp

/-- The principal cylinder of a KS wall is incoming exactly when the KS wall is
KS-incoming. -/
theorem cylinder_projectedWall_incoming_iff :
    ((A.projectedWall W).cylinder hk).Incoming ↔
      A.toLinearMap (i (D.principalCharacter W.ray.generator)) ∈ W.support := by
  rw [DirectedWall.cylinder_incoming_iff, projectedWall_incoming_iff]

end Wall

section Diagram

variable {R : Type*} [CommRing R] [Algebra ℚ R] {d : PositiveDegrees D.unfrozen}
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)] {ι : Type*}

local notation "ℒ" => SkewLieAlgebra.positiveGrading
  (D.coefficientForm R) (D.isAlt_coefficientForm R) d
local notation "𝓟" => D.projectedPrincipalGraphWallSpaces (R := R) d
local notation "p₁" => D.principalCharacter.toAddMonoidHom

/-- The projected principal diagram of an indexed KS presentation, wall by wall. -/
def projectedDiagram (P : IndexedWallPresentation s d ℒ ι) :
    DirectedDiagram (d := D.principalPositiveDegrees d) h (𝓟) ι where
  wall a := A.projectedWall (P.wall a)
  finite_active := by
    -- The labels of the projected walls are the graph images of the KS labels by definition.
    change HasFiniteSupport fun a => d.graphBCHGroupEquiv ℒ p₁ (P.wall a).label
    simpa only [← PositiveDegrees.graphBCHGroupEquiv_apply] using
      (graphGradedLieHom ℒ p₁ d).hasFiniteSupport_completedMap P.finite_active

variable (P : IndexedWallPresentation s d
  (SkewLieAlgebra.positiveGrading (D.coefficientForm R) (D.isAlt_coefficientForm R) d) ι)

@[simp]
theorem projectedDiagram_wall (a : ι) :
    (A.projectedDiagram P).wall a = A.projectedWall (P.wall a) := (rfl)

/-- The graph comparison is injective at every cutoff, so the projected diagram has exactly
the active walls of the KS presentation. -/
@[simp]
theorem projectedDiagram_active (k : ℕ) : (A.projectedDiagram P).active k = P.active k := by
  ext a
  rw [DirectedDiagram.mem_active, IndexedWallPresentation.mem_active, projectedDiagram_wall,
    projectedWall_label, PositiveDegrees.projection_graphBCHGroupEquiv]
  -- The finite graph comparison is injective; its source is the categorical tower group.
  exact not_congr (MulEquiv.map_eq_one_iff _)

/-- The finite path quiver map from the active projected walls to the active KS walls,
applying the restriction to spatial points. -/
def levelProjection (k : ℕ) :
    WallComplement (fun a : (A.projectedDiagram P).active k =>
      ((A.projectedDiagram P).wall a).support) ⥤q
      WallComplement (fun a : P.active k => (P.wall a).support) :=
  let := h.finiteDimensional
  WallComplement.preimageProjection (V := V) A.toLinearMap A.surjective _
    -- Projected supports are preimages by definition, and reindexing retains each index.
    (Set.equivOfEq (A.projectedDiagram_active P k)) (fun _ => rfl)

/-- The level projection applies the restriction to the actual spatial point. -/
@[simp]
theorem levelProjection_obj_val (k : ℕ)
    (x : WallComplement (fun a : (A.projectedDiagram P).active k =>
      ((A.projectedDiagram P).wall a).support)) :
    ((A.levelProjection P k).obj x).val = A.toLinearMap x.val :=
  let := h.finiteDimensional
  WallComplement.preimageProjection_obj_val _ _ _ _ _ x

/-- The finite path quiver map lifting KS paths along a linear section of the restriction. -/
def levelLift (k : ℕ) :
    WallComplement (fun a : P.active k => (P.wall a).support) ⥤q
      WallComplement (fun a : (A.projectedDiagram P).active k =>
        ((A.projectedDiagram P).wall a).support) :=
  let := h.finiteDimensional
  WallComplement.preimageLift (V := V) A.toLinearMap A.surjective _
    -- Projected supports are preimages by definition, and reindexing retains each index.
    (Set.equivOfEq (A.projectedDiagram_active P k)) (fun _ => rfl)

/-- The level lift of a point is a preimage of it under the restriction. -/
@[simp]
theorem apply_levelLift_obj_val (k : ℕ)
    (x : WallComplement (fun a : P.active k => (P.wall a).support)) :
    A.toLinearMap ((A.levelLift P k).obj x).val = x.val :=
  let := h.finiteDimensional
  WallComplement.apply_preimageLift_obj_val _ _ _ _ _ x

/-- Projection is a retraction of the lift. -/
@[simp]
theorem levelLift_comp_levelProjection (k : ℕ) :
    A.levelLift P k ⋙q A.levelProjection P k = Prefunctor.id _ := by
  let := h.finiteDimensional
  exact WallComplement.preimageLift_comp_preimageProjection A.toLinearMap A.surjective _ _ _

/-- On projected walls with a common affine span, the finite KS labels commute. -/
theorem commute_projection_label (k : ℕ) (a b : (A.projectedDiagram P).active k)
    (hab : affineSpan ℝ ((A.projectedDiagram P).wall a).support =
      affineSpan ℝ ((A.projectedDiagram P).wall b).support) :
    Commute (projection k (P.wall a).label)
      (projection k (P.wall b).label) := by
  refine Commute.of_map (d.graphTruncatedGroupEquiv ℒ p₁ k).injective ?_
  have hF := (A.projectedDiagram P).activeLabels_commute k a b hab
  rwa [projectedDiagram_wall, projectedDiagram_wall, projectedWall_label, projectedWall_label,
    PositiveDegrees.projection_graphBCHGroupEquiv,
    PositiveDegrees.projection_graphBCHGroupEquiv] at hF

/-- The finite-order path products of the projected diagram are the wall products for the
pulled-back KS normals and the finite graph images of the KS labels. -/
theorem levelPathProduct_projectedDiagram_eq_wallPathProduct (k : ℕ)
    {x y : WallComplement (fun a : (A.projectedDiagram P).active k =>
      ((A.projectedDiagram P).wall a).support)} (p : AdmissiblePLPath x y) :
    (A.projectedDiagram P).levelPathProduct k p =
      p.wallPathProduct (fun a : (A.projectedDiagram P).active k =>
          (s.normal (P.wall a).ray.generator).comp A.toLinearMap)
        (fun a => d.graphTruncatedGroupEquiv ℒ p₁ k (projection k (P.wall a).label))
        (fun a b hab => (A.commute_projection_label P k a b hab).map _) := by
  let := h.finiteDimensional
  have hν : (fun a : (A.projectedDiagram P).active k =>
      h.realCharacter ((A.projectedDiagram P).wall a).normal) =
        fun a : (A.projectedDiagram P).active k =>
          (D.sublattice.toAddSubgroup.rayIndex ((P.wall a).ray.generator : N) : ℝ) •
            (s.normal (P.wall a).ray.generator).comp A.toLinearMap :=
    funext fun a => A.realCharacter_projectedWall_normal (P.wall a)
  rw [(A.projectedDiagram P).levelPathProduct_eq_wallPathProduct k p
    ((A.projectedDiagram P).activeLabels_commute k)]
  -- Both products run over the same signed events, since `κ` rescales positively.
  refine (Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents _ _ _ p).trans
    (Eq.trans ?_ (Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents _ _ _ p).symm)
  rw [hν, Quiver.Path.signedCrossingEvents_smul _ _ fun a : (A.projectedDiagram P).active k =>
    Rat.cast_pos.mpr (D.rayIndex_unfrozen_pos (P.wall a).ray.generator_ne_zero)]
  simp only [projectedDiagram_wall, projectedWall_label,
    PositiveDegrees.projection_graphBCHGroupEquiv]
  -- The two sides differ only in the group instance of the categorical tower.
  rfl

variable [Module.Free ℤ D.unfrozen]

/-- The finite-order path products of the projected diagram are the images, under the finite
graph comparison, of the KS path products along the restricted paths. Simultaneous and
repeated crossings are retained. -/
theorem levelPathProduct_projectedDiagram (k : ℕ)
    {x y : WallComplement (fun a : (A.projectedDiagram P).active k =>
      ((A.projectedDiagram P).wall a).support)} (p : AdmissiblePLPath x y) :
    (A.projectedDiagram P).levelPathProduct k p =
      d.graphTruncatedGroupEquiv ℒ p₁ k
        (P.levelPathProduct k ((A.levelProjection P k).mapPath p)) := by
  let := h.finiteDimensional
  rw [levelPathProduct_projectedDiagram_eq_wallPathProduct,
    P.levelPathProduct_eq_wallPathProduct k _ (P.activeLabels_commute k)]
  -- The level projection is the preimage projection for the active reindexing.
  refine Eq.trans ?_ (congrArg _ (Quiver.Path.wallPathProduct_preimageProjection A.toLinearMap
    A.surjective (Set.equivOfEq (A.projectedDiagram_active P k)) (fun _ => rfl)
    (fun a : P.active k => s.normal (P.wall a).ray.generator)
    (fun a : P.active k => projection k (P.wall a).label)
    (P.activeLabels_commute k) (A.commute_projection_label P k) p).symm)
  exact (Quiver.Path.map_wallPathProduct _ _ _ (d.graphTruncatedGroupEquiv ℒ p₁ k).toMonoidHom
    p).symm

/-- A lifted KS path has the graph image of the KS path product. -/
theorem levelPathProduct_levelLift (k : ℕ)
    {x y : WallComplement (fun a : P.active k => (P.wall a).support)}
    (p : AdmissiblePLPath x y) :
    (A.projectedDiagram P).levelPathProduct k ((A.levelLift P k).mapPath p) =
      d.graphTruncatedGroupEquiv ℒ p₁ k (P.levelPathProduct k p) := by
  rw [levelPathProduct_projectedDiagram]
  have he := congrArg
    (fun F : WallComplement (fun a : P.active k => (P.wall a).support) ⥤q
        WallComplement (fun a : P.active k => (P.wall a).support) =>
      P.levelPathProduct k (F.mapPath p)) (A.levelLift_comp_levelProjection P k)
  simp only [Prefunctor.mapPath_comp_apply, Prefunctor.mapPath_id] at he
  -- The endpoints of the composite prefunctor are its successive object maps.
  exact congrArg _ he

/-- The projected diagram is consistent at a cutoff exactly when all KS path products
between common endpoints agree at that cutoff. -/
theorem projectedDiagram_levelConsistent_iff (k : ℕ) :
    (A.projectedDiagram P).LevelConsistent k ↔
      ∀ ⦃x y : WallComplement (fun a : P.active k => (P.wall a).support)⦄
        (p q : AdmissiblePLPath x y), P.levelPathProduct k p = P.levelPathProduct k q := by
  rw [DirectedDiagram.levelConsistent_def]
  constructor
  · intro hc x y p q
    have he := hc ((A.levelLift P k).mapPath p) ((A.levelLift P k).mapPath q)
    rw [levelPathProduct_levelLift, levelPathProduct_levelLift] at he
    exact (d.graphTruncatedGroupEquiv ℒ p₁ k).injective he
  · intro hP x y p q
    rw [levelPathProduct_projectedDiagram, levelPathProduct_projectedDiagram, hP]

/-- The projected diagram is consistent exactly when, at every cutoff, all KS path products
between common endpoints agree. -/
theorem projectedDiagram_consistent_iff :
    (A.projectedDiagram P).Consistent ↔
      ∀ (k : ℕ) ⦃x y : WallComplement (fun a : P.active k => (P.wall a).support)⦄
        (p q : AdmissiblePLPath x y), P.levelPathProduct k p = P.levelPathProduct k q := by
  simp only [DirectedDiagram.consistent_iff, projectedDiagram_levelConsistent_iff]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {e : D.unfrozen →+ E}
  (he : TauCeti.Toric.IsIntegralLattice e)

/-- On the principal cylinder `M°_ℝ × (N_uf)_ℝ`, finite-order path products are the graph
images of the KS path products along the restriction of the `M°_ℝ`-projection. -/
theorem levelPathProduct_cylinder_projectedDiagram (k : ℕ)
    {x y : WallComplement (fun a : ((A.projectedDiagram P).cylinder he).active k =>
      (((A.projectedDiagram P).cylinder he).wall a).support)} (p : AdmissiblePLPath x y) :
    ((A.projectedDiagram P).cylinder he).levelPathProduct k p =
      d.graphTruncatedGroupEquiv ℒ p₁ k (P.levelPathProduct k
        ((((A.projectedDiagram P).levelCylinderProjection he k) ⋙q
          A.levelProjection P k).mapPath p)) := by
  rw [DirectedDiagram.levelPathProduct_cylinder, levelPathProduct_projectedDiagram,
    Prefunctor.mapPath_comp_apply]
  -- The endpoints of the composite prefunctor are its successive object maps.
  rfl

/-- The principal cylinder of the projected diagram is consistent exactly when, at every
cutoff, all KS path products between common endpoints agree. -/
theorem cylinder_projectedDiagram_consistent_iff :
    ((A.projectedDiagram P).cylinder he).Consistent ↔
      ∀ (k : ℕ) ⦃x y : WallComplement (fun a : P.active k => (P.wall a).support)⦄
        (p q : AdmissiblePLPath x y), P.levelPathProduct k p = P.levelPathProduct k q := by
  rw [DirectedDiagram.cylinder_consistent_iff, projectedDiagram_consistent_iff]

end Diagram

end KSRestriction

end Mei.SkewLatticeDatum
