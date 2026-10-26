/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Group
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom
public import Mei.GroupTheory.CompletedGroup.OrderedProduct

/-!
# Completed BCH groups and graded homomorphisms

The nilpotent degree truncations of a positively graded Lie algebra give a
surjective tower of BCH groups. Its inverse limit is the completed BCH group.
A graded Lie homomorphism induces a homomorphism of these completions, using
its positive degree map's cutoff modulus. Projections compute this map at finite
order. Identity, composition, filtration estimates and convergent ordered products
are preserved, and the result depends only on the underlying Lie homomorphism,
not on the choice of cutoff modulus.
The canonical exponential of an original Lie element is computed in each finite
quotient and is natural for these completed maps.

The finite maps use `LieHom.bchGroupMap` and `GradedLieHom.truncatedMap`.
The inverse-limit construction, cutoff comparison and ordered-product law use
`Mei.CompletedGroup.map`, `Mei.CompletedGroup.map_eq` and
`Mei.CompletedGroup.map_orderedProd`, on the compatible-family carrier obtained
from Mathlib's `GrpCat.sectionsSubgroup`.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe u

namespace Mei

namespace PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- The BCH group of the order-`k` nilpotent Lie quotient. -/
abbrev truncatedGroup (k : ℕ) := BCHGroup (d.truncatedLie ℒ k)

/-- The tower of BCH groups of finite degree truncations. -/
-- Objects must compute so that projections have their concrete BCH quotient types.
@[expose]
def groupTower : ℕᵒᵖ ⥤ GrpCat where
  obj k := GrpCat.of (d.truncatedGroup ℒ k.unop)
  map f := GrpCat.ofHom (d.truncationMap ℒ (leOfHom f.unop)).bchGroupMap
  map_id k := by
    apply GrpCat.hom_ext
    simp
  map_comp f g := by
    apply GrpCat.hom_ext
    simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom, ← LieHom.bchGroupMap_comp] using
      congrArg (fun h => h.bchGroupMap)
        (d.truncationMap_comp ℒ (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Tower transitions are induced by the Lie quotient transitions. -/
@[simp]
theorem groupTower_map_hom {k l : ℕᵒᵖ} (f : k ⟶ l) :
    ((d.groupTower ℒ).map f).hom =
      (d.truncationMap ℒ (leOfHom f.unop)).bchGroupMap := (rfl)

/-- Every transition in the BCH tower is surjective. -/
theorem groupTower_map_surjective {k l : ℕᵒᵖ} (f : k ⟶ l) :
    Function.Surjective ((d.groupTower ℒ).map f) :=
  LieHom.bchGroupMap_surjective (d.truncationMap_surjective ℒ (leOfHom f.unop))

/-- The group of compatible BCH elements in all finite degree truncations. -/
abbrev completedBCHGroup := completedGroup (d.groupTower ℒ)

/-- The exponential of a Lie element in the degree-completed BCH group. The Lie
algebra itself need not be nilpotent: exponentiation takes place in each quotient. -/
def expToCompletion (x : L) : d.completedBCHGroup ℒ :=
  ⟨fun k => BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ x),
    (mem_completedGroup_iff _ _).mpr (by
      intro k l h
      -- The categorical tower arrow conceals the concrete BCH quotient groups.
      change (d.truncationMap ℒ h).bchGroupMap
        (BCHGroup.exp ((d.degreeIdeal ℒ l).mkQ x)) =
          BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ x)
      rw [LieHom.bchGroupMap_exp]
      congr 1
      exact d.truncationMap_mk ℒ h x)⟩

/-- The completed exponential projects to the exponential of the quotient class. -/
@[simp]
theorem projection_expToCompletion (k : ℕ) (x : L) :
    CompletedGroup.projection k (d.expToCompletion ℒ x) =
      BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ x) := by
  rw [CompletedGroup.projection_apply]
  rfl

@[simp]
theorem expToCompletion_zero : d.expToCompletion ℒ 0 = 1 := by
  apply CompletedGroup.ext
  intro k
  rw [map_one, projection_expToCompletion, map_zero, BCHGroup.exp_zero]
  rfl

@[simp]
theorem expToCompletion_neg (x : L) :
    d.expToCompletion ℒ (-x) = (d.expToCompletion ℒ x)⁻¹ := by
  apply CompletedGroup.ext
  intro k
  rw [map_inv, projection_expToCompletion, projection_expToCompletion,
    map_neg, BCHGroup.exp_neg]
  rfl

/-- Lie elements with zero bracket have commuting completed exponentials. -/
theorem commute_expToCompletion_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    Commute (d.expToCompletion ℒ x) (d.expToCompletion ℒ y) := by
  apply CompletedGroup.ext
  intro k
  rw [map_mul, map_mul, projection_expToCompletion, projection_expToCompletion]
  apply BCHGroup.commute_exp_of_lie_eq_zero
  rw [← LieHom.map_lie, h, map_zero]

end PositiveDegrees

namespace GradedLieHom

variable {N M P R : Type*} {L L' L'' : Type u}
  [AddCommMonoid N] [AddCommMonoid M] [AddCommMonoid P]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq N] [DecidableEq M] [DecidableEq P]
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]
  {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}

/-- A graded Lie homomorphism gives a map of group towers reindexed by its modulus. -/
def groupTowerMap (f : GradedLieHom T ℒ ℳ) :
    (⟨T.modulus, T.monotone_modulus⟩ : ℕ →o ℕ).toFunctor.op ⋙ d.groupTower ℒ ⟶ e.groupTower ℳ where
  app k := GrpCat.ofHom (f.truncatedMap k.unop le_rfl).bchGroupMap
  naturality {k l} h := by
    apply GrpCat.hom_ext
    -- Expose the concrete quotient groups hidden by the functor object wrappers.
    change (f.truncatedMap l.unop le_rfl).bchGroupMap.comp
        (d.truncationMap ℒ (T.monotone_modulus (leOfHom h.unop))).bchGroupMap =
      (e.truncationMap ℳ (leOfHom h.unop)).bchGroupMap.comp
        (f.truncatedMap k.unop le_rfl).bchGroupMap
    simp only [← LieHom.bchGroupMap_comp]
    exact congrArg (fun h => h.bchGroupMap)
      (f.truncationMap_comp_truncatedMap (leOfHom h.unop)).symm

/-- The order-`k` tower map is the BCH map of the corresponding Lie truncation map. -/
@[simp]
theorem groupTowerMap_app_hom (f : GradedLieHom T ℒ ℳ) (k : ℕᵒᵖ) :
    (f.groupTowerMap.app k).hom = (f.truncatedMap k.unop le_rfl).bchGroupMap := (rfl)

/-- The completed group homomorphism induced by a graded Lie homomorphism. -/
def completedMap (f : GradedLieHom T ℒ ℳ) :
    d.completedBCHGroup ℒ →* e.completedBCHGroup ℳ :=
  CompletedGroup.map ⟨T.modulus, T.monotone_modulus⟩ f.groupTowerMap

/-- Projection computes the completed map using exactly the prescribed source cutoff. -/
@[simp]
theorem projection_completedMap (f : GradedLieHom T ℒ ℳ) (k : ℕ)
    (x : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (f.completedMap x) =
      (f.truncatedMap k le_rfl).bchGroupMap
        (CompletedGroup.projection (T.modulus k) x) := by
  rw [completedMap, CompletedGroup.projection_map]
  rfl

/-- A larger source cutoff also computes the projection of a completed map. -/
theorem projection_completedMap_of_le (f : GradedLieHom T ℒ ℳ) (k : ℕ)
    {a : ℕ} (ha : T.modulus k ≤ a) (x : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (f.completedMap x) =
      (f.truncatedMap k ha).bchGroupMap (CompletedGroup.projection a x) := by
  rw [projection_completedMap]
  have hp : (d.truncationMap ℒ ha).bchGroupMap (CompletedGroup.projection a x) =
      CompletedGroup.projection (T.modulus k) x :=
    CompletedGroup.map_projection (T.modulus k) a ha x
  let y : d.truncatedGroup ℒ a := CompletedGroup.projection a x
  have hf := DFunLike.congr_fun (congrArg LieHom.bchGroupMap
    (f.truncatedMap_comp_truncationMap (k := k) le_rfl ha)) y
  simp only [LieHom.bchGroupMap_comp, MonoidHom.comp_apply] at hf
  exact (congrArg (f.truncatedMap k le_rfl).bchGroupMap hp.symm).trans hf

/-- A graded completed map carries the exponential of an original Lie element
to the exponential of its image. -/
@[simp]
theorem completedMap_expToCompletion (f : GradedLieHom T ℒ ℳ) (x : L) :
    f.completedMap (d.expToCompletion ℒ x) = e.expToCompletion ℳ (f x) := by
  apply CompletedGroup.ext
  intro k
  rw [projection_completedMap, PositiveDegrees.projection_expToCompletion,
    PositiveDegrees.projection_expToCompletion, LieHom.bchGroupMap_exp]
  congr 1
  exact f.truncatedMap_mk k le_rfl x

/-- The finite projection formula uniquely characterizes the completed homomorphism. -/
theorem completedMap_unique (f : GradedLieHom T ℒ ℳ)
    (g : d.completedBCHGroup ℒ →* e.completedBCHGroup ℳ)
    (hg : ∀ k, (CompletedGroup.projection k).comp g =
      (f.truncatedMap k le_rfl).bchGroupMap.comp
        (CompletedGroup.projection (T.modulus k))) : g = f.completedMap :=
  CompletedGroup.map_unique ⟨T.modulus, T.monotone_modulus⟩ f.groupTowerMap g hg

/-- The completed map of the identity graded homomorphism is the identity. -/
@[simp]
theorem completedMap_id :
    (id (d := d) ℒ).completedMap = MonoidHom.id (d.completedBCHGroup ℒ) := by
  rw [completedMap]
  apply CompletedGroup.map_eq_id
  intro k
  refine ⟨max ((PositiveDegreeMap.id d).modulus k) k,
    le_max_left _ _, le_max_right _ _, ?_⟩
  apply GrpCat.hom_ext
  -- The categorical arrows conceal the concrete quotient groups.
  change ((id (d := d) ℒ).truncatedMap k le_rfl).bchGroupMap.comp
      (d.truncationMap ℒ (le_max_left _ _)).bchGroupMap =
    (d.truncationMap ℒ (le_max_right _ _)).bchGroupMap
  rw [← LieHom.bchGroupMap_comp, truncatedMap_comp_truncationMap]
  congr 1
  apply (d.degreeIdeal ℒ _).lieHom_qext
  intro a
  simp [LieIdeal.mkQ_apply]

/-- Completed maps respect composition, with successive source moduli composed. -/
@[simp]
theorem completedMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ) :
    (g.comp f).completedMap = g.completedMap.comp f.completedMap := by
  rw [completedMap, completedMap, completedMap, ← CompletedGroup.map_comp]
  apply CompletedGroup.map_eq
  intro k
  refine ⟨max ((U.comp T).modulus k) (T.modulus (U.modulus k)),
    le_max_left _ _, le_max_right _ _, ?_⟩
  apply GrpCat.hom_ext
  -- Re-elaborate the functor and whiskering wrappers at their concrete quotient types.
  change ((g.comp f).truncatedMap k le_rfl).bchGroupMap.comp
      (d.truncationMap ℒ (le_max_left _ _)).bchGroupMap =
    (g.truncatedMap k le_rfl).bchGroupMap.comp
      ((f.truncatedMap (U.modulus k) le_rfl).bchGroupMap.comp
        (d.truncationMap ℒ (le_max_right _ _)).bchGroupMap)
  simp only [← LieHom.bchGroupMap_comp, truncatedMap_comp_truncationMap,
    ← truncatedMap_comp]

/-- The original cutoff modulus also bounds the filtration shift on completed groups. -/
theorem completedMap_mem_degreeFiltration (f : GradedLieHom T ℒ ℳ) (k : ℕ)
    {x : d.completedBCHGroup ℒ}
    (hx : x ∈ CompletedGroup.degreeFiltration (d.groupTower ℒ) (T.modulus k + 1)) :
    f.completedMap x ∈ CompletedGroup.degreeFiltration (e.groupTower ℳ) (k + 1) :=
  CompletedGroup.map_mem_degreeFiltration ⟨T.modulus, T.monotone_modulus⟩ f.groupTowerMap k hx

/-- Graded homomorphisms with the same underlying Lie map induce the same completed
homomorphism, even when their degree maps or cutoff moduli differ. -/
theorem completedMap_eq_of_toLieHom_eq {T' : PositiveDegreeMap d e}
    (f : GradedLieHom T ℒ ℳ) (g : GradedLieHom T' ℒ ℳ)
    (hfg : f.toLieHom = g.toLieHom) : f.completedMap = g.completedMap := by
  rw [completedMap, completedMap]
  apply CompletedGroup.map_eq
  intro k
  refine ⟨max (T.modulus k) (T'.modulus k), le_max_left _ _, le_max_right _ _, ?_⟩
  apply GrpCat.hom_ext
  -- Re-elaborate the categorical arrows as homomorphisms of concrete BCH quotients.
  change (f.truncatedMap k le_rfl).bchGroupMap.comp
      (d.truncationMap ℒ (le_max_left _ _)).bchGroupMap =
    (g.truncatedMap k le_rfl).bchGroupMap.comp
      (d.truncationMap ℒ (le_max_right _ _)).bchGroupMap
  simp only [← LieHom.bchGroupMap_comp, truncatedMap_comp_truncationMap]
  congr 1
  apply (d.degreeIdeal ℒ (max (T.modulus k) (T'.modulus k))).lieHom_qext
  intro a
  simpa only [LieIdeal.mkQ_apply, truncatedMap_mk, coe_toLieHom] using
    congrArg (fun h : L →ₗ⁅R⁆ L' => (e.degreeIdeal ℳ k).mkQ (h a)) hfg

variable {ι : Type*}

/-- A graded completed map preserves finite support at every order. -/
theorem hasFiniteSupport_completedMap (f : GradedLieHom T ℒ ℳ)
    {x : ι → d.completedBCHGroup ℒ} (hx : CompletedGroup.HasFiniteSupport x) :
    CompletedGroup.HasFiniteSupport (fun i => f.completedMap (x i)) := by
  simpa only [completedMap] using
    hx.map ⟨T.modulus, T.monotone_modulus⟩ f.groupTowerMap

/-- Graded maps preserve convergent ordered products, with the smallest index leftmost. -/
@[simp]
theorem completedMap_orderedProd [LinearOrder ι] (f : GradedLieHom T ℒ ℳ)
    (x : ι → d.completedBCHGroup ℒ) (hx : CompletedGroup.HasFiniteSupport x) :
    f.completedMap (CompletedGroup.orderedProd x hx) =
      CompletedGroup.orderedProd (fun i => f.completedMap (x i))
        (f.hasFiniteSupport_completedMap hx) :=
  CompletedGroup.map_orderedProd ⟨T.modulus, T.monotone_modulus⟩ f.groupTowerMap x hx

end GradedLieHom
end Mei
