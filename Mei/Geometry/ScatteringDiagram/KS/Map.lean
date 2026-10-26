/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction
public import Mei.Algebra.Lie.BCH.Sign.Hom

/-!
# Change of coefficients in KS diagrams

A degree-preserving Lie homomorphism maps finite and completed KS diagrams by
applying its BCH maps to the wall labels. Orthogonal support is preserved, as
are geometric path products and consistency. Identity, composition and cutoff
change commute with this construction. At every finite cutoff, reconstruction
by middle sign factors commutes with these maps as an equality of KS complexes.

The geometry is retained, even when a label becomes the identity; injectivity
of the Lie map is not required. These constructions use
`FiniteWallDiagram.relabel`, `GradedLieHom.completedMap`,
`Mei.map_mem_orthogonalLieSubalgebra`, and the uniqueness of sign factorization.
-/

public section

noncomputable section

universe u

namespace Mei

open Set Mei.Convex

variable {N V R : Type*} {L L' L'' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]

namespace KSComplex

variable {C : FinitePolyhedralComplex h} {k l : ℕ}

/-- Map the Lie coefficients of a finite KS complex, retaining its actual geometry. -/
def mapDiagram (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : KSComplex s d ℳ C k where
  isConical := D.isConical
  degree := D.degree
  degree_mem := D.degree_mem
  degree_ne_zero := D.degree_ne_zero
  evaluation_eq_zero := D.evaluation_eq_zero
  label P := (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.label P)
  label_mem P := by
    rw [LieSubalgebra.mem_bchSubgroup, LieHom.log_bchGroupMap]
    exact map_mem_orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
      (d.truncatedGrading ℳ k) (f.truncatedMap (a := k) k (by simp))
      (fun _ _ hx => by
        simpa only [PositiveDegreeMap.id_apply] using
          f.truncatedMap_mem (a := k) k (by simp) hx) _
      ((LieSubalgebra.mem_bchSubgroup _ _).mp (D.label_mem P))

/-- Coefficient maps retain the coorienting degrees. -/
@[simp]
theorem mapDiagram_degree (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.mapDiagram f).degree = D.degree := (rfl)

/-- Coefficient change applies the induced finite BCH map to each wall label. -/
@[simp]
theorem mapDiagram_label (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (P : C.walls) :
    (D.mapDiagram f).label P =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.label P) := (rfl)

/-- Forgetting the grading identifies coefficient change with relabelling. -/
@[simp]
theorem toFiniteWallDiagram_mapDiagram (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) :
    (D.mapDiagram f).toFiniteWallDiagram =
      D.toFiniteWallDiagram.relabel (f.truncatedMap (a := k) k (by simp)).bchGroupMap := by
  ext <;> simp

/-- The identity Lie map leaves the finite diagram unchanged. -/
@[simp]
theorem mapDiagram_id (D : KSComplex s d ℒ C k) :
    D.mapDiagram (GradedLieHom.id ℒ) = D := by
  ext <;> simp

/-- Successive coefficient changes compose as equalities of finite complexes. -/
@[simp]
theorem mapDiagram_comp (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.mapDiagram f).mapDiagram g =
      D.mapDiagram (by simpa only [PositiveDegreeMap.id_comp] using g.comp f) := by
  ext P
  · rfl
  · simp only [mapDiagram_label, ← MonoidHom.comp_apply, ← LieHom.bchGroupMap_comp]
    congr 1
    apply congrArg LieHom.bchGroupMap
    apply (d.degreeIdeal ℒ k).lieHom_qext
    intro x
    simp [LieIdeal.mkQ_apply, GradedLieHom.comp_apply]

/-- Lowering the cutoff commutes with changing the Lie coefficients. -/
@[simp]
theorem mapDiagram_truncate (D : KSComplex s d ℒ C l)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (hkl : k ≤ l) :
    (D.truncate hkl).mapDiagram f = (D.mapDiagram f).truncate hkl := by
  ext P
  · simp
  · simp only [mapDiagram_label, truncate_label, ← MonoidHom.comp_apply,
      ← LieHom.bchGroupMap_comp]
    exact DFunLike.congr_fun
      (congrArg LieHom.bchGroupMap
        (f.truncationMap_comp_truncatedMap_of_le hkl hkl (by simp) (by simp)).symm) _

/-- Coefficient change applies the finite BCH map to the geometric path product. -/
theorem pathProduct_mapDiagram (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    {x y : WallComplement (fun P : C.walls => (P : Set V))}
    (p : AdmissiblePLPath x y) :
    (D.mapDiagram f).toFiniteWallDiagram.pathProduct p =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.toFiniteWallDiagram.pathProduct p) := by
  rw [toFiniteWallDiagram_mapDiagram, FiniteWallDiagram.pathProduct_relabel]

/-- Coefficient maps preserve consistency without an injectivity hypothesis. -/
theorem consistent_mapDiagram (D : KSComplex s d ℒ C k)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (hD : D.toFiniteWallDiagram.Consistent) :
    (D.mapDiagram f).toFiniteWallDiagram.Consistent := by
  rw [toFiniteWallDiagram_mapDiagram]
  exact hD.relabel _

end KSComplex

namespace CompletedDiagram

variable {C : ℕ → FinitePolyhedralComplex h}

/-- Change the Lie coefficients at every order of a completed KS diagram. -/
def mapDiagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : CompletedDiagram s d ℳ C where
  diagram k := (D.diagram k).mapDiagram f
  compatible k {_ _ _ _} p q hpq := by
    simp only [KSComplex.pathProduct_mapDiagram]
    have hc := D.compatible k p q hpq
    have hn := DFunLike.congr_fun
      (congrArg LieHom.bchGroupMap
        (f.truncationMap_comp_truncatedMap_of_le (Nat.le_succ k)
          (Nat.le_succ k) (by simp) (by simp)))
      ((D.diagram (k + 1)).toFiniteWallDiagram.pathProduct q)
    simpa only [LieHom.bchGroupMap_comp, MonoidHom.comp_apply, hc] using hn

/-- The finite levels of coefficient change are the existing finite diagram maps. -/
@[simp]
theorem mapDiagram_diagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (k : ℕ) :
    (D.mapDiagram f).diagram k = (D.diagram k).mapDiagram f := (rfl)

/-- The identity coefficient map leaves a completed diagram unchanged. -/
@[simp]
theorem mapDiagram_id (D : CompletedDiagram s d ℒ C) :
    D.mapDiagram (GradedLieHom.id ℒ) = D := by
  apply CompletedDiagram.ext
  funext k
  simp

/-- Successive maps of completed diagrams compose as equalities. -/
@[simp]
theorem mapDiagram_comp (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.mapDiagram f).mapDiagram g =
      D.mapDiagram (by simpa only [PositiveDegreeMap.id_comp] using g.comp f) := by
  apply CompletedDiagram.ext
  funext k
  simp

/-- The complete product is natural for the completed Lie coefficient map. -/
theorem pathProduct_mapDiagram (D : CompletedDiagram s d ℒ C)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    {x y : Point C} (p : Quiver.Path x y) :
    (D.mapDiagram f).pathProduct p = f.completedMap (D.pathProduct p) := by
  apply CompletedGroup.ext
  intro k
  rw [f.projection_completedMap_of_le k (a := k) (by simp)]
  simp only [projection_pathProduct, mapDiagram_diagram, KSComplex.pathProduct_mapDiagram]
  -- The tower projections use the concrete BCH group operations.
  rfl

/-- A map of Lie coefficients preserves consistency at all orders. -/
theorem Consistent.mapDiagram {D : CompletedDiagram s d ℒ C} (hD : D.Consistent)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) : (D.mapDiagram f).Consistent := by
  apply (consistent_iff _).mpr
  intro k
  exact (D.diagram k).consistent_mapDiagram f ((consistent_iff _).mp hD k)

/-- Endpoint transport commutes with the completed coefficient map. -/
theorem transport_mapDiagram (D : CompletedDiagram s d ℒ C) (hD : D.Consistent)
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (x y : Point C) :
    (D.mapDiagram f).transport (hD.mapDiagram f) x y =
      f.completedMap (D.transport hD x y) := by
  obtain ⟨p⟩ := exists_path x y
  rw [transport_eq_pathProduct _ (hD.mapDiagram f) p,
    D.transport_eq_pathProduct hD p, pathProduct_mapDiagram]

end CompletedDiagram

namespace PositiveDegrees

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {j : N →+ W} (d : PositiveDegrees N) (hj : TauCeti.Toric.IsIntegralLattice j)

/-- Reconstruction by finite middle factors commutes with coefficient change,
including coefficient maps which kill nonidentity labels. -/
@[simp]
theorem mapDiagram_reconstructFinite (ℒ : N → Submodule R L) (ℳ : N → Submodule R L')
    [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
    [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ) (k : ℕ)
    (g : d.truncatedGroup ℒ k) :
    (d.reconstructFinite hj ℒ g).mapDiagram f =
      d.reconstructFinite hj ℳ ((f.truncatedMap (a := k) k (by simp)).bchGroupMap g) := by
  let := hj.continuousDual.finiteDimensional
  apply KSComplex.ext
  · rw [KSComplex.mapDiagram_degree]
    exact d.reconstructFinite_degree_eq hj ℒ g _
  · funext P
    obtain ⟨θ, hθ⟩ := (intrinsicInterior_nonempty
      ((d.arrangementComplex hj k).isConvexPolyhedron
        ((d.arrangementComplex hj k).mem_cells_of_mem_walls P.property)).convex).mpr
      ((d.arrangementComplex hj k).nonempty P
        ((d.arrangementComplex hj k).mem_cells_of_mem_walls P.property))
    rw [KSComplex.mapDiagram_label, d.reconstructFinite_label hj ℒ g P hθ,
      d.reconstructFinite_label hj ℳ _ P hθ,
      GradedLieHom.truncatedMap_signFactorizationEquiv_symm]

end PositiveDegrees
end Mei
