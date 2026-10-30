/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Correspondence
public import Mei.Algebra.MonoidAlgebra.Grading
public import Mei.LinearAlgebra.GradedCorrespondence.Hom
public import Mei.LinearAlgebra.GradedCorrespondence.RestrictScalars
public import TauCeti.RingTheory.Node.BaseChange

/-!
# Coefficient change for slab correspondences

Coefficient change commutes with the two Laurent chamber maps of a nodal algebra
and with its incoming homogeneous lifts. These maps give a morphism of the
normal-weight slab correspondences, after restricting the target scalars.
The target nodal algebra is equipped with a source scalar action compatible with
its coefficient-algebra action.
Quotient coefficient algebras are allowed, so the same morphism applies to
truncations even when a smoothing parameter or an incoming coefficient vanishes.

More generally, `Mei.NodeAlgebra.mapOfEq` is the coefficient map
`R[x,y]/(xy-a) → S[x,y]/(xy-a')` whenever `a` maps to `a'`.

We use `TauCeti.NodeAlgebra.map`, `AddMonoidAlgebra.mapAlgHom`, and the chosen
lifts of `Mei.NodeAlgebra.normalWeightCorrespondence`. The slab interpretation
follows Gross–Hacking–Siebert, *Theta functions on varieties with effective
anti-canonical class*, Definitions 3.1–3.3, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra LaurentPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (a : R)

section MapOfEq

variable {a' : S} [Algebra R (NodeAlgebra S a')] [IsScalarTower R S (NodeAlgebra S a')]
  (h : algebraMap R S a = a')

/-- The coefficient map `R[x,y]/(xy-a) → S[x,y]/(xy-a')`, `x ↦ x`, `y ↦ y`, when `a` maps
to `a'`. -/
def mapOfEq : NodeAlgebra R a →ₐ[R] NodeAlgebra S a' :=
  lift a (coord a' 0) (coord a' 1) (by
    rw [coord_zero_mul_coord_one, IsScalarTower.algebraMap_apply R S, h])

/-- `mapOfEq` fixes both coordinates. -/
@[simp]
theorem mapOfEq_coord (i : Fin 2) : mapOfEq a h (coord a i) = coord a' i := by
  fin_cases i <;> simp [mapOfEq]

end MapOfEq

variable [Algebra R (NodeAlgebra S (algebraMap R S a))]
  [IsScalarTower R S (NodeAlgebra S (algebraMap R S a))]

/-- The existing nodal coefficient map, retaining linearity over the source ring. -/
def mapAlgHom : NodeAlgebra R a →ₐ[R] NodeAlgebra S (algebraMap R S a) where
  __ := TauCeti.NodeAlgebra.map (S := S) a
  commutes' r := (TauCeti.NodeAlgebra.map_algebraMap (S := S) a r).trans
    (IsScalarTower.algebraMap_apply R S _ r).symm

/-- The algebra map has the values of the canonical coefficient ring map. -/
@[simp]
theorem mapAlgHom_apply (x : NodeAlgebra R a) :
    mapAlgHom (S := S) a x = TauCeti.NodeAlgebra.map (S := S) a x := (rfl)

/-- For `a' = algebraMap R S a`, `mapOfEq` is the coefficient map `TauCeti.NodeAlgebra.map`. -/
theorem mapOfEq_rfl : mapOfEq a (rfl : algebraMap R S a = _) = mapAlgHom a := by
  ext <;> simp

omit [Algebra R (NodeAlgebra S (algebraMap R S a))]
  [IsScalarTower R S (NodeAlgebra S (algebraMap R S a))] in
/-- Coefficient change commutes with the left chamber map. -/
@[simp]
theorem leftLaurentMap_map (x : NodeAlgebra R a) :
    leftLaurentMap (algebraMap R S a) (TauCeti.NodeAlgebra.map (S := S) a x) =
      AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S) (leftLaurentMap a x) := by
  let : Algebra R (NodeAlgebra S (algebraMap R S a)) := Algebra.compHom _ (algebraMap R S)
  let : IsScalarTower R S (NodeAlgebra S (algebraMap R S a)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h : ((leftLaurentMap (algebraMap R S a)).restrictScalars R).comp (mapAlgHom a) =
      (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).comp (leftLaurentMap a) := by
    apply TauCeti.NodeAlgebra.hom_ext <;> simp [C, T, -single_eq_C_mul_T]
  exact DFunLike.congr_fun h x

omit [Algebra R (NodeAlgebra S (algebraMap R S a))]
  [IsScalarTower R S (NodeAlgebra S (algebraMap R S a))] in
/-- Coefficient change commutes with the right chamber map. -/
@[simp]
theorem rightLaurentMap_map (x : NodeAlgebra R a) :
    rightLaurentMap (algebraMap R S a) (TauCeti.NodeAlgebra.map (S := S) a x) =
      AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S) (rightLaurentMap a x) := by
  let : Algebra R (NodeAlgebra S (algebraMap R S a)) := Algebra.compHom _ (algebraMap R S)
  let : IsScalarTower R S (NodeAlgebra S (algebraMap R S a)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have h : ((rightLaurentMap (algebraMap R S a)).restrictScalars R).comp (mapAlgHom a) =
      (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).comp (rightLaurentMap a) := by
    apply TauCeti.NodeAlgebra.hom_ext <;> simp [C, T, -single_eq_C_mul_T]
  exact DFunLike.congr_fun h x

omit [Algebra R (NodeAlgebra S (algebraMap R S a))]
  [IsScalarTower R S (NodeAlgebra S (algebraMap R S a))] in
/-- Both incoming lifts commute with coefficient change, including weight zero. -/
@[simp]
theorem map_incomingLift (i : Fin 2) (n : {n : ℤ | 0 ≤ n}) (u : grade R n.val) :
    TauCeti.NodeAlgebra.map (S := S) a (incomingLift a i n u) =
      incomingLift (algebraMap R S a) i n
        ⟨AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S) u,
          AddMonoidAlgebra.mapAlgHom_mem_gradeBy (Algebra.ofId R S) u.property⟩ := by
  simp [incomingLift_apply, Algebra.smul_def, coeff_mapAlgHom]

omit [Algebra R (NodeAlgebra S (algebraMap R S a))]
  [IsScalarTower R S (NodeAlgebra S (algebraMap R S a))] in
/-- Incoming lifts commute with coefficient change to any equal smoothing parameter. -/
@[simp]
theorem mapOfEq_incomingLift {a' : S} [Algebra R (NodeAlgebra S a')]
    [IsScalarTower R S (NodeAlgebra S a')] (h : algebraMap R S a = a')
    (i : Fin 2) (n : {n : ℤ | 0 ≤ n}) (u : grade R n.val) :
    mapOfEq a h (incomingLift a i n u) =
      incomingLift a' i n
        ⟨AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S) u,
          AddMonoidAlgebra.mapAlgHom_mem_gradeBy (Algebra.ofId R S) u.property⟩ := by
  subst a'
  simpa only [mapOfEq_rfl, mapAlgHom_apply] using map_incomingLift a i n u

/-- Coefficient change is a morphism of normal-weight slab correspondences.
It preserves both chamber maps and the chosen admissible lifts. -/
def normalWeightCorrespondenceMap :
    GradedCorrespondence.Hom (normalWeightCorrespondence a)
      ((normalWeightCorrespondence (algebraMap R S a)).restrictScalars R) id id where
  middle := (mapAlgHom (S := S) a).toLinearMap
  left := (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).toLinearMap
  right := (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).toLinearMap
  left_comm := by ext x; simp
  right_comm := by ext x; simp
  left_mem _ _ hx := AddMonoidAlgebra.mapAlgHom_mem_gradeBy (Algebra.ofId R S) hx
  right_mem _ _ hx := AddMonoidAlgebra.mapAlgHom_mem_gradeBy (Algebra.ofId R S) hx
  admissible_left _ hx := hx
  admissible_right _ hx := hx
  middle_liftLeft n u := by simp; rfl
  middle_liftRight n u := by simp; rfl

@[simp]
theorem normalWeightCorrespondenceMap_middle :
    (normalWeightCorrespondenceMap (S := S) a).middle = (mapAlgHom a).toLinearMap := (rfl)

@[simp]
theorem normalWeightCorrespondenceMap_left :
    (normalWeightCorrespondenceMap (S := S) a).left =
      (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).toLinearMap := (rfl)

@[simp]
theorem normalWeightCorrespondenceMap_right :
    (normalWeightCorrespondenceMap (S := S) a).right =
      (AddMonoidAlgebra.mapAlgHom ℤ (Algebra.ofId R S)).toLinearMap := (rfl)

end Mei.NodeAlgebra
