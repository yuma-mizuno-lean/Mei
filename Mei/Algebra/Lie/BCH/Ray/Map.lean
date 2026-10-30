/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Factor
public import Mei.Algebra.PositiveDegrees.Ray.Map

/-!
# Transport of completed supported-ray labels

A graded Lie homomorphism sends a completed ray label to the ray containing its
image degrees. The comparison uses the original cutoff modulus, also when the
source primitive generator is not an allowed degree or its image is nonprimitive.
The target ray can be specified by its actual degrees without a freeness hypothesis;
for a free target lattice it is the canonical transported supported ray.

Restricting the existing completed homomorphism gives a homomorphism between ray
subgroups, respecting identity and composition. In particular these results apply
directly to the graded maps of tropical pairings and to changes of positive degree.
No abelian-ray condition or injectivity of the degree or Lie map is required.
A degree-preserving endomorphism fixing the homogeneous pieces on a ray fixes every
completed label of that ray.
Taking a ray factor commutes with degree-preserving coefficient maps, even when
the coefficient map kills some or all of its logarithmic coefficients.

The finite support argument uses `Mei.GradedLieHom.map_mem_rayLieSubalgebra` and
`Mei.PositiveDegrees.map_rayLieSubalgebra_mkQ`. Completion uses
`Mei.GradedLieHom.projection_completedMap` and `LieHom.log_bchGroupMap`.
The restriction argument follows the wall-group construction in
`Mei.Geometry.ScatteringDiagram.WallSpace.Hom`, with all homogeneous pieces
on the ray in place of normal-dependent wall spaces.
-/

public section

namespace Mei.GradedLieHom

universe u

variable {N M P R : Type*} {L L' L'' : Type u}
  [AddCommGroup N] [AddCommGroup M] [AddCommGroup P] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [DecidableEq N] [DecidableEq M] [DecidableEq P]
  {d : PositiveDegrees N} {e : PositiveDegrees M} {p : PositiveDegrees P}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'} {ℋ : P → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]
  {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {w : SupportedRay d} {v : SupportedRay e} {z : SupportedRay p}

variable [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']

/-- A completed graded map preserves supported-ray labels with its original
cutoff modulus. Only actual allowed ray degrees need to map to the target ray. -/
theorem completedMap_mem_completedRaySubgroup (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    {g : d.completedBCHGroup ℒ} (hg : g ∈ d.completedRaySubgroup ℒ w) :
    f.completedMap g ∈ e.completedRaySubgroup ℳ v := by
  apply (e.mem_completedRaySubgroup ℳ v _).mpr
  intro k
  rw [projection_completedMap]
  have hlog := (f.truncatedMap k le_rfl).log_bchGroupMap
    (CompletedGroup.projection (T.modulus k) g)
  exact hlog.symm ▸ f.truncatedMap_mem_rayLieSubalgebra hdegree le_rfl
    ((d.mem_completedRaySubgroup ℒ w g).mp hg (T.modulus k))

/-- Restrict a completed graded homomorphism to two supported-ray subgroups. -/
noncomputable def rayGroupMap (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees) :
    d.completedRaySubgroup ℒ w →* e.completedRaySubgroup ℳ v :=
  (f.completedMap.domRestrict (d.completedRaySubgroup ℒ w)).codRestrict
    (e.completedRaySubgroup ℳ v)
    (fun g => f.completedMap_mem_completedRaySubgroup hdegree g.property)

/-- The restricted ray homomorphism agrees with the ambient completed map. -/
@[simp]
theorem coe_rayGroupMap_apply (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (g : d.completedRaySubgroup ℒ w) :
    (f.rayGroupMap hdegree g : e.completedBCHGroup ℳ) = f.completedMap g := (rfl)

/-- The identity graded map restricts to the identity on each completed ray subgroup. -/
@[simp]
theorem rayGroupMap_id :
    (id (d := d) ℒ).rayGroupMap (w := w) (v := w)
      (fun _ hn => by simpa only [PositiveDegreeMap.id_apply] using hn) =
      MonoidHom.id (d.completedRaySubgroup ℒ w) := by
  ext g : 1
  apply Subtype.ext
  simp

/-- Restriction to ray subgroups respects composition, with the same composite
cutoff modulus as the ambient completed maps. -/
theorem rayGroupMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ)
    (hf : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hg : ∀ n ∈ v.rayDegrees, U n ∈ z.rayDegrees) :
    (g.comp f).rayGroupMap
      (fun n hn => by simpa only [PositiveDegreeMap.comp_apply] using hg (T n) (hf n hn)) =
      (g.rayGroupMap hg).comp (f.rayGroupMap hf) := by
  ext x : 1
  apply Subtype.ext
  simpa only [MonoidHom.comp_apply, coe_rayGroupMap_apply] using
    DFunLike.congr_fun (completedMap_comp g f) (x : d.completedBCHGroup ℒ)

/-- For a free target degree group, the image label lies on the canonically
transported primitive ray. The generator may acquire a positive integer multiplier. -/
theorem completedMap_mem_completedRaySubgroup_map [Module.Free ℤ M]
    (f : GradedLieHom T ℒ ℳ) {g : d.completedBCHGroup ℒ}
    (hg : g ∈ d.completedRaySubgroup ℒ w) :
    f.completedMap g ∈ e.completedRaySubgroup ℳ
      (w.map T.toAddMonoidHom (fun _ hn => T.map_mem hn)
        (fun _ hn h0 => T.map_ne_zero hn h0)) :=
  f.completedMap_mem_completedRaySubgroup
    (fun _ hn => w.map_mem_rayDegrees T.toAddMonoidHom
      (fun _ hn => T.map_mem hn) (fun _ hn h0 => T.map_ne_zero hn h0) hn) hg

/-- A degree-preserving graded endomorphism fixing every homogeneous piece on a ray
pointwise fixes every completed label of that ray. -/
theorem completedMap_eq_self_of_mem_completedRaySubgroup
    (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℒ)
    (hf : ∀ n ∈ w.rayDegrees, ∀ x ∈ ℒ n, f x = x)
    {g : d.completedBCHGroup ℒ} (hg : g ∈ d.completedRaySubgroup ℒ w) :
    f.completedMap g = g := by
  apply CompletedGroup.ext
  intro k
  rw [f.projection_completedMap_of_le k (a := k) (by simp)]
  -- Read the tower projection as an element of the concrete finite BCH group.
  let y : d.truncatedGroup ℒ k := CompletedGroup.projection k g
  apply BCHGroup.log_injective
  refine ((f.truncatedMap (a := k) k (by simp)).log_bchGroupMap y).trans ?_
  have hle : (rayLieSubalgebra (d.truncatedGrading ℒ k) w).toSubmodule ≤
      LinearMap.eqLocus (f.truncatedMap (a := k) k (by simp)).toLinearMap LinearMap.id := by
    rw [rayLieSubalgebra_toSubmodule]
    refine iSup_le fun n => ?_
    rw [d.truncatedGrading_eq]
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearMap.mem_eqLocus, LieHom.coe_toLinearMap, LinearMap.id_apply,
      Submodule.mkQ_apply, f.truncatedMap_mk, hf n n.property x hx]
  exact LinearMap.mem_eqLocus.mp (hle ((d.mem_completedRaySubgroup ℒ w g).mp hg k))

variable {𝓝 : N → Submodule R L'} [GradedLieAlgebra 𝓝] [IsPositiveGrading d 𝓝]

/-- Taking a supported-ray factor commutes with degree-preserving coefficient
maps. Specializations may kill arbitrary coefficients, including a whole ray. -/
@[simp]
theorem completedMap_rayFactor (f : GradedLieHom (PositiveDegreeMap.id d) ℒ 𝓝)
    (g : d.completedBCHGroup ℒ) (w : SupportedRay d) :
    f.completedMap (d.rayFactor ℒ g w) = d.rayFactor 𝓝 (f.completedMap g) w := by
  apply d.ext_logComponent 𝓝
  intro n
  apply Subtype.ext
  rw [f.logComponent_completedMap]
  by_cases hn : n ∈ w.rayDegrees
  · rw [d.logComponent_rayFactor_of_mem ℒ g hn,
      d.logComponent_rayFactor_of_mem 𝓝 (f.completedMap g) hn,
      f.logComponent_completedMap]
  · rw [d.logComponent_rayFactor_of_notMem ℒ g hn,
      d.logComponent_rayFactor_of_notMem 𝓝 (f.completedMap g) hn]
    simp

end Mei.GradedLieHom
