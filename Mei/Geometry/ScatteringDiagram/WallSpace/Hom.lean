/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.PositiveDegrees.Ray.Map

/-!
# Maps of completed wall groups

A graded Lie homomorphism preserving homogeneous wall spaces sends supported-ray
wall groups into the corresponding target wall groups. At finite order it uses
exactly the source cutoff prescribed by its positive degree map, or any larger
cutoff. Restricting the completed homomorphism gives a homomorphism of wall groups,
with identity and composition laws.

The source and target rays can be specified by their actual allowed degrees; no
freeness assumption is needed for this form. For a free target degree group,
`Mei.GradedLieHom.completedMap_mem_wallGroup_map` identifies the target using the
canonical supported-ray map, even when the primitive generator is not an allowed
degree or its image is nonprimitive. Fixed-degree maps take the same ray and normal.

The construction restricts `Mei.GradedLieHom.completedMap`, using its finite
projection formula and `LieHom.log_bchGroupMap`. Subgroup restriction uses
Mathlib's `MonoidHom.domRestrict` and `MonoidHom.codRestrict`.
-/

public section

namespace Mei

universe u

namespace GradedLieHom

variable {Γ Γ' Γ'' Λ Λ' Λ'' R : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommMonoid Λ] [AddCommMonoid Λ'] [AddCommMonoid Λ'']
  [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {p : PositiveDegrees Γ''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]
  {T : PositiveDegreeMap d e} {U : PositiveDegreeMap e p}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {H'' : DirectedWallSpaces ρ'' ℋ}
  {w : SupportedRay d} {v : SupportedRay e} {z : SupportedRay p}
  {m : Λ →+ ℤ} {m' : Λ' →+ ℤ} {m'' : Λ'' →+ ℤ}

/-- Wall-space preservation descends to finite ray Lie algebras at every source
cutoff at least as large as the prescribed modulus. -/
theorem truncatedMap_mem_truncatedRayLieSubalgebra (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    {a k : ℕ} (ha : T.modulus k ≤ a) {x : d.truncatedLie ℒ a}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m a) :
    f.truncatedMap k ha x ∈ H'.truncatedRayLieSubalgebra v m' k := by
  obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m a x).mp hx
  refine (H'.mem_truncatedRayLieSubalgebra v m' k _).mpr
    ⟨f y, H.map_mem_raySubmodule H' f.toLieHom.toLinearMap T hdegree hwall hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply] using (f.truncatedMap_mk k ha y).symm

variable [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']

/-- A wall-space-preserving graded map preserves completed wall labels, using
its original cutoff modulus. -/
theorem completedMap_mem_wallGroup (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    {g : d.completedBCHGroup ℒ} (hg : g ∈ H.wallGroup w m) :
    f.completedMap g ∈ H'.wallGroup v m' := by
  apply (H'.mem_wallGroup v m' _).mpr
  intro k
  rw [projection_completedMap]
  have hlog := (f.truncatedMap k le_rfl).log_bchGroupMap
    (CompletedGroup.projection (T.modulus k) g)
  exact hlog.symm ▸ f.truncatedMap_mem_truncatedRayLieSubalgebra hdegree hwall le_rfl
    ((H.mem_wallGroup w m g).mp hg (T.modulus k))

/-- Restrict a completed graded map to its source and target wall groups. -/
noncomputable def wallGroupMap (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m') :
    H.wallGroup w m →* H'.wallGroup v m' :=
  (f.completedMap.domRestrict (H.wallGroup w m)).codRestrict (H'.wallGroup v m')
    (fun g => f.completedMap_mem_wallGroup hdegree hwall g.property)

/-- The restricted wall-group map is the existing map on completed labels. -/
@[simp]
theorem coe_wallGroupMap_apply (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    (g : H.wallGroup w m) :
    (f.wallGroupMap hdegree hwall g : e.completedBCHGroup ℳ) = f.completedMap g := (rfl)

/-- The identity graded map restricts to the identity on every wall group. -/
@[simp]
theorem wallGroupMap_id :
    (id (d := d) ℒ).wallGroupMap (w := w) (v := w) (H := H) (H' := H)
      (m := m) (m' := m)
      (fun _ hn => by simpa only [PositiveDegreeMap.id_apply] using hn)
      (fun _ _ _ hx => by simpa only [id_apply, PositiveDegreeMap.id_apply] using hx) =
      MonoidHom.id (H.wallGroup w m) := by
  ext g : 1
  apply Subtype.ext
  simp [wallGroupMap]

/-- Wall-group restrictions respect composition, with the composite cutoff modulus. -/
theorem wallGroupMap_comp (g : GradedLieHom U ℳ ℋ) (f : GradedLieHom T ℒ ℳ)
    (hfdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    (hfwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    (hgdegree : ∀ n ∈ v.rayDegrees, U n ∈ z.rayDegrees)
    (hgwall : ∀ n ∈ v.rayDegrees, ∀ x ∈ H'.wall n m', g x ∈ H''.wall (U n) m'') :
    (g.comp f).wallGroupMap
      (fun n hn => by
        simpa only [PositiveDegreeMap.comp_apply] using hgdegree (T n) (hfdegree n hn))
      (fun n hn x hx => by
        simpa only [comp_apply, PositiveDegreeMap.comp_apply] using
          hgwall (T n) (hfdegree n hn) (f x) (hfwall n hn x hx)) =
      (g.wallGroupMap hgdegree hgwall).comp (f.wallGroupMap hfdegree hfwall) := by
  ext x : 1
  apply Subtype.ext
  -- Both sides are restrictions of the ambient completed homomorphisms.
  exact DFunLike.congr_fun (completedMap_comp g f) (x : d.completedBCHGroup ℒ)

/-- With a free target degree group, the target ray is the canonical transport of
the source ray. Only its actual allowed degrees enter the wall-preservation hypothesis. -/
theorem completedMap_mem_wallGroup_map [Module.Free ℤ Γ'] (f : GradedLieHom T ℒ ℳ)
    (hwall : ∀ n ∈ w.rayDegrees, ∀ x ∈ H.wall n m, f x ∈ H'.wall (T n) m')
    {g : d.completedBCHGroup ℒ} (hg : g ∈ H.wallGroup w m) :
    f.completedMap g ∈ H'.wallGroup
      (w.map T.toAddMonoidHom (fun _ hn => T.map_mem hn)
        (fun _ hn h0 => T.map_ne_zero hn h0)) m' := by
  exact f.completedMap_mem_wallGroup
    (fun _ hn => w.map_mem_rayDegrees T.toAddMonoidHom
      (fun _ hn => T.map_mem hn) (fun _ hn h0 => T.map_ne_zero hn h0) hn) hwall hg

end GradedLieHom
end Mei
