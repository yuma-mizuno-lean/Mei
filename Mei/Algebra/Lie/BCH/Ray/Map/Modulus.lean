/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Ray.Map

/-!
# Ray factors under graded maps fixing every degree

A positive degree map `T : d → d` with `T n = n` for every degree may still carry a cutoff
modulus other than the identity, and need not be syntactically `PositiveDegreeMap.id d`; this
happens for degree maps assembled from other data. Completed maps along such a `T` commute with
taking supported-ray factors, as for `PositiveDegreeMap.id d`
(`TauCeti.GradedLieHom.completedMap_rayFactor`).
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading SupportedRay GradedLieHom)

namespace TauCeti.GradedLieHom

open Mei

universe u

variable {N R : Type*} {L L' : Type u} [AddCommGroup N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] [DecidableEq N]
  {d : PositiveDegrees N} {ℒ : N → Submodule R L} {𝓝 : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra 𝓝] [IsPositiveGrading d ℒ] [IsPositiveGrading d 𝓝]
  {T : PositiveDegreeMap d d}

/-- Taking a supported-ray factor commutes with completed maps along a degree map fixing every
degree, whatever its cutoff modulus. -/
theorem completedMap_rayFactor_of_forall_apply_eq (f : GradedLieHom T ℒ 𝓝) (hT : ∀ n, T n = n)
    (g : d.completedBCHGroup ℒ) (w : SupportedRay d) :
    f.completedMap (d.rayFactor ℒ g w) = d.rayFactor 𝓝 (f.completedMap g) w := by
  have hlog (x : d.completedBCHGroup ℒ) (n : N) :
      (d.logComponent 𝓝 (f.completedMap x) n : L') = f (d.logComponent ℒ x n : L) :=
    (congrArg (fun m => (d.logComponent 𝓝 (f.completedMap x) m : L')) (hT n)).symm.trans
      (f.logComponent_completedMap_of_injective (fun a b h => by rwa [hT, hT] at h) x n)
  apply d.ext_logComponent 𝓝
  intro n
  apply Subtype.ext
  rw [hlog]
  by_cases hn : n ∈ w.rayDegrees
  · rw [d.logComponent_rayFactor_of_mem ℒ g hn, d.logComponent_rayFactor_of_mem 𝓝 _ hn, hlog]
  · rw [d.logComponent_rayFactor_of_notMem ℒ g hn, d.logComponent_rayFactor_of_notMem 𝓝 _ hn]
    simp

end TauCeti.GradedLieHom
