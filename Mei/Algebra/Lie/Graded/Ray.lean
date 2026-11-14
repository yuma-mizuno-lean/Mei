/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Ray
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom
public import Mei.Algebra.Lie.Graded.Truncation.Transition
public import Mei.Algebra.PositiveDegrees.Ray.Basic
public import Mathlib.Algebra.Lie.Abelian

/-!
# Lie subalgebras on supported rays

The ray Lie algebra sums the homogeneous pieces on the actual allowed positive
multiples of a supported primitive vector. The vector itself need not be allowed.
Its elements are characterized by vanishing of all components off the ray.
Graded Lie maps transport ray support along their degree maps, including on
finite quotients with the source cutoff prescribed by the map's modulus.

`IsAbelianRays` says that each such Lie algebra is abelian. It can be checked on
pairs of homogeneous elements, and is inherited by degree-preserving surjective
maps on homogeneous pieces. This is the condition that permits independent labels
on one primitive ray to be combined without choosing their order.

The construction specializes `TauCeti.supportedLieSubalgebra`; the abelian criterion
uses Mathlib's `Submodule.iSup_induction` and `IsLieAbelian`.
-/

public section

open TauCeti

namespace Mei

variable {N R L L' : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  {d : PositiveDegrees N} (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- Abelian rays require commutation within each supported ray, not between distinct rays. -/
class IsAbelianRays (d : PositiveDegrees N) (ℒ : N → Submodule R L)
    [SetLike.GradedBracket ℒ ℒ] : Prop where
  /-- Each supported ray Lie algebra is abelian. -/
  isLieAbelian : ∀ w : SupportedRay d, IsLieAbelian (rayLieSubalgebra ℒ w)

attribute [instance] IsAbelianRays.isLieAbelian

/-- Two elements of one ray Lie algebra have zero bracket when rays are abelian. -/
theorem lie_eq_zero_of_mem_rayLieSubalgebra [IsAbelianRays d ℒ]
    {w : SupportedRay d} {x y : L}
    (hx : x ∈ rayLieSubalgebra ℒ w) (hy : y ∈ rayLieSubalgebra ℒ w) : ⁅x, y⁆ = 0 :=
  congrArg Subtype.val (trivial_lie_zero (rayLieSubalgebra ℒ w)
    (rayLieSubalgebra ℒ w) ⟨x, hx⟩ ⟨y, hy⟩)

/-- Abelian rays can be checked on homogeneous pairs at actual allowed ray degrees. -/
theorem isAbelianRays_iff : IsAbelianRays d ℒ ↔
    ∀ (w : SupportedRay d) (n m : N), n ∈ w.rayDegrees → m ∈ w.rayDegrees →
      ∀ x ∈ ℒ n, ∀ y ∈ ℒ m, ⁅x, y⁆ = 0 := by
  exact ⟨fun h w n m hn hm => (TauCeti.isLieAbelian_rayLieSubalgebra_iff ℒ w).mp
    (h.isLieAbelian w) n hn m hm, fun h => ⟨fun w =>
      (TauCeti.isLieAbelian_rayLieSubalgebra_iff ℒ w).mpr
        (fun n hn m hm => h w n m hn hm)⟩⟩

/-- Every grading of an abelian ambient Lie algebra has abelian rays. -/
instance [IsLieAbelian L] : IsAbelianRays d ℒ :=
  (isAbelianRays_iff ℒ).mpr fun _ _ _ _ _ _ _ _ _ => trivial_lie_zero L L _ _

variable (ℳ : N → Submodule R L') [SetLike.GradedBracket ℳ ℳ]

/-- Surjectivity on homogeneous pieces preserves abelian rays, without injectivity. -/
theorem isAbelianRays_of_map_eq [IsAbelianRays d ℒ]
    (f : L →ₗ⁅R⁆ L') (hf : ∀ n, (ℒ n).map f.toLinearMap = ℳ n) :
    IsAbelianRays d ℳ := by
  apply (isAbelianRays_iff ℳ).mpr
  intro w n m hn hm x hx y hy
  rw [← hf n, Submodule.mem_map] at hx
  rw [← hf m, Submodule.mem_map] at hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (f.map_lie a b).symm.trans (by
    rw [(isAbelianRays_iff ℒ).mp ‹IsAbelianRays d ℒ› w n m hn hm a ha b hb, map_zero])

variable [DecidableEq N] [DirectSum.Decomposition ℒ]

end Mei

namespace TauCeti.PositiveDegrees

open Mei

variable {N R L : Type*} [AddCommGroup N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Taking the degree quotient commutes with forming a ray Lie algebra. -/
@[simp]
theorem map_rayLieSubalgebra_mkQ (w : SupportedRay d) (k : ℕ) :
    (rayLieSubalgebra ℒ w).map (d.degreeIdeal ℒ k).mkQ =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simpa only [rayLieSubalgebra_def] using
    d.map_mkQ_supportedLieSubalgebra ℒ w.degreeSemigroup k

/-- Degree truncation maps a ray algebra onto its lower-order counterpart. -/
theorem map_rayLieSubalgebra_truncationMap (w : SupportedRay d) {k l : ℕ} (h : k ≤ l) :
    (rayLieSubalgebra (d.truncatedGrading ℒ l) w).map (d.truncationMap ℒ h) =
      rayLieSubalgebra (d.truncatedGrading ℒ k) w := by
  simpa only [rayLieSubalgebra_def] using
    d.map_truncationMap_supportedLieSubalgebra ℒ w.degreeSemigroup h

/-- Finite degree quotients inherit abelian rays. -/
instance isAbelianRays_truncatedGrading [IsAbelianRays d ℒ] (k : ℕ) :
    IsAbelianRays d (d.truncatedGrading ℒ k) :=
  isAbelianRays_of_map_eq ℒ (d.truncatedGrading ℒ k) (d.degreeIdeal ℒ k).mkQ
    (fun n => (d.truncatedGrading_eq ℒ k n).symm)

end TauCeti.PositiveDegrees

namespace TauCeti.GradedLieHom

open Mei

variable {N M R L L' : Type*} [AddCommGroup N] [AddCommGroup M] [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  {d : PositiveDegrees N} {e : PositiveDegrees M} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℳ : M → Submodule R L'}
  {w : SupportedRay d} {v : SupportedRay e}

/-- A graded Lie map preserves ray support whenever its degree map carries the
actual source ray degrees into the chosen target ray. No lattice freeness,
internal decomposition or positivity of the homogeneous pieces is required. -/
theorem map_mem_rayLieSubalgebra [SetLike.GradedBracket ℒ ℒ] [SetLike.GradedBracket ℳ ℳ]
    (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    {x : L} (hx : x ∈ rayLieSubalgebra ℒ w) : f x ∈ rayLieSubalgebra ℳ v := by
  have hle : rayLieSubalgebra ℒ w ≤ (rayLieSubalgebra ℳ v).comap f.toLieHom :=
    (rayLieSubalgebra_le_iff ℒ w _).mpr fun n hn _ hx =>
      le_rayLieSubalgebra ℳ (hdegree n hn) (f.map_mem hx)
  exact hle hx

variable [DecidableEq N] [DecidableEq M]
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ]

/-- Ray support is preserved at finite order, for any source cutoff at least
the order prescribed by the positive degree map. -/
theorem truncatedMap_mem_rayLieSubalgebra (f : GradedLieHom T ℒ ℳ)
    (hdegree : ∀ n ∈ w.rayDegrees, T n ∈ v.rayDegrees)
    {a k : ℕ} (ha : T.modulus k ≤ a) {x : d.truncatedLie ℒ a}
    (hx : x ∈ rayLieSubalgebra (d.truncatedGrading ℒ a) w) :
    f.truncatedMap k ha x ∈ rayLieSubalgebra (e.truncatedGrading ℳ k) v := by
  rw [← d.map_rayLieSubalgebra_mkQ ℒ w a] at hx
  obtain ⟨y, hy, rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hx
  rw [← e.map_rayLieSubalgebra_mkQ ℳ v k]
  refine (LieSubalgebra.mem_map _ _ _).mpr
    ⟨f y, f.map_mem_rayLieSubalgebra hdegree hy, ?_⟩
  simpa only [LieIdeal.mkQ_apply] using (f.truncatedMap_mk k ha y).symm

end TauCeti.GradedLieHom
