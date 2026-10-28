/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Degree
public import Mei.Geometry.Convex.Cone.LatticePoints
public import TauCeti.Geometry.Toric.Algebraic.Cone.Basic

/-!
# Module-probe cones and their lattice points

For a cone `σ` in a real space `V` and a vector `v`, the module-probe cone in
`V × ℝ × ℝ` is spanned by `σ × 0 × 0` and `(v, 1, 0)`. Its points are exactly the
`(y, t, 0)` with `t ≥ 0` and `y - t • v ∈ σ`.

When a lattice map `i : Γ →+ V` is extended by integer casts on the charge and probe
coordinates, the lattice points of the probe cone over `v = i p` are exactly the
extended degrees `(n + c • p, c, 0)` with `n` a lattice point of `σ` and `c ≥ 0`.
Hence, if the positive monoid `P` is the lattice-point monoid of `σ`, the module-probe
monoid `ModuleProbe.degreeMonoid` is the lattice-point monoid of the probe cone. The
probe cone is lattice rational when `σ` is, and is salient exactly when `σ` is. No
injectivity of `i` and no condition on the shift `p` is needed.

The module probe is the semidirect construction of Travis Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3, arXiv:1503.06183v5.
We use `IsLatticeRational.sup`, `IsLatticeRational.map` and `PointedCone.latticePoints`.
-/

public section

namespace PointedCone

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The module-probe cone in `V × ℝ × ℝ` over a cone `σ` with shift vector `v`:
the cone spanned by `σ × 0 × 0` and `(v, 1, 0)`. -/
def moduleProbe (σ : PointedCone ℝ V) (v : V) : PointedCone ℝ (V × ℝ × ℝ) :=
  σ.map (LinearMap.inl ℝ V (ℝ × ℝ)) ⊔ PointedCone.hull ℝ {(v, 1, 0)}

/-- The probe cone is the join of the charge-zero copy of `σ` and the ray of `(v, 1, 0)`. -/
theorem moduleProbe_def (σ : PointedCone ℝ V) (v : V) :
    σ.moduleProbe v = σ.map (LinearMap.inl ℝ V (ℝ × ℝ)) ⊔ PointedCone.hull ℝ {(v, 1, 0)} :=
  (rfl)

/-- A point lies in the probe cone exactly when its charge `t` is nonnegative, its
probe coordinate vanishes, and removing `t • v` leaves a point of `σ`. -/
@[simp]
theorem mem_moduleProbe {σ : PointedCone ℝ V} {v y : V} {t s : ℝ} :
    (y, t, s) ∈ σ.moduleProbe v ↔ y - t • v ∈ σ ∧ 0 ≤ t ∧ s = 0 := by
  rw [moduleProbe_def, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.mp ha
    obtain ⟨r, hr, rfl⟩ := PointedCone.mem_hull_singleton.mp hb
    simp only [LinearMap.inl_apply, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
      Prod.mk_add_mk, zero_add, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl, rfl⟩ := hab
    simpa using ⟨hx, hr⟩
  · rintro ⟨hy, ht, rfl⟩
    refine ⟨(y - t • v, 0, 0), PointedCone.mem_map.mpr ⟨_, hy, rfl⟩, t • (v, 1, 0),
      PointedCone.mem_hull_singleton.mpr ⟨t, ht, rfl⟩, ?_⟩
    simp

/-- The probe cone is salient exactly when `σ` is, for every shift vector. -/
@[simp]
theorem salient_moduleProbe_iff (σ : PointedCone ℝ V) (v : V) :
    (σ.moduleProbe v : ConvexCone ℝ (V × ℝ × ℝ)).Salient ↔ (σ : ConvexCone ℝ V).Salient := by
  constructor
  · intro h y hy hy0 hny
    exact h (y, 0, 0) (by simpa using hy) (by simpa using hy0) (by simpa using hny)
  · rintro h ⟨y, t, s⟩ hx hx0 hnx
    simp only [PointedCone.mem_toConvexCone, Prod.neg_mk, mem_moduleProbe] at hx hnx
    obtain ⟨hy, ht, rfl⟩ := hx
    obtain ⟨hny, hnt, -⟩ := hnx
    obtain rfl : t = 0 := le_antisymm (by linarith) ht
    simp only [neg_zero, zero_smul, sub_zero] at hy hny
    exact h y hy (by rintro rfl; exact hx0 rfl) hny

end PointedCone

namespace AddMonoidHom

variable {Γ V : Type*} [AddCommGroup Γ] [AddCommGroup V]

/-- The extension of a lattice map `i : Γ →+ V` to extended degrees, by integer casts
on the charge and probe coordinates. -/
def moduleProbeLatticeMap (i : Γ →+ V) : (Γ × ℤ × ℤ) →+ (V × ℝ × ℝ) :=
  i.prodMap ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))

/-- Evaluation of the extended lattice map. -/
@[simp]
theorem moduleProbeLatticeMap_apply (i : Γ →+ V) (x : Γ) (c l : ℤ) :
    i.moduleProbeLatticeMap (x, c, l) = (i x, (c : ℝ), (l : ℝ)) := (rfl)

end AddMonoidHom

namespace Mei.ModuleProbe

open TauCeti.Toric

variable {Γ V : Type*} [AddCommGroup Γ] [AddCommGroup V] [Module ℝ V]

/-- The probe cone over a lattice-rational cone and a lattice shift is lattice rational
for the extended lattice map. -/
theorem isLatticeRational_cone {i : Γ →+ V} {σ : PointedCone ℝ V}
    (hσ : IsLatticeRational i σ) (p : Γ) :
    IsLatticeRational i.moduleProbeLatticeMap (σ.moduleProbe (i p)) := by
  rw [PointedCone.moduleProbe_def]
  refine (hσ.map (f := AddMonoidHom.inl Γ (ℤ × ℤ)) fun n => ?_).sup ?_
  · simp [Prod.zero_eq_mk]
  · convert isLatticeRational_hull_image i.moduleProbeLatticeMap {(p, 1, 0)}
    simp

/-- An extended degree is a lattice point of the probe cone over `i p` exactly when its
charge `c` is nonnegative, its probe coordinate vanishes, and `x - c • p` is a lattice
point of `σ`. The lattice map `i` need not be injective. -/
theorem mem_latticePoints_cone {σ : PointedCone ℝ V} {i : Γ →+ V} {p x : Γ} {c l : ℤ} :
    (x, c, l) ∈ (σ.moduleProbe (i p)).latticePoints i.moduleProbeLatticeMap ↔
      x - c • p ∈ σ.latticePoints i ∧ 0 ≤ c ∧ l = 0 := by
  simp [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]

variable (d : PositiveDegrees Γ) (p : Γ)

/-- If the positive monoid is the lattice-point monoid of a cone `σ`, then the
module-probe monoid is the lattice-point monoid of the probe cone over `i p`. -/
theorem positiveDegrees_monoid_eq_latticePoints {i : Γ →+ V} {σ : PointedCone ℝ V}
    (hσ : d.monoid = σ.latticePoints i) :
    (positiveDegrees d p).monoid = (σ.moduleProbe (i p)).latticePoints i.moduleProbeLatticeMap := by
  ext ⟨x, c, l⟩
  rw [mem_positiveDegrees_monoid, mem_latticePoints_cone, hσ]

end Mei.ModuleProbe
