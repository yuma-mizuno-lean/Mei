/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Coordinates
public import Mei.Algebra.Lie.Logarithmic.WallFunction
public import Mei.RingTheory.FilteredAlgebra.Exp.Pow

/-!
# Function-wall labels under graded maps of tropical vertex algebras

Fix characters `m` and `m'` of two spatial lattices and a positive degree map `T` sending the
degrees tangent to `m` to degrees tangent to `m'`; for integral characters this holds when `T`
lies over a tangent map `t` with `m' ∘ t` a rational multiple of `m`
(`Mei.map_tropicalTangentMonoid_intCast_le`). The monomial map `z^q ↦ z^{T q}` of tangent
coefficients (`Mei.tropicalTangentMap`) extends to completed tangent coefficients with the cutoff
modulus of `T` (`Mei.completedTropicalTangentMap`) and commutes with completed exponentials and
logarithms (`Mei.completedTropicalTangentMap_completedExp`,
`Mei.completedTropicalTangentMap_completedLog`).

Let `f` be a graded Lie map between tropical vertex Lie algebras sending every tangent field
`z^q ∂_m`, `q ≠ 0`, to `c • z^{T q} ∂_{m'}`; its own degree map and cutoff modulus may differ
from `T`. Then `f` sends `v ∂_m` to `(c • T_* v) ∂_{m'}`
(`TauCeti.GradedLieHom.map_tropicalTangentField`) and the completed function-wall label
`exp(u ∂_m)` to `exp((c • T_* u) ∂_{m'})`
(`TauCeti.GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField`).

If moreover `r * c = 1` for a natural number `r` and `T_* f₀ = f₁ ^ r`, then `exp(log(f₀) ∂_m)`
is sent to `exp(log(f₁) ∂_{m'})`
(`TauCeti.GradedLieHom.completedMap_completedBCHExp_completedTropicalTangentField_completedLog`).
These labels act on coefficients by `z^p ↦ z^p f₀^{m(ρ p)}` and `z^p ↦ z^p f₁^{m'(ρ' p)}`
(`Mei.completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog`), so for
primitive integral normals `m` and `m'` the image of the wall function `f₀` is the `r`-th power
of the wall function `f₁`. The finite-index pushforwards of
`Mei.DirectedWall.Pushforward.ofFiniteIndex` are maps of this kind, with `c` the inverse of the
normal comparison scalar.

The tropical vertex group and its function walls are those of Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap GradedLieHom)

noncomputable section

section

open Mei

open _root_.AddMonoidAlgebra

universe v w

variable {R : Type*} {Γ Γ' : Type v} {Λ Λ' : Type w} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}

namespace Mei

section TangentMap

variable (T : PositiveDegreeMap d e) {m : Λ →+ R} {m' : Λ' →+ R}
  (hT : (tropicalTangentMonoid d ρ m).map T.toAddMonoidHom ≤ tropicalTangentMonoid e ρ' m')

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ m)
local notation "G'" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' m')

/-- The monomial map `z^q ↦ z^(T q)` from coefficients tangent to `m` to coefficients tangent
to `m'`. -/
def tropicalTangentMap :
    R[tropicalTangentMonoid d ρ m] →ₐ[R] R[tropicalTangentMonoid e ρ' m'] :=
  mapDomainAlgHom R R
    ((AddSubmonoid.inclusion hT).comp (T.toAddMonoidHom.addSubmonoidMap _))

/-- The tangent monomial map sends `c z^q` to `c z^(T q)`. -/
@[simp]
theorem tropicalTangentMap_single (q : tropicalTangentMonoid d ρ m) (c : R) :
    tropicalTangentMap T hT (single q c) =
      single ⟨T q, hT (AddSubmonoid.mem_map_of_mem _ q.property)⟩ c := by
  have hq : (AddSubmonoid.inclusion hT).comp (T.toAddMonoidHom.addSubmonoidMap _) q =
      ⟨T q, hT (AddSubmonoid.mem_map_of_mem _ q.property)⟩ := by
    apply Subtype.ext
    rw [AddMonoidHom.comp_apply, AddSubmonoid.coe_inclusion,
      AddMonoidHom.addSubmonoidMap_apply_coe]
  rw [tropicalTangentMap, mapDomainAlgHom_apply, mapDomain_single, hq]

/-- The tangent monomial map preserves the filtration terms above the cutoff modulus. -/
theorem filtration_ideal_le_comap_tropicalTangentMap (k : ℕ) :
    (G).ideal (T.modulus k + 1) ≤ ((G').ideal (k + 1)).comap (tropicalTangentMap T hT) :=
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom T hT k

/-- The tangent monomial map preserves the first filtration term. -/
theorem filtration_ideal_one_le_comap_tropicalTangentMap :
    (G).ideal 1 ≤ ((G').ideal 1).comap (tropicalTangentMap T hT) :=
  TropicalVertexCoefficientAction.filtration_ideal_one_le_comap_mapDomainAlgHom T hT

/-- The tangent monomial map `z^q ↦ z^(T q)` on completed tangent coefficients, with the
cutoff modulus of `T`. -/
def completedTropicalTangentMap : (G).completion →ₐ[R] (G').completion :=
  (G).mapCompletionₐ (G') (tropicalTangentMap T hT) T.modulus T.monotone_modulus
    (filtration_ideal_le_comap_tropicalTangentMap T hT)

/-- At order `k`, the completed tangent monomial map is the quotient map at source order
`T.modulus k`. -/
@[simp]
theorem projection_completedTropicalTangentMap (k : ℕ) (u : (G).completion) :
    (G').projection k (completedTropicalTangentMap T hT u) =
      Ideal.quotientMapₐ ((G').ideal (k + 1)) (tropicalTangentMap T hT)
        (filtration_ideal_le_comap_tropicalTangentMap T hT k) ((G).projection (T.modulus k) u) :=
  (G).projection_mapCompletionₐ (G') _ _ _ _ k u

/-- Any source order at least `T.modulus k` computes the order-`k` projection of the completed
tangent monomial map. -/
theorem projection_completedTropicalTangentMap_of_le (k a : ℕ) (ha : T.modulus k ≤ a)
    (u : (G).completion) :
    (G').projection k (completedTropicalTangentMap T hT u) =
      Ideal.quotientMapₐ ((G').ideal (k + 1)) (tropicalTangentMap T hT)
        (((G).antitone (Nat.add_le_add_right ha 1)).trans
          (filtration_ideal_le_comap_tropicalTangentMap T hT k)) ((G).projection a u) :=
  (G).projection_mapCompletionₐ_of_le (G') _ _ _ _ k a ha u

/-- The completed tangent monomial map extends the finite one. -/
@[simp]
theorem completedTropicalTangentMap_toCompletion (u : R[tropicalTangentMonoid d ρ m]) :
    completedTropicalTangentMap T hT ((G).toCompletion u) =
      (G').toCompletion (tropicalTangentMap T hT u) :=
  (G).mapCompletionₐ_toCompletion (G') _ _ _ _ u

/-- The completed tangent monomial map preserves the first completed ideal. -/
theorem completedTropicalTangentMap_mem_completionIdeal_one {u : (G).completion}
    (hu : u ∈ (G).completionIdeal 1) :
    completedTropicalTangentMap T hT u ∈ (G').completionIdeal 1 := by
  rw [completedTropicalTangentMap, ← AlgHom.coe_toRingHom, AlgFiltration.coe_mapCompletionₐ]
  exact (G).mapCompletion_mem_first (G') _ _ _ _
    (filtration_ideal_one_le_comap_tropicalTangentMap T hT) hu

/-- The completed tangent monomial map sends coefficients congruent to one to coefficients
congruent to one. -/
theorem completedTropicalTangentMap_sub_one_mem {u : (G).completion}
    (hu : u - 1 ∈ (G).completionIdeal 1) :
    completedTropicalTangentMap T hT u - 1 ∈ (G').completionIdeal 1 := by
  simpa only [map_sub, map_one] using completedTropicalTangentMap_mem_completionIdeal_one T hT hu

variable [Algebra ℚ R]

/-- The completed tangent monomial map commutes with completed exponentials. -/
@[simp]
theorem completedTropicalTangentMap_completedExp (x : (G).completionIdeal 1) :
    completedTropicalTangentMap T hT ((G).completedExp x) =
      (G').completedExp ⟨completedTropicalTangentMap T hT x,
        completedTropicalTangentMap_mem_completionIdeal_one T hT x.property⟩ := by
  simp only [completedTropicalTangentMap, ← AlgHom.coe_toRingHom,
    AlgFiltration.coe_mapCompletionₐ]
  exact (G).mapCompletion_completedExp (G') _ _ _ _
    (filtration_ideal_one_le_comap_tropicalTangentMap T hT) x

/-- The completed tangent monomial map commutes with completed logarithms. -/
@[simp]
theorem completedTropicalTangentMap_completedLog
    (u : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1}) :
    completedTropicalTangentMap T hT ((G).completedLog u) =
      (G').completedLog ⟨completedTropicalTangentMap T hT u,
        completedTropicalTangentMap_sub_one_mem T hT u.property⟩ := by
  simp only [completedTropicalTangentMap, ← AlgHom.coe_toRingHom,
    AlgFiltration.coe_mapCompletionₐ]
  exact (G).mapCompletion_completedLog (G') _ _ _ _
    (filtration_ideal_one_le_comap_tropicalTangentMap T hT) u

/-- If a positive degree map lies over a tangent map `t`, and `μ' ∘ t = a • μ` for rational
`a`, then degrees tangent to `μ` map to degrees tangent to `μ'`. -/
theorem map_tropicalTangentMonoid_intCast_le {t : Λ →+ Λ'}
    (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n)) {μ : Λ →+ ℤ} {μ' : Λ' →+ ℤ} {a : ℚ}
    (hμ : ∀ x, (μ' (t x) : ℚ) = a * μ x) :
    (tropicalTangentMonoid d ρ ((Int.castAddHom R).comp μ)).map T.toAddMonoidHom ≤
      tropicalTangentMonoid e ρ' ((Int.castAddHom R).comp μ') := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_tropicalTangentMonoid] at hx
  rw [mem_tropicalTangentMonoid]
  refine ⟨T.map_mem hx.1, ?_⟩
  have hx₀ := hx.2
  simp only [AddMonoidHom.comp_apply, Int.coe_castAddHom] at hx₀ ⊢
  rw [hρ x hx.1, ← map_intCast (algebraMap ℚ R), hμ, map_mul, map_intCast, hx₀, mul_zero]

end TangentMap

end Mei

namespace TauCeti.GradedLieHom

open Mei

open LogarithmicVectorField

variable [DecidableEq Γ] [DecidableEq Γ']
  {T₀ : PositiveDegreeMap d e}
  (f : GradedLieHom T₀ (tropicalVertexGrading (R := R) d ρ) (tropicalVertexGrading e ρ'))
  {T : PositiveDegreeMap d e} {m : Λ →+ R} {m' : Λ' →+ R}
  (hT : (tropicalTangentMonoid d ρ m).map T.toAddMonoidHom ≤ tropicalTangentMonoid e ρ' m')
  {c : R}
  (hf : ∀ (q : tropicalTangentMonoid d ρ m), (q : Γ) ≠ 0 →
    ∀ x : tropicalVertexLieAlgebra (R := R) d ρ, single ρ q m = x.val →
      (f x).val = c • single ρ' (T q) m')

include hf in
/-- A graded Lie map sending each tangent field `z^q ∂_m` to `c • z^{T q} ∂_{m'}` sends the
tangent field `v ∂_m` to the tangent field `(c • T_* v) ∂_{m'}`. -/
theorem map_tropicalTangentField (v : R[tropicalTangentMonoid d ρ m]) :
    f (tropicalTangentField d ρ m v) =
      tropicalTangentField e ρ' m' (c • tropicalTangentMap T hT v) := by
  induction v using induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, smul_add, map_add, ha, hb]
  | single q a =>
    rw [show single q a = a • single q (1 : R) by rw [smul_single', mul_one]]
    simp only [map_smul, tropicalTangentMap_single]
    by_cases hq : (q : Γ) = 0
    · have h0 : (⟨T q, hT (AddSubmonoid.mem_map_of_mem _ q.property)⟩ :
          tropicalTangentMonoid e ρ' m') = 0 := Subtype.ext (by simp [hq])
      rw [h0, show q = 0 from Subtype.ext hq, tropicalTangentField_single_zero,
        tropicalTangentField_single_zero, map_zero, smul_zero, smul_zero]
    have hTq : T q ≠ 0 := T.map_ne_zero ((mem_tropicalTangentMonoid d ρ m q).mp q.2).1 hq
    have hx := hf q hq (tropicalTangentField d ρ m (single q 1))
      (by rw [coe_tropicalTangentField_single d ρ m hq, one_smul])
    apply Subtype.ext
    rw [SetLike.val_smul, hx, SetLike.val_smul, SetLike.val_smul,
      coe_tropicalTangentField_single e ρ' m' (q := ⟨T q, _⟩) hTq, one_smul, smul_comm]

variable [Algebra ℚ R]

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℒ'" => tropicalVertexGrading (R := R) e ρ'
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) d
  (tropicalTangentMonoid d ρ m)
local notation "G'" => TropicalVertexCoefficientAction.filtration (R := R) e
  (tropicalTangentMonoid e ρ' m')

include hf in
/-- A graded Lie map sending each tangent field `z^q ∂_m` to `c • z^{T q} ∂_{m'}` sends the
completed function-wall label `exp(u ∂_m)` to `exp((c • T_* u) ∂_{m'})`. -/
theorem completedMap_completedBCHExp_completedTropicalTangentField (u : (G).completion) :
    f.completedMap (d.completedBCHExp ℒ (completedTropicalTangentField d ρ m u)) =
      e.completedBCHExp ℒ'
        (completedTropicalTangentField e ρ' m' (c • completedTropicalTangentMap T hT u)) := by
  apply (e.completedBCHExp ℒ').symm.injective
  rw [completedBCHExp_symm_completedMap, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  apply ModuleFiltration.completion_ext
  intro k
  let a := max (T₀.modulus k) (T.modulus k)
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((G).projection a u)
  have hv' : (G').projection k (c • completedTropicalTangentMap T hT u) =
      Ideal.Quotient.mk _ (c • tropicalTangentMap T hT v) := by
    rw [← AlgFiltration.projectionₐ_apply (R := R), map_smul, AlgFiltration.projectionₐ_apply,
      projection_completedTropicalTangentMap_of_le T hT k a (le_max_right _ _), ← hv,
      Ideal.quotient_map_mkₐ, ← map_smul, Ideal.Quotient.mkₐ_eq_mk]
  rw [ModuleFiltration.projection_completionMap_of_le _ _ _ _ _ _ k a (le_max_left _ _),
    ← LieIdeal.completionProjection_apply,
    completionProjection_completedTropicalTangentField d ρ m _ u v hv.symm,
    ← LieIdeal.completionProjection_apply,
    completionProjection_completedTropicalTangentField e ρ' m' k _ _ hv',
    ← f.map_tropicalTangentField hT hf]
  simp only [LieIdeal.mkQ_apply, Submodule.mapQ_apply, LieHom.coe_toLinearMap, coe_toLieHom]

include hf in
/-- **Power comparison of function walls.** Let a graded Lie map send each tangent field
`z^q ∂_m` to `c • z^{T q} ∂_{m'}`, where `r * c = 1` for a natural number `r`. If the tangent
monomial map sends `f₀` to `f₁ ^ r`, the function-wall label `exp(log(f₀) ∂_m)` is sent to
`exp(log(f₁) ∂_{m'})`. -/
theorem completedMap_completedBCHExp_completedTropicalTangentField_completedLog {r : ℕ}
    (hr : (r : R) * c = 1) (f₀ : {u : (G).completion // u - 1 ∈ (G).completionIdeal 1})
    (f₁ : {u : (G').completion // u - 1 ∈ (G').completionIdeal 1})
    (hf₀ : completedTropicalTangentMap T hT f₀ = (f₁ : (G').completion) ^ r) :
    f.completedMap
        (d.completedBCHExp ℒ (completedTropicalTangentField d ρ m ((G).completedLog f₀))) =
      e.completedBCHExp ℒ' (completedTropicalTangentField e ρ' m' ((G').completedLog f₁)) := by
  rw [f.completedMap_completedBCHExp_completedTropicalTangentField hT hf,
    completedTropicalTangentMap_completedLog]
  have he : (⟨completedTropicalTangentMap T hT f₀,
      completedTropicalTangentMap_sub_one_mem T hT f₀.property⟩ :
        {u : (G').completion // u - 1 ∈ (G').completionIdeal 1}) =
      ⟨(f₁ : (G').completion) ^ r, (G').pow_sub_one_mem f₁ r⟩ := Subtype.ext hf₀
  rw [he, AlgFiltration.completedLog_pow, ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm, hr,
    one_smul]

end TauCeti.GradedLieHom

end
