/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map
public import Mei.RingTheory.GradedAlgebra.Shifted.Basic

/-!
# Multiplicativity of shifted quantum coefficient transport

Compatible scalar and degree maps preserve finite-quotient and completed shifted
products for arbitrary bilinear forms. Neither scalar nor exponent injectivity
is required.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

private theorem positiveMap_smul' (r : R) (x : positiveSubalgebra q β d.monoid) :
    positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn) (r • x) =
      φ r • positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn) x := by
  apply Subtype.ext
  simp only [Subalgebra.coe_smul, coe_positiveMap]
  exact map_smul φ T.toAddMonoidHom h r x

/-- Transport ordinary coefficients in a translated support by the ambient quantum map. -/
def mapShiftedSupport (p : Γ) :
    shiftedSubmodule (grade q β) d.monoid p →ₛₗ[φ]
      shiftedSubmodule (grade q' β') e.monoid (T p) where
  toFun x := positiveShiftEquiv q' β' e (T p)
    (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn)
      ((positiveShiftEquiv q β d p).symm x))
  map_add' x y := by
    rw [LinearEquiv.map_add,
      (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
        (fun _ hn => T.map_mem hn)).map_add, LinearEquiv.map_add]
  map_smul' r x := by
    rw [LinearEquiv.map_smul, positiveMap_smul', LinearEquiv.map_smul]

/-- The finite support map is the original ambient scalar and exponent map. -/
theorem coe_mapShiftedSupport (p : Γ) (x : shiftedSubmodule (grade q β) d.monoid p) :
    (mapShiftedSupport d e T φ h p x : QuantumMonoidAlgebra q' β') =
      map φ T.toAddMonoidHom h x := by
  have hm := map_positiveShiftEquiv d e T φ h p ((positiveShiftEquiv q β d p).symm x)
  have he := congrArg (fun z : shiftedSubmodule (grade q β) d.monoid p =>
    (z : QuantumMonoidAlgebra q β)) ((positiveShiftEquiv q β d p).apply_symm_apply x)
  exact hm.symm.trans (congrArg (map φ T.toAddMonoidHom h) he)

private theorem mapShiftedSupport_coordinates (p : Γ)
    (x : positiveSubalgebra q β d.monoid) :
    mapShiftedSupport d e T φ h p (positiveShiftEquiv q β d p x) =
      positiveShiftEquiv q' β' e (T p)
        (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
          (fun _ hn => T.map_mem hn) x) := by
  simp only [mapShiftedSupport, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.symm_apply_apply]

/-- The original finite quotient map is induced by the ambient map of translated supports. -/
theorem mapShiftedQuotient_mk (p : Γ) (k : ℕ)
    (x : shiftedSubmodule (grade q β) d.monoid p) :
    mapShiftedQuotient d e T φ h p k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (mapShiftedSupport d e T φ h p x) := by
  obtain ⟨y, rfl⟩ := (positiveShiftEquiv q β d p).surjective x
  exact (mapShiftedQuotient_mk_coordinates d e T φ h p k y).trans
    (congrArg Submodule.Quotient.mk (mapShiftedSupport_coordinates d e T φ h p y).symm)

private theorem coe_cast_shiftedSupport {p r : Γ'} (hpr : p = r)
    (x : shiftedSubmodule (grade q' β') e.monoid p) :
    ((cast (congrArg (fun u => ↥(shiftedSubmodule (grade q' β') e.monoid u)) hpr) x :
      shiftedSubmodule (grade q' β') e.monoid r) : QuantumMonoidAlgebra q' β') =
        (x : QuantumMonoidAlgebra q' β') := by
  subst r
  rfl

private theorem mapShiftedSupport_mul (p r : Γ)
    (x : shiftedSubmodule (grade q β) d.monoid p)
    (y : shiftedSubmodule (grade q β) d.monoid r) :
    cast (congrArg (fun u => ↥(shiftedSubmodule (grade q' β') e.monoid u))
        (map_add T.toAddMonoidHom p r))
        (mapShiftedSupport d e T φ h (p + r) (shiftedMul (grade q β) d.monoid p r x y)) =
      shiftedMul (grade q' β') e.monoid (T p) (T r)
        (mapShiftedSupport d e T φ h p x) (mapShiftedSupport d e T φ h r y) := by
  apply Subtype.ext
  rw [coe_cast_shiftedSupport e (map_add T.toAddMonoidHom p r)
    (mapShiftedSupport d e T φ h (p + r) (shiftedMul (grade q β) d.monoid p r x y))]
  simp only [coe_mapShiftedSupport, coe_shiftedMul, _root_.map_mul]

private theorem cast_shiftedQuotient_mk {p r : Γ'} (hpr : p = r) (k : ℕ)
    (x : shiftedSubmodule (grade q' β') e.monoid p) :
    cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k) hpr)
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (cast (congrArg (fun u => ↥(shiftedSubmodule (grade q' β') e.monoid u)) hpr) x) := by
  subst r
  rfl

private theorem mapShiftedQuotient_mul_mk (p r : Γ) (k : ℕ)
    (a : shiftedSubmodule (grade q β) d.monoid p)
    (b : shiftedSubmodule (grade q β) d.monoid r) :
    cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k)
        (map_add T.toAddMonoidHom p r))
      (mapShiftedQuotient d e T φ h (p + r) k
        (d.shiftedQuotientMul (grade q β) p r (T.modulus k)
          (Submodule.Quotient.mk a) (Submodule.Quotient.mk b))) =
      e.shiftedQuotientMul (grade q' β') (T p) (T r) k
        (mapShiftedQuotient d e T φ h p k (Submodule.Quotient.mk a))
        (mapShiftedQuotient d e T φ h r k (Submodule.Quotient.mk b)) := by
  simp only [PositiveDegrees.shiftedQuotientMul_mk, mapShiftedQuotient_mk]
  rw [cast_shiftedQuotient_mk e (map_add T.toAddMonoidHom p r) k
    (mapShiftedSupport d e T φ h (p + r) (shiftedMul (grade q β) d.monoid p r a b))]
  exact congrArg (fun z : shiftedSubmodule (grade q' β') e.monoid (T p + T r) =>
    (Submodule.Quotient.mk z : (e.shiftedFiltration (grade q' β') (T p + T r)).quotient k))
      (mapShiftedSupport_mul d e T φ h p r a b)

/-- Finite product transport needs no alternation hypothesis on either bilinear form. -/
theorem mapShiftedQuotient_mul (p r : Γ) (k : ℕ)
    (x : (d.shiftedFiltration (grade q β) p).quotient (T.modulus k))
    (y : (d.shiftedFiltration (grade q β) r).quotient (T.modulus k)) :
    cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k)
        (map_add T.toAddMonoidHom p r))
      (mapShiftedQuotient d e T φ h (p + r) k
        (d.shiftedQuotientMul (grade q β) p r (T.modulus k) x y)) =
      e.shiftedQuotientMul (grade q' β') (T p) (T r) k
        (mapShiftedQuotient d e T φ h p k x) (mapShiftedQuotient d e T φ h r k y) := by
  -- Exists.elim retains typed quotient equalities without substituting through the cast tower.
  refine (((d.shiftedFiltration (grade q β) p).submodule
    (T.modulus k + 1)).mkQ_surjective x).elim fun a ha => ?_
  refine (((d.shiftedFiltration (grade q β) r).submodule
    (T.modulus k + 1)).mkQ_surjective y).elim fun b hb => ?_
  let C := cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k)
    (map_add T.toAddMonoidHom p r))
  have hl := congrArg₂ (fun u v => C (mapShiftedQuotient d e T φ h (p + r) k
    (d.shiftedQuotientMul (grade q β) p r (T.modulus k) u v))) ha hb
  have hr := congrArg₂ (fun u v => e.shiftedQuotientMul (grade q' β') (T p) (T r) k
    (mapShiftedQuotient d e T φ h p k u) (mapShiftedQuotient d e T φ h r k v)) ha hb
  exact (hl.symm).trans <|
    (mapShiftedQuotient_mul_mk d e T φ h p r k a b).trans <|
    hr

private theorem projection_cast_completed {p r : Γ'} (hpr : p = r) (k : ℕ)
    (x : e.ShiftedCoefficients (grade q' β') p) :
    (e.shiftedFiltration (grade q' β') r).projection k
        (cast (congrArg (e.ShiftedCoefficients (grade q' β')) hpr) x) =
      cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k) hpr)
        ((e.shiftedFiltration (grade q' β') p).projection k x) :=
by
  -- Projection is indexed by the same degree; equality elimination identifies both carriers.
  subst r
  rfl

private theorem exists_mapShiftedSupport_projection (p : Γ) (k : ℕ)
    (x : d.ShiftedCoefficients (grade q β) p) :
    ∃ a : shiftedSubmodule (grade q β) d.monoid p,
      (Submodule.Quotient.mk a : (d.shiftedFiltration (grade q β) p).quotient (T.modulus k)) =
        (d.shiftedFiltration (grade q β) p).projection (T.modulus k) x ∧
      (Submodule.Quotient.mk (mapShiftedSupport d e T φ h p a) :
          (e.shiftedFiltration (grade q' β') (T p)).quotient k) =
        (e.shiftedFiltration (grade q' β') (T p)).projection k
          (mapShiftedCompletion d e T φ h p x) := by
  refine (((d.shiftedFiltration (grade q β) p).submodule
    (T.modulus k + 1)).mkQ_surjective
      ((d.shiftedFiltration (grade q β) p).projection (T.modulus k) x)).elim fun a ha => ?_
  refine ⟨a, ha, ?_⟩
  calc
    _ = mapShiftedQuotient d e T φ h p k (Submodule.Quotient.mk a) :=
      (mapShiftedQuotient_mk d e T φ h p k a).symm
    _ = mapShiftedQuotient d e T φ h p k
        ((d.shiftedFiltration (grade q β) p).projection (T.modulus k) x) :=
      congrArg (mapShiftedQuotient d e T φ h p k) ha
    _ = _ := mapShiftedQuotient_projection d e T φ h p k x

/-- Completed product transport holds for arbitrary compatible bilinear forms. -/
theorem mapShiftedCompletion_mul (p r : Γ)
    (x : d.ShiftedCoefficients (grade q β) p)
    (y : d.ShiftedCoefficients (grade q β) r) :
    cast (congrArg (e.ShiftedCoefficients (grade q' β')) (map_add T.toAddMonoidHom p r))
        (mapShiftedCompletion d e T φ h (p + r)
          (d.shiftedCompletionMul (grade q β) p r x y)) =
      e.shiftedCompletionMul (grade q' β') (T p) (T r)
        (mapShiftedCompletion d e T φ h p x) (mapShiftedCompletion d e T φ h r y) := by
  apply (e.shiftedFiltration (grade q' β') (T p + T r)).completion_ext
  intro k
  let C := cast (congrArg (fun u => (e.shiftedFiltration (grade q' β') u).quotient k)
    (map_add T.toAddMonoidHom p r))
  have h₀ := projection_cast_completed e (map_add T.toAddMonoidHom p r) k
    (mapShiftedCompletion d e T φ h (p + r) (d.shiftedCompletionMul (grade q β) p r x y))
  have h₁ := congrArg C (mapShiftedQuotient_projection d e T φ h (p + r) k
    (d.shiftedCompletionMul (grade q β) p r x y))
  refine (exists_mapShiftedSupport_projection d e T φ h p k x).elim fun a ha => ?_
  refine (exists_mapShiftedSupport_projection d e T φ h r k y).elim fun b hb => ?_
  have h₂ := congrArg (fun z => C (mapShiftedQuotient d e T φ h (p + r) k z))
    (d.projection_shiftedCompletionMul (grade q β) p r (T.modulus k) x y a b ha.1 hb.1)
  have h₃ := congrArg C (mapShiftedQuotient_mk d e T φ h (p + r) k
    (shiftedMul (grade q β) d.monoid p r a b))
  have h₄ := cast_shiftedQuotient_mk e (map_add T.toAddMonoidHom p r) k
    (mapShiftedSupport d e T φ h (p + r) (shiftedMul (grade q β) d.monoid p r a b))
  have h₅ := congrArg
    (fun z : shiftedSubmodule (grade q' β') e.monoid (T p + T r) =>
      (Submodule.Quotient.mk z : (e.shiftedFiltration (grade q' β') (T p + T r)).quotient k))
    (mapShiftedSupport_mul d e T φ h p r a b)
  have h₆ := e.projection_shiftedCompletionMul (grade q' β') (T p) (T r) k
    (mapShiftedCompletion d e T φ h p x) (mapShiftedCompletion d e T φ h r y)
    (mapShiftedSupport d e T φ h p a) (mapShiftedSupport d e T φ h r b) ha.2 hb.2
  exact (h₀).trans <|
    (h₁.symm).trans <|
    (h₂).trans <|
    (h₃).trans <|
    (h₄).trans <|
    (h₅).trans <|
    h₆.symm

end Mei.QuantumMonoidAlgebra
