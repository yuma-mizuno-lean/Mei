/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Action
public import Mei.RingTheory.FilteredAlgebra.Completion.Commute
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Specialization of quantum algebras at `q = 1`

At `q = 1` the factor set `q^(β p r)` is trivial, so for every integral form `β` the quantum
algebra is the additive monoid algebra, as graded algebras (`atOneEquiv`,
`atOneEquiv_mem_grade_iff`). It is therefore commutative: its unnormalized commutator
vanishes (`lie_eq_zero_atOne`), the positive quantum Lie algebra acts trivially on positive
coefficients (`CoefficientAction.lie_eq_zero_atOne`), and every completed label acts as the
identity on completed positive coefficients (`CoefficientAction.completedBCHAction_atOne`).
The form `β` is retained at `q = 1`, so the positive Lie algebra and its grading are still
those of `β`.

A coefficient map `φ : R →+* S` with `φ q = 1` induces the specialization `mapAtOne`,
`a z^p ↦ φ(a) z^p`, onto the quantum algebra at `q = 1`. It preserves degrees, is surjective
when `φ` is, and sends every commutator to zero (`mapAtOne_lie`). For Laurent coefficients
`k[T;T⁻¹]` with quantum parameter `T`, evaluation at `1` gives `laurentAtOne`. By contrast,
no ring homomorphism from `RatFunc k` to a nontrivial semiring sends `X` to `1`
(`Mei.RatFunc.ringHom_X_ne_one`), so the quantum algebra over `k(q)` with `q = X` has no
such specialization.

Only the unnormalized commutator is treated; its quotient by `q - q⁻¹` and the resulting
classical limit are not formalized here.

The specialization is `Mei.QuantumMonoidAlgebra.map` with the identity exponent map, and the
untwisting combines `domCongr` with `zeroFormEquiv`. The quantum multiplication convention is
that of Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(iii), arXiv:1503.06183.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R S Γ : Type*} [CommRing R] [CommRing S] [AddCommGroup Γ]
  (β : LinearMap.BilinForm ℤ Γ)

section AtOne

/-- At `q = 1` the quantum algebra of any integral form is the additive monoid algebra. -/
def atOneEquiv : QuantumMonoidAlgebra (1 : Sˣ) β ≃ₐ[S] AddMonoidAlgebra S Γ :=
  (domCongr (AddEquiv.refl Γ) fun _ _ => by simp only [one_zpow]).trans (zeroFormEquiv 1)

/-- At `q = 1` each quantum monomial is the corresponding monoid algebra monomial. -/
@[simp]
theorem atOneEquiv_monomial (p : Γ) :
    atOneEquiv β (monomial (1 : Sˣ) β p) = AddMonoidAlgebra.single p 1 := by
  simp [atOneEquiv]

/-- The comparison at `q = 1` preserves and reflects the homogeneous pieces. -/
theorem atOneEquiv_mem_grade_iff (p : Γ) (x : QuantumMonoidAlgebra (1 : Sˣ) β) :
    atOneEquiv β x ∈ AddMonoidAlgebra.grade S p ↔ x ∈ grade (1 : Sˣ) β p := by
  rw [atOneEquiv, AlgEquiv.trans_apply, zeroFormEquiv_mem_grade_iff]
  exact domCongr_mem_grade_iff (AddEquiv.refl Γ) _ p x

/-- The quantum algebra at `q = 1` is commutative. -/
theorem commute_atOne (x y : QuantumMonoidAlgebra (1 : Sˣ) β) : Commute x y :=
  (atOneEquiv β).injective (by rw [map_mul, map_mul, mul_comm])

/-- Positive coefficients at `q = 1` commute. -/
theorem commute_positiveSubalgebra_atOne (P : AddSubmonoid Γ)
    (x y : positiveSubalgebra (1 : Sˣ) β P) : Commute x y :=
  Subtype.ext (by
    simpa only [Subalgebra.coe_mul] using
      (commute_atOne β (x : QuantumMonoidAlgebra (1 : Sˣ) β) y).eq)

/-- The unnormalized commutator vanishes at `q = 1`. -/
@[simp]
theorem lie_eq_zero_atOne (x y : QuantumMonoidAlgebra (1 : Sˣ) β) : ⁅x, y⁆ = 0 := by
  rw [Ring.lie_def, (commute_atOne β x y).eq, sub_self]

end AtOne

section Map

variable {q : Rˣ} (φ : R →+* S) (hφ : φ q = 1)

/-- The specialization `q ↦ 1` along a coefficient map `φ` with `φ q = 1`, sending `a z^p`
to `φ(a) z^p` and retaining the form. -/
def mapAtOne : QuantumMonoidAlgebra q β →+* QuantumMonoidAlgebra (1 : Sˣ) β :=
  map φ (AddMonoidHom.id Γ) fun p r => by
    have hq : Units.map φ.toMonoidHom q = 1 := Units.ext (by simpa using hφ)
    simp only [map_zpow, hq, one_zpow]

/-- The specialization sends each quantum monomial to the monomial at `q = 1`. -/
@[simp]
theorem mapAtOne_monomial (p : Γ) :
    mapAtOne β φ hφ (monomial q β p) = monomial (1 : Sˣ) β p :=
  map_monomial φ (AddMonoidHom.id Γ) _ p

/-- The specialization applies `φ` to scalars. -/
@[simp]
theorem mapAtOne_algebraMap (r : R) :
    mapAtOne β φ hφ (algebraMap R _ r) = algebraMap S _ (φ r) :=
  map_algebraMap φ (AddMonoidHom.id Γ) _ r

/-- The specialization is semilinear for `φ`. -/
theorem mapAtOne_smul (r : R) (x : QuantumMonoidAlgebra q β) :
    mapAtOne β φ hφ (r • x) = φ r • mapAtOne β φ hφ x :=
  map_smul φ (AddMonoidHom.id Γ) _ r x

/-- The specialization preserves the homogeneous pieces. -/
theorem mapAtOne_mem_grade {p : Γ} {x : QuantumMonoidAlgebra q β} (hx : x ∈ grade q β p) :
    mapAtOne β φ hφ x ∈ grade (1 : Sˣ) β p :=
  map_mem_grade φ (AddMonoidHom.id Γ) _ hx

/-- The specialization along a surjective coefficient map is surjective. -/
theorem mapAtOne_surjective (hs : Function.Surjective φ) :
    Function.Surjective (mapAtOne β φ hφ) := by
  intro y
  induction (basis (1 : Sˣ) β).mem_span y using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨p, rfl⟩ := h
    exact ⟨monomial q β p, by simp⟩
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨x', rfl⟩ := hy
    exact ⟨x + x', map_add _ x x'⟩
  | smul a _ _ hx =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := hs a
    exact ⟨r • x, mapAtOne_smul β φ hφ r x⟩

/-- The specialization `q ↦ 1` kills every unnormalized commutator. -/
@[simp]
theorem mapAtOne_lie (x y : QuantumMonoidAlgebra q β) : mapAtOne β φ hφ ⁅x, y⁆ = 0 := by
  rw [Ring.lie_def, map_sub, map_mul, map_mul, (commute_atOne β _ _).eq, sub_self]

end Map

section Laurent

open _root_.LaurentPolynomial

variable (k : Type*) [CommRing k]

/-- Evaluation `q ↦ 1` for Laurent coefficients `k[T;T⁻¹]` with quantum parameter `T`. -/
def laurentAtOne :
    QuantumMonoidAlgebra (isUnit_T (R := k) 1).unit β →+* QuantumMonoidAlgebra (1 : kˣ) β :=
  mapAtOne β (eval₂ (RingHom.id k) 1) (by simp)

/-- Laurent evaluation at `1` sends each quantum monomial to the monomial at `q = 1`. -/
@[simp]
theorem laurentAtOne_monomial (p : Γ) :
    laurentAtOne β k (monomial _ β p) = monomial (1 : kˣ) β p := by
  simp [laurentAtOne]

/-- Laurent evaluation at `1` evaluates scalar coefficients at `1`. -/
@[simp]
theorem laurentAtOne_algebraMap (f : LaurentPolynomial k) :
    laurentAtOne β k (algebraMap _ _ f) = algebraMap k _ (eval₂ (RingHom.id k) 1 f) := by
  simp [laurentAtOne]

/-- Laurent evaluation at `1` is surjective. -/
theorem laurentAtOne_surjective : Function.Surjective (laurentAtOne β k) :=
  mapAtOne_surjective β _ _ fun a => ⟨C a, by simp⟩

/-- Laurent evaluation at `1` kills every unnormalized commutator. -/
@[simp]
theorem laurentAtOne_lie (x y : QuantumMonoidAlgebra (isUnit_T (R := k) 1).unit β) :
    laurentAtOne β k ⁅x, y⁆ = 0 :=
  mapAtOne_lie β _ _ x y

end Laurent

section Action

variable (d : PositiveDegrees Γ)

local notation "𝓕" => positiveFiltration (1 : Sˣ) β d.monoid d.degree
  (fun _ hn => d.degree_nonneg hn)
local notation "ℒ" => positiveLieGrading (1 : Sˣ) β d

namespace CoefficientAction

/-- At `q = 1` the positive quantum Lie algebra acts trivially on positive coefficients. -/
theorem lie_eq_zero_atOne (x : positiveLieAlgebra (1 : Sˣ) β d)
    (a : positiveSubalgebra (1 : Sˣ) β d.monoid) : ⁅x, a⁆ = 0 := by
  rw [lie_eq, (commute_positiveSubalgebra_atOne β _ _ _).eq, sub_self]

/-- At `q = 1` every completed label acts as the identity on completed positive
coefficients. -/
theorem completedBCHAction_atOne [Algebra ℚ S] [DecidableEq Γ] (g : d.completedBCHGroup ℒ)
    (a : (𝓕).completion) : (𝓕).completedBCHAction d ℒ g a = a := by
  let E := (𝓕).completedExp (completedCoefficientLog (1 : Sˣ) β d g)
  let E' := (𝓕).completedExp (completedCoefficientLog (1 : Sˣ) β d g⁻¹)
  -- The action fixes `1`, so the two exponential factors are mutually inverse.
  have hone : E * E' = 1 := ((congrArg (· * E') (mul_one E)).symm.trans
    (completedBCHAction_apply (1 : Sˣ) β d g 1).symm).trans (map_one _)
  -- Rewriting directly in the completion is slow, so conclude in an abstract monoid.
  have key : ∀ {M : Type _} [Monoid M] (x y z : M), x * y = y * x → x * z = 1 →
      x * y * z = y := fun x y z h hz => by rw [h, mul_assoc, hz, mul_one]
  exact (completedBCHAction_apply (1 : Sˣ) β d g a).trans (key E a E'
    ((𝓕).commute_completion (commute_positiveSubalgebra_atOne β _) E a).eq hone)

end CoefficientAction

end Action

end Mei.QuantumMonoidAlgebra
