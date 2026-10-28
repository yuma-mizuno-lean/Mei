/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Supported
public import Mei.Algebra.Lie.Graded.Subalgebra
public import Mei.Algebra.QuantumMonoidAlgebra.Hom
public import Mei.Algebra.Lie.Graded.RestrictScalars

/-!
# The positive quantum Lie algebra

The commutator of the quantum algebra respects its exponent decomposition.
Selecting the nonzero allowed degrees gives an internally and positively graded
Lie algebra, ready for nilpotent truncation and completed BCH groups. Compatible
coefficient and exponent maps induce graded Lie maps over any common scalar ring,
with the original cutoff modulus.

We use `supportedLieSubalgebra` and `LieSubalgebra.gradedLieAlgebra` to retain the
existing quantum homogeneous pieces. The map construction follows the positive
coefficient restriction in `Mei.QuantumMonoidAlgebra.positiveMap`, using submodule
induction and Mathlib's `AlgHom.toLieHom` and linear-map restriction combinators.
The quantum commutator convention is that
of Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(iii).

As for other associative algebras, consumers working with the ambient quantum
Lie algebra should install `LieRing.ofAssociativeRing` locally.
-/

public section

noncomputable section

namespace Mei.QuantumMonoidAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The quantum exponent decomposition is also a Lie grading for the commutator. -/
instance instGradedBracketGrade : SetLike.GradedBracket (grade q β) (grade q β) where
  bracket_mem := by
    intro n n' x y hx hy
    rw [Ring.lie_def]
    exact (grade q β (n + n')).sub_mem (SetLike.mul_mem_graded hx hy)
      (add_comm n' n ▸ SetLike.mul_mem_graded hy hx)

/-- The quantum exponent decomposition is internal as a Lie grading. -/
instance instGradedLieAlgebraGrade [DecidableEq Γ] : GradedLieAlgebra (grade q β) where
  toGradedBracket := inferInstance

/-- The quantum Lie algebra supported on the nonzero positive degrees. -/
def positiveLieAlgebra (d : PositiveDegrees Γ) : LieSubalgebra R (QuantumMonoidAlgebra q β) :=
  supportedLieSubalgebra (grade q β)
    { carrier := {n | n ∈ d.monoid ∧ n ≠ 0}
      add_mem' := by
        rintro n n' ⟨hn, hne⟩ ⟨hn', hne'⟩
        refine ⟨d.monoid.add_mem hn hn', ?_⟩
        have hp := add_pos (d.degree_pos hn hne) (d.degree_pos hn' hne')
        intro h
        simp [← map_add, h] at hp }

variable (d : PositiveDegrees Γ)

/-- Positive quantum Lie elements are exactly those with no component at zero or
outside the allowed monoid. -/
@[simp]
theorem mem_positiveLieAlgebra_iff [DecidableEq Γ] (x : QuantumMonoidAlgebra q β) :
    x ∈ positiveLieAlgebra q β d ↔ ∀ n, n ∉ d.monoid ∨ n = 0 →
      (DirectSum.decompose (grade q β) x n : QuantumMonoidAlgebra q β) = 0 := by
  simp only [positiveLieAlgebra, mem_supportedLieSubalgebra_iff,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, not_and_or, not_not]

/-- Every allowed nonzero homogeneous piece lies in the positive Lie algebra. -/
theorem grade_le_positiveLieAlgebra {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0) :
    grade q β n ≤ (positiveLieAlgebra q β d).toSubmodule :=
  le_supportedLieSubalgebra (grade q β) (S := _) ⟨hn, hne⟩

/-- The inherited exponent pieces of the positive quantum Lie algebra. -/
def positiveLieGrading (n : Γ) : Submodule R (positiveLieAlgebra q β d) :=
  (grade q β n).comap (positiveLieAlgebra q β d).incl.toLinearMap

/-- The positive grading is the inverse image of the ambient quantum grading. -/
theorem positiveLieGrading_def :
    positiveLieGrading q β d = fun n =>
      (grade q β n).comap (positiveLieAlgebra q β d).incl.toLinearMap := (rfl)

/-- Membership in an inherited piece is ambient homogeneous membership. -/
@[simp]
theorem mem_positiveLieGrading (n : Γ) (x : positiveLieAlgebra q β d) :
    x ∈ positiveLieGrading q β d n ↔ (x : QuantumMonoidAlgebra q β) ∈ grade q β n :=
  Iff.rfl

/-- The restricted quantum commutator adds the Lie and coefficient exponents. -/
instance instGradedBracketPositiveLieGrading :
    SetLike.GradedBracket (positiveLieGrading q β d) (grade q β) where
  bracket_mem _ _ _ _ hx ha := by
    rw [LieSubalgebra.coe_bracket_of_module]
    exact SetLike.GradedBracket.bracket_mem (ℒ := grade q β)
      ((mem_positiveLieGrading q β d _ _).mp hx) ha

/-- Positive quantum Lie elements inherit the internal homogeneous decomposition. -/
instance instGradedLieAlgebraPositiveLieGrading [DecidableEq Γ] :
    GradedLieAlgebra (positiveLieGrading q β d) := by
  rw [positiveLieGrading_def]
  exact (positiveLieAlgebra q β d).gradedLieAlgebra (grade q β)
    (by
      unfold positiveLieAlgebra
      exact supportedLieSubalgebra_isHomogeneous (grade q β) _)

/-- The inherited grading vanishes at zero and outside the allowed degrees. -/
instance instIsPositiveGradingPositiveLieGrading :
    IsPositiveGrading d (positiveLieGrading q β d) where
  eq_bot n hn := by
    classical
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hz := (mem_positiveLieAlgebra_iff q β d x).mp x.property n hn
    rwa [DirectSum.decompose_of_mem_same (grade q β)
      ((mem_positiveLieGrading q β d n x).mp hx)] at hz

section Maps

variable {S Γ' : Type*} [CommRing S] [AddCommGroup Γ']
  {q : Rˣ} {β : LinearMap.BilinForm ℤ Γ} {d : PositiveDegrees Γ}
  {q' : Sˣ} {β' : LinearMap.BilinForm ℤ Γ'} {e : PositiveDegrees Γ'}

/-- A compatible quantum map preserves strictly positive support along its
positive degree map, even when coefficients or exponents have a kernel. -/
theorem map_mem_positiveLieAlgebra (φ : R →+* S) (T : PositiveDegreeMap d e)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))
    {x : QuantumMonoidAlgebra q β} (hx : x ∈ positiveLieAlgebra q β d) :
    map φ T.toAddMonoidHom h x ∈ positiveLieAlgebra q' β' e := by
  -- Positive support is the sum of its actual allowed nonzero homogeneous pieces.
  rw [positiveLieAlgebra, ← LieSubalgebra.mem_toSubmodule,
    supportedLieSubalgebra_toSubmodule] at hx
  refine Submodule.iSup_induction _
    (motive := fun x => map φ T.toAddMonoidHom h x ∈ positiveLieAlgebra q' β' e) hx
    (fun n x hx => ?_) (by simp) (fun x y hx hy => by
      simpa using (positiveLieAlgebra q' β' e).add_mem hx hy)
  exact grade_le_positiveLieAlgebra q' β' e (T.map_mem n.property.1)
    (T.map_ne_zero n.property.1 n.property.2) (map_mem_grade φ T.toAddMonoidHom h hx)

variable {k : Type*} [CommRing k] [Algebra k R] [Algebra k S]

/-- The graded Lie map induced by simultaneous coefficient and exponent transport.
Both gradings retain their original homogeneous carriers after scalar restriction
to the common base ring. The cutoff modulus is exactly that of `T`. -/
def positiveGradedLieHom (φ : R →ₐ[k] S) (T : PositiveDegreeMap d e)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r)) :
    GradedLieHom T (fun n => (positiveLieGrading q β d n).restrictScalars k)
      (fun n => (positiveLieGrading q' β' e n).restrictScalars k) where
  toLieHom :=
    { toLinearMap :=
        ((mapAlgHom φ T.toAddMonoidHom h).toLinearMap.comp
          ((positiveLieAlgebra q β d).incl.toLinearMap.restrictScalars k)).codRestrict
            ((positiveLieAlgebra q' β' e).toSubmodule.restrictScalars k)
            (fun x => by
              simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
                AlgHom.toLinearMap_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
                mapAlgHom_apply, Submodule.restrictScalars_mem, LieSubalgebra.mem_toSubmodule] using
                map_mem_positiveLieAlgebra φ.toRingHom T h x.property)
      map_lie' {x y} := Subtype.ext (by
        simp only [LieSubalgebra.coe_bracket]
        exact (mapAlgHom φ T.toAddMonoidHom h).toLieHom.map_lie
          (x : QuantumMonoidAlgebra q β) (y : QuantumMonoidAlgebra q β)) }
  map_mem {n x} hx := by
    rw [Submodule.restrictScalars_mem, mem_positiveLieGrading]
    -- Expose the composite and codomain restriction while keeping the quantum map opaque.
    change mapAlgHom φ T.toAddMonoidHom h (x : QuantumMonoidAlgebra q β) ∈
      grade q' β' (T n)
    rw [mapAlgHom_apply]
    exact map_mem_grade φ.toRingHom T.toAddMonoidHom h hx

/-- The graded Lie map has the original quantum map as its ambient value. -/
@[simp]
theorem coe_positiveGradedLieHom_apply (φ : R →ₐ[k] S) (T : PositiveDegreeMap d e)
    (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))
    (x : positiveLieAlgebra q β d) :
    (positiveGradedLieHom φ T h x : QuantumMonoidAlgebra q' β') =
      map φ.toRingHom T.toAddMonoidHom h x := mapAlgHom_apply φ T.toAddMonoidHom h x

/-- Identity coefficient and degree maps give the identity positive Lie map. -/
@[simp]
theorem positiveGradedLieHom_id :
    positiveGradedLieHom (AlgHom.id k R) (PositiveDegreeMap.id d)
      (q := q) (β := β) (by intro a b; simp) =
      GradedLieHom.id (fun n => (positiveLieGrading q β d n).restrictScalars k) := by
  apply GradedLieHom.ext
  intro x
  apply Subtype.ext
  have hid : (PositiveDegreeMap.id d).toAddMonoidHom = AddMonoidHom.id Γ :=
    DFunLike.ext _ _ (fun n => PositiveDegreeMap.id_apply n)
  simp [coe_positiveGradedLieHom_apply, hid]

/-- Positive quantum Lie maps compose with both their coefficient maps and their
degree maps, retaining the composite cutoff modulus. -/
theorem positiveGradedLieHom_comp {U Γ'' : Type*} [CommRing U] [Algebra k U]
    [AddCommGroup Γ''] {q'' : Uˣ} {β'' : LinearMap.BilinForm ℤ Γ''}
    {p : PositiveDegrees Γ''} (φ : R →ₐ[k] S) (ψ : S →ₐ[k] U)
    (T : PositiveDegreeMap d e) (V : PositiveDegreeMap e p)
    (h : ∀ a b, Units.map φ.toMonoidHom (q ^ β a b) = q' ^ β' (T a) (T b))
    (h' : ∀ a b, Units.map ψ.toMonoidHom (q' ^ β' a b) = q'' ^ β'' (V a) (V b)) :
    (positiveGradedLieHom ψ V h').comp (positiveGradedLieHom φ T h) =
      positiveGradedLieHom (ψ.comp φ) (V.comp T) (fun a b => by
        rw [PositiveDegreeMap.comp_apply, PositiveDegreeMap.comp_apply, ← h', ← h]
        rfl) := by
  apply GradedLieHom.ext
  intro x
  apply Subtype.ext
  have hcomp : (V.comp T).toAddMonoidHom = V.toAddMonoidHom.comp T.toAddMonoidHom :=
    DFunLike.ext _ _ (fun n => PositiveDegreeMap.comp_apply V T n)
  simpa only [GradedLieHom.comp_apply, coe_positiveGradedLieHom_apply,
    hcomp, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom] using
    map_map φ.toRingHom ψ.toRingHom T.toAddMonoidHom V.toAddMonoidHom h h'
      (x : QuantumMonoidAlgebra q β)

end Maps

end Mei.QuantumMonoidAlgebra
