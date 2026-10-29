/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Composition

/-!
# Tropical pairings from coordinate isomorphisms

Compatible additive isomorphisms of degrees and tangent vectors give a tropical
pairing: characters transform by precomposition with the inverse tangent map.
The positive degree functions may differ. The cutoff modulus is the finite
maximum supplied by `PositiveDegreeMap.ofInjectiveOn`, rather than an assumed
same-order bound.

On the full character domains the forward and reverse pairings induce inverse
Lie maps and inverse maps of completed BCH groups. In particular, their cutoff
moduli need not be inverse functions. The completion comparison uses
`GradedLieHom.completedMap_eq_of_toLieHom_eq` and the existing composition law.

The inverse-dual coordinate transformation follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.TropicalPairing

open LogarithmicVectorField

section Pairing

variable {R Γ Γ' Λ Λ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommMonoid Λ] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (T : Γ ≃+ Γ') (S : Λ ≃+ Λ')
  (hP : ∀ n, T n ∈ e.monoid ↔ n ∈ d.monoid)
  (hρ : ∀ n, S (ρ n) = ρ' (T n))
  (U : Submodule R (Λ →+ R))

/-- Coordinate isomorphisms give a tropical pairing with the inverse-dual
character map. Different positive degree functions are allowed. -/
def ofEquiv : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U where
  degreeMap := PositiveDegreeMap.ofInjectiveOn T.toAddMonoidHom
    (fun n hn => (hP n).mpr hn) T.injective.injOn
  characterMap :=
    { toFun m := m.val.comp S.symm.toAddMonoidHom
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  eval_eq m n _ := by simp [← hρ n]

/-- The degree map is the canonical finite-cutoff comparison of the coordinate map. -/
@[simp]
theorem ofEquiv_degreeMap :
    (ofEquiv T S hP hρ U).degreeMap =
      PositiveDegreeMap.ofInjectiveOn T.toAddMonoidHom
        (fun n hn => (hP n).mpr hn) T.injective.injOn := (rfl)

/-- Characters transform contravariantly by the inverse tangent isomorphism. -/
@[simp]
theorem ofEquiv_characterMap (m : U) :
    (ofEquiv T S hP hρ U).characterMap m = m.val.comp S.symm.toAddMonoidHom := (rfl)

/-- The canonical cutoff is the least bound on source degrees surviving the
chosen target order. -/
theorem ofEquiv_modulus_le_iff (k l : ℕ) :
    (ofEquiv T S hP hρ U).degreeMap.modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree (T n) ≤ k → d.degree n ≤ l :=
  PositiveDegreeMap.ofInjectiveOn_modulus_le_iff _ _ _ k l

end Pairing

section Inverse

universe u v w

variable {R : Type u} {Γ Γ' : Type v} {Λ Λ' : Type w} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Γ'] [AddCommMonoid Λ] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  (T : Γ ≃+ Γ') (S : Λ ≃+ Λ')
  (hP : ∀ n, T n ∈ e.monoid ↔ n ∈ d.monoid)
  (hρ : ∀ n, S (ρ n) = ρ' (T n))

local notation "U" => (⊤ : Submodule R (Λ →+ R))
local notation "V" => (⊤ : Submodule R (Λ' →+ R))
local notation "p" => ofEquiv T S hP hρ U
local notation "q" => ofEquiv (AddEquiv.symm T) (AddEquiv.symm S)
  (fun n => Iff.trans (Iff.symm (hP (AddEquiv.symm T n)))
    (Eq.to_iff (congrArg (fun x => x ∈ e.monoid) (AddEquiv.apply_symm_apply T n))))
  (fun n => Iff.mpr (AddEquiv.symm_apply_eq S)
    (Eq.trans (Eq.symm (congrArg ρ' (AddEquiv.apply_symm_apply T n)))
      (Eq.symm (hρ (AddEquiv.symm T n))))) V

/-- The reverse coordinate pairing is a left inverse on positive tangent fields.
Only the Lie maps agree with the identity: cutoff moduli remain independent. -/
theorem ofEquiv_restrictGradedLieHom_symm_comp :
    ((q).restrictGradedLieHom (fun _ => Submodule.mem_top)).toLieHom.comp
        ((p).restrictGradedLieHom (fun _ => Submodule.mem_top)).toLieHom =
      LieHom.id := by
  apply LieHom.ext
  intro x
  induction x using tropicalSubalgebra_induction with
  | zero => simp
  | homogeneous n m x hm =>
    apply Subtype.ext
    apply Subtype.ext
    have hx := (p).coe_gradedLieHom_of_homogeneous x m hm
    have hy := (q).coe_gradedLieHom_of_homogeneous
      ((p).restrictGradedLieHom (fun _ => Submodule.mem_top) x)
      ⟨(p).characterMap m, Submodule.mem_top⟩
      (by simpa using hx.symm)
    have hy' : ((q).gradedLieHom
        ((p).restrictGradedLieHom (fun _ => Submodule.mem_top) x)).val =
          single ρ n m.val := by
      convert hy using 1
      congr 1
      · simp
      · ext l
        simp
    simpa only [LieHom.comp_apply, GradedLieHom.coe_toLieHom,
      coe_restrictGradedLieHom, LieHom.id_apply] using hy'.trans hm
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ']

/-- Forward and reverse coordinate maps are inverse after completion, even for
different degree functions and noninverse cutoff moduli. -/
theorem ofEquiv_completedMap_symm_comp :
    ((q).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap.comp
        ((p).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap =
      MonoidHom.id (d.completedBCHGroup (tropicalSubalgebraGrading ρ U d)) := by
  rw [← GradedLieHom.completedMap_comp]
  exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _
    (GradedLieHom.id (tropicalSubalgebraGrading ρ U d))
    (by simpa only [GradedLieHom.toLieHom_comp, GradedLieHom.toLieHom_id] using
      ofEquiv_restrictGradedLieHom_symm_comp (R := R) T S hP hρ)).trans
      GradedLieHom.completedMap_id

/-- Coordinate isomorphisms identify the completed tropical vertex groups.
Both directions are the existing pairing-induced maps. -/
def completedEquivOfEquiv :
    d.completedBCHGroup (tropicalSubalgebraGrading ρ U d) ≃*
      e.completedBCHGroup (tropicalSubalgebraGrading ρ' V e) :=
  ((p).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap.toMulEquiv
    ((q).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap
    (ofEquiv_completedMap_symm_comp T S hP hρ)
    (ofEquiv_completedMap_symm_comp T.symm S.symm _ _)

/-- The forward coordinate equivalence is the pairing's completed map. -/
@[simp]
theorem completedEquivOfEquiv_apply
    (g : d.completedBCHGroup (tropicalSubalgebraGrading ρ U d)) :
    completedEquivOfEquiv T S hP hρ g =
      ((p).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap g := (rfl)

/-- The inverse uses the reverse coordinate pairing and its own cutoff modulus. -/
@[simp]
theorem completedEquivOfEquiv_symm_apply
    (g : e.completedBCHGroup (tropicalSubalgebraGrading ρ' V e)) :
    (completedEquivOfEquiv T S hP hρ).symm g =
      ((q).restrictGradedLieHom (fun _ => Submodule.mem_top)).completedMap g := (rfl)

end Inverse

end Mei.TropicalPairing
