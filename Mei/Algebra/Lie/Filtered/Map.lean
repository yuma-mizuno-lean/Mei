/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.RingTheory.FilteredAlgebra.AlgHom
public import Mei.RingTheory.Ideal.Quotient

/-!
# Naturality of filtered BCH actions

An equivariant coefficient map along a graded Lie homomorphism intertwines the
finite and completed BCH actions. Finite comparison requires only the filtration
bound at the selected source and target orders; completed comparison requires
the compatible bounds at every target order. Coefficient continuity has its own
monotone modulus, independent of the positive degree map's modulus. Comparison at
the maximum of the two cutoffs suffices. Coefficient and Lie maps may have kernels,
and degrees may merge.

The algebra statements transport finite module equivariance across the canonical
ideal-quotient comparison and preserve the existing algebra completion carriers.

The finite statement uses the existing quotient Lie representations and Mathlib's
naturality of nilpotent exponentials. The completion maps are the existing maps of
filtered coefficients and graded BCH groups. This is the action compatibility in
Mandel's shifted coefficient setting, *Scattering diagrams, theta functions, and
refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.ModuleFiltration

section Finite

variable {N N' R L L' M M' : Type*} [AddCommMonoid N] [AddCommMonoid N']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [DecidableEq N] [DecidableEq N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (F : ModuleFiltration R M) (G : ModuleFiltration R M')
  [IsFiltrationRaising d ℒ F] [IsFiltrationRaising e ℒ' G]
  (φ : GradedLieHom T ℒ ℒ') (ψ : M →ₗ[R] M')
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

include hequiv

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']

/-- Equivariant coefficient maps intertwine finite BCH actions along the induced
map of Lie truncations, allowing different source and target orders. -/
theorem mapQ_truncatedBCHAction_of_gradedLieHom {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a)
    (hψ : F.submodule (a + 1) ≤ (G.submodule (k + 1)).comap ψ)
    (g : BCHGroup (d.truncatedLie ℒ a)) (z : F.quotient a) :
    (F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ
        hψ
        (F.truncatedBCHAction d ℒ a g z) =
      G.truncatedBCHAction e ℒ' k ((φ.truncatedMap k h).bchGroupMap g)
        ((F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ
          hψ z) := by
  rw [F.truncatedBCHAction_apply, G.truncatedBCHAction_apply, LieHom.log_bchGroupMap]
  exact F.mapQ_truncatedExpLieAction_of_gradedLieHom G φ ψ hequiv k h hψ (BCHGroup.log g) z

end Finite

section Completed

variable {N N' R M M' : Type*} {L L' : Type u} [AddCommMonoid N] [AddCommMonoid N']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [DecidableEq N] [DecidableEq N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (F : ModuleFiltration R M) (G : ModuleFiltration R M')
  [IsFiltrationRaising d ℒ F] [IsFiltrationRaising e ℒ' G]
  (φ : GradedLieHom T ℒ ℒ') (ψ : M →ₗ[R] M')
  (μ : ℕ → ℕ) (hμ : Monotone μ)
  (hψ : ∀ k, F.submodule (μ k + 1) ≤ (G.submodule (k + 1)).comap ψ)
  (hequiv : ∀ (x : L) (a : M), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

include hequiv

/-- The induced maps on completed coefficients and completed BCH groups intertwine
the actions on arbitrary completed coefficient inputs. The coefficient map may
have a continuity modulus independent of the Lie map's degree modulus. -/
theorem completionMap_completedBCHAction_of_gradedLieHom
    (g : d.completedBCHGroup ℒ) (z : F.completion) :
    F.completionMap G ψ μ hμ hψ (F.completedBCHAction d ℒ g z) =
      G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.completionMap G ψ μ hμ hψ z) := by
  apply G.completion_ext
  intro k
  let a := max (T.modulus k) (μ k)
  have hLie : T.modulus k ≤ a := le_max_left _ _
  have hCoeff : μ k ≤ a := le_max_right _ _
  have hψa : F.submodule (a + 1) ≤ (G.submodule (k + 1)).comap ψ :=
    (F.antitone (Nat.add_le_add_right hCoeff 1)).trans (hψ k)
  let gk : BCHGroup (d.truncatedLie ℒ a) := CompletedGroup.projection a g
  let qψ := (F.submodule (a + 1)).mapQ (G.submodule (k + 1)) ψ hψa
  have hl : G.projection k
      (F.completionMap G ψ μ hμ hψ (F.completedBCHAction d ℒ g z)) =
      qψ (F.truncatedBCHAction d ℒ a gk (F.projection a z)) :=
    (F.projection_completionMap_of_le G ψ μ hμ hψ k a hCoeff _).trans
      (congrArg qψ (F.projection_completedBCHAction d ℒ g z a))
  have hr : G.projection k
      (G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.completionMap G ψ μ hμ hψ z)) =
      G.truncatedBCHAction e ℒ' k ((φ.truncatedMap k hLie).bchGroupMap gk)
        (qψ (F.projection a z)) :=
    (G.projection_completedBCHAction e ℒ' (φ.completedMap g) _ k).trans
      (congrArg₂ (fun g z => G.truncatedBCHAction e ℒ' k g z)
        (φ.projection_completedMap_of_le k hLie g)
        (F.projection_completionMap_of_le G ψ μ hμ hψ k a hCoeff z))
  exact hl.trans ((F.mapQ_truncatedBCHAction_of_gradedLieHom G φ ψ hequiv k hLie hψa
    gk (F.projection a z)).trans hr.symm)

end Completed

end Mei.ModuleFiltration

namespace Mei.AlgFiltration

variable {N N' R A B : Type*} {L L' : Type u}
  [AddCommMonoid N] [AddCommMonoid N'] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [Ring A] [Algebra R A] [Algebra ℚ A] [LieRingModule L A] [LieModule R L A]
  [Ring B] [Algebra R B] [Algebra ℚ B] [LieRingModule L' B] [LieModule R L' B]
  [DecidableEq N] [DecidableEq N']
  {d : PositiveDegrees N} {e : PositiveDegrees N'} {T : PositiveDegreeMap d e}
  {ℒ : N → Submodule R L} {ℒ' : N' → Submodule R L'}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℒ'] [IsPositiveGrading e ℒ']
  (F : AlgFiltration A) (G : AlgFiltration B)
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]
  [IsFiltrationRaising e ℒ' (G.toModuleFiltration R)] [IsDerivationAction L' B]
  (φ : GradedLieHom T ℒ ℒ') (ψ : A →ₐ[R] B)
  (hequiv : ∀ (x : L) (a : A), ψ ⁅x, a⁆ = ⁅φ x, ψ a⁆)

include hequiv

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L'] in
/-- An equivariant algebra map intertwines finite exponential actions at any source
cutoff sufficient for both the Lie map and the coefficient map. -/
theorem quotientMapₐ_truncatedExpLieAction_of_gradedLieHom {a : ℕ} (k : ℕ)
    (h : T.modulus k ≤ a) (hψ : F.ideal (a + 1) ≤ (G.ideal (k + 1)).comap ψ)
    (x : d.truncatedLie ℒ a) (z : A ⧸ F.ideal (a + 1)) :
    Ideal.quotientMapₐ (G.ideal (k + 1)) ψ hψ (F.truncatedExpLieAction d ℒ a x z) =
      G.truncatedExpLieAction e ℒ' k (φ.truncatedMap k h x)
        (Ideal.quotientMapₐ (G.ideal (k + 1)) ψ hψ z) := by
  obtain ⟨z, rfl⟩ := (Submodule.Quotient.restrictScalarsEquiv R
    (F.ideal (a + 1))).surjective z
  simp only [truncatedExpLieAction_restrictScalarsEquiv,
    Ideal.quotientMapₐ_restrictScalarsEquiv]
  exact congrArg (Submodule.Quotient.restrictScalarsEquiv R (G.ideal (k + 1)))
    ((F.toModuleFiltration R).mapQ_truncatedExpLieAction_of_gradedLieHom
      (G.toModuleFiltration R) φ ψ.toLinearMap hequiv k h hψ x z)

/-- Equivariant algebra maps intertwine the completed BCH actions on arbitrary
completed coefficients. The continuity modulus may differ from the Lie modulus. -/
theorem mapCompletionₐ_completedBCHAction_of_gradedLieHom
    (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hψ : ∀ k, F.ideal (μ k + 1) ≤ (G.ideal (k + 1)).comap ψ)
    (g : d.completedBCHGroup ℒ) (z : F.completion) :
    F.mapCompletionₐ G ψ μ hμ hψ (F.completedBCHAction d ℒ g z) =
      G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.mapCompletionₐ G ψ μ hμ hψ z) := by
  apply G.completion_ext
  intro k
  let a := max (T.modulus k) (μ k)
  have hLie : T.modulus k ≤ a := le_max_left _ _
  have hCoeff : μ k ≤ a := le_max_right _ _
  have hψa : F.ideal (a + 1) ≤ (G.ideal (k + 1)).comap ψ :=
    (F.antitone (Nat.add_le_add_right hCoeff 1)).trans (hψ k)
  let qψ := Ideal.quotientMapₐ (G.ideal (k + 1)) ψ hψa
  have hl : G.projection k
      (F.mapCompletionₐ G ψ μ hμ hψ (F.completedBCHAction d ℒ g z)) =
      qψ (F.truncatedExpLieAction d ℒ a (BCHGroup.log (CompletedGroup.projection a g))
        (F.projection a z)) :=
    (F.projection_mapCompletionₐ_of_le G ψ μ hμ hψ k a hCoeff _).trans
      (congrArg qψ (F.projection_completedBCHAction d ℒ g z a))
  have hg : BCHGroup.log (CompletedGroup.projection k (φ.completedMap g)) =
      φ.truncatedMap k hLie (BCHGroup.log (CompletedGroup.projection a g)) :=
    (congrArg BCHGroup.log (φ.projection_completedMap_of_le k hLie g)).trans
      ((φ.truncatedMap k hLie).log_bchGroupMap _)
  have hr : G.projection k
      (G.completedBCHAction e ℒ' (φ.completedMap g)
        (F.mapCompletionₐ G ψ μ hμ hψ z)) =
      G.truncatedExpLieAction e ℒ' k
        (φ.truncatedMap k hLie (BCHGroup.log (CompletedGroup.projection a g)))
        (qψ (F.projection a z)) :=
    (G.projection_completedBCHAction e ℒ' (φ.completedMap g) _ k).trans
      (congrArg₂ (fun x z => G.truncatedExpLieAction e ℒ' k x z) hg
        (F.projection_mapCompletionₐ_of_le G ψ μ hμ hψ k a hCoeff z))
  exact hl.trans ((F.quotientMapₐ_truncatedExpLieAction_of_gradedLieHom G φ ψ hequiv k
    hLie hψa (BCHGroup.log (CompletedGroup.projection a g)) (F.projection a z)).trans hr.symm)

end Mei.AlgFiltration
