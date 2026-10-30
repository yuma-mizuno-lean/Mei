/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Algebra.Lie.Filtered.BCH
public import Mei.Algebra.DirectSum.Supported

/-!
# Conservation of normal velocity under wall actions

A wall logarithm changes a homogeneous degree only in directions annihilated by
its normal. It therefore preserves the sum of all coefficient pieces with any
fixed normal evaluation, without assuming that the action kills tangent inputs.
This conservation passes to the finite exponential actions and to every projection
of the completed BCH action. In a homogeneous coefficient quotient, every nonzero
output component has the same normal evaluation as the homogeneous input.

This is the normal-velocity constraint for component propagation in broken lines.
The entire tangent direction need not be preserved, and degrees in the kernel of
the geometric projection remain present. The coefficient module may have arbitrary
homogeneous pieces. No faithfulness or separatedness hypothesis is needed.

The action is homogeneous for the supplied coefficient grading. Extraction of
quotient components uses an inherited direct-sum decomposition of the quotient.
The component-propagation setting is that of Travis Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 and Definition 2.10
(arXiv:1503.06183).
-/

public section

namespace Mei

section NormalDegree

variable {Γ Λ R M : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [Semiring R] [AddCommMonoid M] [Module R M] {ρ : Γ →+ Λ}

/-- Coefficients supported on degrees with a fixed normal evaluation. -/
def normalDegreeSubmodule (ρ : Γ →+ Λ) (𝒜 : Γ → Submodule R M)
    (m : Λ →+ ℤ) (c : ℤ) : Submodule R M :=
  ⨆ p : {p // m (ρ p) = c}, 𝒜 p

/-- The normal-degree submodule is the sum of the pieces on that normal fiber. -/
theorem normalDegreeSubmodule_eq_iSup (𝒜 : Γ → Submodule R M) (m : Λ →+ ℤ) (c : ℤ) :
    normalDegreeSubmodule ρ 𝒜 m c = ⨆ p : {p // m (ρ p) = c}, 𝒜 p := (rfl)

/-- Linear images of normal-degree submodules are the normal-degree submodules
of the image pieces. The linear map need not be injective. -/
@[simp]
theorem map_normalDegreeSubmodule {N : Type*} [AddCommMonoid N] [Module R N]
    (𝒜 : Γ → Submodule R M) (m : Λ →+ ℤ) (c : ℤ) (f : M →ₗ[R] N) :
    (normalDegreeSubmodule ρ 𝒜 m c).map f =
      normalDegreeSubmodule ρ (fun p => (𝒜 p).map f) m c := by
  simp only [normalDegreeSubmodule_eq_iSup, Submodule.map_iSup]

/-- Each homogeneous piece belongs to its own normal-degree submodule. -/
theorem le_normalDegreeSubmodule (𝒜 : Γ → Submodule R M) (m : Λ →+ ℤ) (p : Γ) :
    𝒜 p ≤ normalDegreeSubmodule ρ 𝒜 m (m (ρ p)) :=
  le_iSup (fun q : {q // m (ρ q) = m (ρ p)} => 𝒜 q) ⟨p, rfl⟩

/-- A coefficient has fixed normal degree exactly when all other components vanish. -/
theorem mem_normalDegreeSubmodule_iff (𝒜 : Γ → Submodule R M)
    [DecidableEq Γ] [DirectSum.Decomposition 𝒜] (m : Λ →+ ℤ) (c : ℤ) (a : M) :
    a ∈ normalDegreeSubmodule ρ 𝒜 m c ↔
      ∀ p, m (ρ p) ≠ c → (DirectSum.decompose 𝒜 a p : M) = 0 := by
  rw [normalDegreeSubmodule_eq_iSup]
  exact Mei.DirectSum.mem_iSup_iff_decompose_eq_zero 𝒜 {p | m (ρ p) = c}

end NormalDegree

section Monoid

variable {Γ Λ R L M : Type*} [AddCommMonoid Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}

namespace DirectedWallSpaces

variable (H : DirectedWallSpaces ρ ℒ) (𝒜 : Γ → Submodule R M)
  [SetLike.GradedBracket ℒ 𝒜]

/-- A homogeneous wall logarithm preserves every normal-degree submodule. -/
theorem lie_mem_normalDegreeSubmodule_of_mem_wall {n : Γ} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.wall n m) {c : ℤ} {a : M}
    (ha : a ∈ normalDegreeSubmodule ρ 𝒜 m c) :
    ⁅x, a⁆ ∈ normalDegreeSubmodule ρ 𝒜 m c := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hn := H.normal_apply_eq_zero hx hx0
  rw [normalDegreeSubmodule_eq_iSup] at ha ⊢
  refine Submodule.iSup_induction _ (motive := fun a =>
    ⁅x, a⁆ ∈ ⨆ p : {p // m (ρ p) = c}, 𝒜 p) ha ?_ (by simp) ?_
  · intro p a ha
    exact Submodule.mem_iSup_of_mem
      ⟨n + p, by simp only [map_add, hn, zero_add, p.property]⟩
      (SetLike.GradedBracket.bracket_mem (H.wall_le_piece n m hx) ha)
  · intro a b ha hb
    simpa only [lie_add] using Submodule.add_mem _ ha hb

end DirectedWallSpaces
end Monoid

section Group

variable {Γ Λ R L M : Type*} [AddCommGroup Γ] [AddCommMonoid Λ]
  [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  {d : PositiveDegrees Γ}

namespace DirectedWallSpaces

variable (H : DirectedWallSpaces ρ ℒ) (𝒜 : Γ → Submodule R M)
  [SetLike.GradedBracket ℒ 𝒜]

/-- An entire supported-ray wall logarithm preserves every normal-degree submodule. -/
theorem lie_mem_normalDegreeSubmodule_of_mem_ray {w : SupportedRay d} {m : Λ →+ ℤ}
    {x : L} (hx : x ∈ H.raySubmodule w m) {c : ℤ} {a : M}
    (ha : a ∈ normalDegreeSubmodule ρ 𝒜 m c) :
    ⁅x, a⁆ ∈ normalDegreeSubmodule ρ 𝒜 m c := by
  rw [raySubmodule_def] at hx
  exact Submodule.iSup_induction _
    (motive := fun x => ⁅x, a⁆ ∈ normalDegreeSubmodule ρ 𝒜 m c) hx
    (fun _ _ hx => H.lie_mem_normalDegreeSubmodule_of_mem_wall 𝒜 hx ha)
    (by simp) (fun x y hx hy => by simpa only [add_lie] using Submodule.add_mem _ hx hy)

variable [Algebra ℚ R] [LieModule R L M] [DecidableEq Γ]
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (F : ModuleFiltration R M) [IsFiltrationRaising d ℒ F]

/-- Rational scalars on a finite coefficient quotient come from its scalar ring. -/
local instance quotientRatModuleNormalVelocity (k : ℕ) : Module ℚ (F.quotient k) :=
  Module.compHom (F.quotient k) (algebraMap ℚ R)

/-- Every finite wall exponential preserves normal degree, even if the filtration
is not homogeneous. The submodule in the quotient is the image of the original one. -/
theorem truncatedExpLieAction_mem_normalDegreeSubmodule
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {x : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k) {c : ℤ} {a : F.quotient k}
    (ha : a ∈ (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ) :
    F.truncatedExpLieAction d ℒ k x a ∈
      (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ := by
  rw [ModuleFiltration.truncatedExpLieAction_apply]
  apply Module.End.exp_apply_mem_of_forall_mem _
    ⟨k + 1, F.truncatedLieAction_pow_eq_zero d ℒ k x⟩ _ ?_ ha
  intro b hb
  obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m k x).mp hx
  obtain ⟨b, hb, rfl⟩ := hb
  rw [LieIdeal.mkQ_apply, ModuleFiltration.truncatedLieAction_mk,
    Submodule.mkQ_apply, ModuleFiltration.quotientLieAction_mk]
  exact Submodule.mem_map_of_mem (H.lie_mem_normalDegreeSubmodule_of_mem_ray 𝒜 hy hb)

/-- A finite wall exponential maps a quotient coefficient into the image of a
normal-degree submodule exactly when the original coefficient lies there. -/
theorem truncatedExpLieAction_mem_normalDegreeSubmodule_iff
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {x : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k) (c : ℤ) (a : F.quotient k) :
    F.truncatedExpLieAction d ℒ k x a ∈
      (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ ↔
    a ∈ (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ := by
  constructor
  · intro ha
    simpa only [ModuleFiltration.truncatedExpLieAction_neg,
      LinearEquiv.symm_apply_apply] using
      H.truncatedExpLieAction_mem_normalDegreeSubmodule 𝒜 F
        ((H.truncatedRayLieSubalgebra w m k).neg_mem hx) ha
  · exact H.truncatedExpLieAction_mem_normalDegreeSubmodule 𝒜 F hx

/-- In a graded finite coefficient quotient, every nonzero output component of a
homogeneous input has the same normal evaluation. The inherited quotient grading
is the sum of the images of the original pieces, with no finite-rank requirement. -/
theorem normal_eq_of_decompose_truncatedExpLieAction_ne_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {x : d.truncatedLie ℒ k}
    (hx : x ∈ H.truncatedRayLieSubalgebra w m k)
    [DirectSum.Decomposition (fun p => (𝒜 p).map (F.submodule (k + 1)).mkQ)]
    {p q : Γ} {a : M} (ha : a ∈ 𝒜 p)
    (hq : DirectSum.decompose (fun n => (𝒜 n).map (F.submodule (k + 1)).mkQ)
      (F.truncatedExpLieAction d ℒ k x (Submodule.Quotient.mk a)) q ≠ 0) :
    m (ρ q) = m (ρ p) := by
  by_contra hne
  apply hq
  apply Subtype.ext
  have hmem := H.truncatedExpLieAction_mem_normalDegreeSubmodule 𝒜 F hx
    (Submodule.mem_map_of_mem (le_normalDegreeSubmodule 𝒜 m p ha))
  rw [map_normalDegreeSubmodule] at hmem
  exact (mem_normalDegreeSubmodule_iff
    (fun n => (𝒜 n).map (F.submodule (k + 1)).mkQ) m (m (ρ p)) _).mp hmem q hne

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- A surviving homogeneous component of a finite BCH wall action preserves
normal degree. The coefficient grading is any inherited quotient grading, and
the input may be an arbitrary homogeneous quotient class. -/
theorem normal_eq_of_decompose_truncatedBCHAction_ne_zero
    {w : SupportedRay d} {m : Λ →+ ℤ} {k : ℕ} {g : d.truncatedGroup ℒ k}
    (hg : BCHGroup.log g ∈ H.truncatedRayLieSubalgebra w m k)
    (𝓝 : Γ → Submodule R (F.quotient k)) [DirectSum.Decomposition 𝓝]
    (h𝓝 : ∀ n, 𝓝 n = (𝒜 n).map (F.submodule (k + 1)).mkQ)
    {p q : Γ} {a : F.quotient k} (ha : a ∈ 𝓝 p)
    (hq : DirectSum.decompose 𝓝 (F.truncatedBCHAction d ℒ k g a) q ≠ 0) :
    m (ρ q) = m (ρ p) := by
  obtain ⟨b, hb, rfl⟩ := (Submodule.mem_map.mp (h𝓝 p ▸ ha))
  have he : 𝓝 = fun n => (𝒜 n).map (F.submodule (k + 1)).mkQ := funext h𝓝
  subst 𝓝
  rw [ModuleFiltration.truncatedBCHAction_apply] at hq
  exact H.normal_eq_of_decompose_truncatedExpLieAction_ne_zero 𝒜 F hg hb hq

/-- A completed wall label preserves and reflects normal degree at every finite
projection, for arbitrary completed inputs rather than only original coefficients. -/
theorem projection_completedBCHAction_mem_normalDegreeSubmodule_iff
    {w : SupportedRay d} {m : Λ →+ ℤ} {g : d.completedBCHGroup ℒ}
    (hg : g ∈ H.wallGroup w m) (k : ℕ) (c : ℤ) (a : F.completion) :
    F.projection k (F.completedBCHAction d ℒ g a) ∈
      (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ ↔
    F.projection k a ∈
      (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ := by
  rw [ModuleFiltration.projection_completedBCHAction]
  have he := F.truncatedBCHAction_apply d ℒ k (CompletedGroup.projection k g)
    (F.projection k a)
  exact (Iff.of_eq (congrArg (fun z => z ∈
    (normalDegreeSubmodule ρ 𝒜 m c).map (F.submodule (k + 1)).mkQ) he)).trans
      (H.truncatedExpLieAction_mem_normalDegreeSubmodule_iff 𝒜 F
        ((H.mem_wallGroup w m g).mp hg k) c (F.projection k a))

end DirectedWallSpaces
end Group
end Mei
