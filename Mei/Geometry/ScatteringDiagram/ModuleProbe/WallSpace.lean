/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Grading.Lie
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Normal
public import Mei.Geometry.ScatteringDiagram.WallSpace.Action

/-!
# Directed wall spaces for module probes

Base wall spaces occupy charge zero with lifted base normals. Charge-one pieces
carry every nonzero multiple of the probe normal; all other wall spaces vanish.
The mixed bracket has the contracted probe normal. When that contraction vanishes,
the wall-annihilation condition kills the coefficient action, so the zero-normal
law holds without discarding any coefficient piece.

This constructs the wall-space datum on the existing semidirect Lie algebra and
positive grading. It uses `DirectedWallSpaces`, the normal identities in
`ModuleProbe.Normal`, and the wall-annihilation condition of Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§2.1 and §3.3.3 (arXiv:1503.06183v5).
-/

public section
noncomputable section
namespace Mei.ModuleProbe

variable {R M Γ Λ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Γ] [DecidableEq Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  {L : Type*} [LieRing L] [LieAlgebra R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)

open Classical in
/-- Base walls at charge zero and coefficient walls at charge one, with zero
spaces for every other degree or normal. -/
def wallSubmodule (a : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ) :
    Submodule R (ProbeLie d ℳ p ℒ) :=
  if a.2 = (0, 0) then
    if m ∈ Set.range (baseNormal (Λ := Λ)) then
      (H.wall a.1 (m.comp (AddMonoidHom.inl Λ (ℤ × ℤ)))).map
        (baseInclusion d ℳ p ℒ).toLinearMap
    else ⊥
  else if a.2 = (1, 0) ∧ m ≠ 0 ∧
      m ∈ Set.range (fun c : ℤ => c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ)) then
    grading d ℳ p ℒ a
  else ⊥

open Classical in
/-- The complete degree and normal cases defining the probe wall spaces. -/
theorem wallSubmodule_def (a : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ) :
    wallSubmodule d ℳ p ℒ H a m =
      if a.2 = (0, 0) then
        if m ∈ Set.range (baseNormal (Λ := Λ)) then
          (H.wall a.1 (m.comp (AddMonoidHom.inl Λ (ℤ × ℤ)))).map
            (baseInclusion d ℳ p ℒ).toLinearMap
        else ⊥
      else if a.2 = (1, 0) ∧ m ≠ 0 ∧
          m ∈ Set.range (fun c : ℤ => c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ)) then
        grading d ℳ p ℒ a
      else ⊥ := (rfl)

/-- Lifted base normals recover precisely the original wall spaces. -/
@[simp]
theorem wallSubmodule_base (n : Γ) (m : Λ →+ ℤ) :
    wallSubmodule d ℳ p ℒ H (n, 0, 0) (baseNormal m) =
      (H.wall n m).map (baseInclusion d ℳ p ℒ).toLinearMap := by
  classical
  have hm : (baseNormal m).comp (AddMonoidHom.inl Λ (ℤ × ℤ)) = m := by
    ext v
    exact baseNormal_apply _ v 0 0
  simp only [wallSubmodule, ↓reduceIte, Set.mem_range_self, hm]

/-- Every nonzero integral probe normal carries the whole charge-one piece. -/
@[simp]
theorem wallSubmodule_module (q : Γ) (c : ℤ) (hc : c ≠ 0) :
    wallSubmodule d ℳ p ℒ H (q, 1, 0) (c • probeNormal) =
      grading d ℳ p ℒ (q, 1, 0) := by
  classical
  have hn : c • (probeNormal : (Λ × ℤ × ℤ) →+ ℤ) ≠ 0 := by
    intro h
    have := DFunLike.congr_fun h (0, 0, 1)
    simp [hc] at this
  simp [wallSubmodule, hn]

/-- The zero normal carries no probe wall elements. -/
@[simp]
theorem wallSubmodule_zero (a : Γ × ℤ × ℤ) :
    wallSubmodule d ℳ p ℒ H a 0 = ⊥ := by
  classical
  have h0 : (0 : (Λ × ℤ × ℤ) →+ ℤ).comp (AddMonoidHom.inl Λ (ℤ × ℤ)) = 0 := rfl
  simp only [wallSubmodule, h0, H.zero_normal, Submodule.map_bot, ne_eq,
    not_true_eq_false, false_and, and_false, ite_false, ite_self]

private theorem wallSubmodule_le_grading (a : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ) :
    wallSubmodule d ℳ p ℒ H a m ≤ grading d ℳ p ℒ a := by
  classical
  rcases a with ⟨n, c, l⟩
  simp only [wallSubmodule]
  split_ifs with h h' h''
  · have hc : c = 0 := congrArg Prod.fst h
    have hl : l = 0 := congrArg Prod.snd h
    subst c; subst l
    rw [grading_base]
    exact Submodule.map_mono (H.wall_le_piece _ _)
  · exact bot_le
  · exact le_rfl
  · exact bot_le

private theorem mem_wallSubmodule_cases {a : Γ × ℤ × ℤ}
    {m : (Λ × ℤ × ℤ) →+ ℤ} {x : ProbeLie d ℳ p ℒ}
    (hx : x ∈ wallSubmodule d ℳ p ℒ H a m) (hx0 : x ≠ 0) :
    (∃ n m₀ y, a = (n, 0, 0) ∧ m = baseNormal m₀ ∧
      y ∈ H.wall n m₀ ∧ x = baseInclusion d ℳ p ℒ y) ∨
    (∃ (q : Γ) (c : ℤ), a = (q, 1, 0) ∧ c ≠ 0 ∧ m = c • probeNormal ∧
      x ∈ grading d ℳ p ℒ (q, 1, 0)) := by
  classical
  rcases a with ⟨n, c, l⟩
  simp only [wallSubmodule] at hx
  split_ifs at hx with h h' h''
  · obtain ⟨m₀, rfl⟩ := h'
    have hm : (baseNormal m₀).comp (AddMonoidHom.inl Λ (ℤ × ℤ)) = m₀ := by
      ext v
      exact baseNormal_apply _ v 0 0
    rw [hm] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Or.inl ⟨n, m₀, y, by simpa using h, rfl, hy, rfl⟩
  · exact (hx0 (by simpa only [Submodule.mem_bot] using hx)).elim
  · obtain ⟨e, rfl⟩ := h''.2.2
    have he : e ≠ 0 := by intro he; exact h''.2.1 (by simp [he])
    have ha : (n, c, l) = (n, 1, 0) := by simpa using h''.1
    exact Or.inr ⟨n, e, ha, he, rfl, ha ▸ hx⟩
  · exact (hx0 (by simpa only [Submodule.mem_bot] using hx)).elim

/-- A probe wall element is zero, a lifted base wall element, or an element of a
charge-one piece with a nonzero integral probe normal. -/
@[simp]
theorem mem_wallSubmodule_iff (a : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ)
    (x : ProbeLie d ℳ p ℒ) :
    x ∈ wallSubmodule d ℳ p ℒ H a m ↔
      x = 0 ∨
      (∃ n m₀ y, a = (n, 0, 0) ∧ m = baseNormal m₀ ∧
        y ∈ H.wall n m₀ ∧ x = baseInclusion d ℳ p ℒ y) ∨
      (∃ (q : Γ) (c : ℤ), a = (q, 1, 0) ∧ c ≠ 0 ∧ m = c • probeNormal ∧
        x ∈ grading d ℳ p ℒ (q, 1, 0)) := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (mem_wallSubmodule_cases d ℳ p ℒ H hx hx0)
  · rintro (rfl | ⟨n, m₀, y, rfl, rfl, hy, rfl⟩ | ⟨q, c, rfl, hc, rfl, hx⟩)
    · exact Submodule.zero_mem _
    · rw [wallSubmodule_base]
      exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    · rwa [wallSubmodule_module d ℳ p ℒ H q c hc]

private theorem wallSubmodule_rescale (a : Γ × ℤ × ℤ)
    (m : (Λ × ℤ × ℤ) →+ ℤ) (c : ℤ) (hc : c ≠ 0) :
    wallSubmodule d ℳ p ℒ H a (c • m) = wallSubmodule d ℳ p ℒ H a m := by
  classical
  have hs : (c • m).comp (AddMonoidHom.inl Λ (ℤ × ℤ)) =
      c • m.comp (AddMonoidHom.inl Λ (ℤ × ℤ)) := rfl
  have hz : c • m = 0 ↔ m = 0 := by
    constructor
    · intro h
      ext v
      have := DFunLike.congr_fun h v
      simpa [hc] using this
    · rintro rfl; simp
  simp only [wallSubmodule, smul_mem_range_baseNormal _ hc,
    smul_mem_range_smul_probeNormal _ hc, hs, H.rescale _ _ c hc, ne_eq, hz]

section
variable [IsWallAnnihilating H ℳ]

private theorem mixed_bracket_mem {n q : Γ} {m : Λ →+ ℤ} {c : ℤ}
    (hc : c ≠ 0) {x : L} (hx : x ∈ H.wall n m)
    {y : ProbeLie d ℳ p ℒ} (hy : y ∈ grading d ℳ p ℒ (q, 1, 0)) :
    ⁅baseInclusion d ℳ p ℒ x, y⁆ ∈
      wallSubmodule d ℳ p ℒ H (n + q, 1, 0)
        ((m (ρ q) * c) • probeNormal) := by
  classical
  obtain ⟨hyR, hyL⟩ := (mem_grading_module d ℳ p ℒ q y).mp hy
  have he : y = moduleInclusion d ℳ p ℒ y.left := by
    apply LieAlgebra.SemiDirectSum.ext <;> simp [hyR]
  by_cases hm : m (ρ q) = 0
  · have ha : ((moduleCoefficientsEquiv d ℳ p y.left : shiftedSubmodule ℳ d.monoid p) : M)
        ∈ ℳ q := by simpa using (mem_shiftedGrading ℳ d.monoid p).mp hyL
    have hz := IsWallAnnihilating.lie_eq_zero (H := H) (𝒜 := ℳ) hx ha hm
    have hd : actionDerivationHom d ℳ p (ℒ := ℒ) x y.left = 0 := by
      apply (moduleCoefficientsEquiv d ℳ p).injective
      rw [moduleCoefficientsEquiv_actionDerivationHom, map_zero]
      apply Subtype.ext
      exact hz
    rw [he, lie_baseInclusion_moduleInclusion, hd, map_zero]
    exact Submodule.zero_mem _
  · rw [wallSubmodule_module d ℳ p ℒ H _ _ (mul_ne_zero hm hc), he,
      lie_baseInclusion_moduleInclusion, mem_grading_module]
    refine ⟨rfl, ?_⟩
    simpa only [LieAlgebra.SemiDirectSum.inl_eq_mk, add_sub_assoc] using
      actionDerivationHom_mem_shiftedGrading d ℳ p ℒ (H.wall_le_piece n m hx) hyL

/-- The module probe carries directed wall spaces, including the full coefficient
pieces even when their original spatial degree vanishes. -/
def wallSpaces : DirectedWallSpaces (spatialMap ρ) (grading d ℳ p ℒ) where
  wall := wallSubmodule d ℳ p ℒ H
  wall_le_piece := wallSubmodule_le_grading d ℳ p ℒ H
  zero_normal := wallSubmodule_zero d ℳ p ℒ H
  nontangent a m hm := by
    apply eq_bot_iff.mpr
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    rcases mem_wallSubmodule_cases d ℳ p ℒ H hx hx0 with h | h
    · obtain ⟨n, m₀, y, rfl, rfl, hy, rfl⟩ := h
      have ht : m₀ (ρ n) ≠ 0 := by simpa using hm
      rw [H.nontangent n m₀ ht, Submodule.mem_bot] at hy
      simp [hy]
    · obtain ⟨q, c, rfl, hc, rfl, hy⟩ := h
      exact (hm (by simp)).elim
  rescale := wallSubmodule_rescale d ℳ p ℒ H
  bracket_mem := by
    intro a b m m' x y hxW hyW
    by_cases hx0 : x = 0
    · rw [hx0, zero_lie]; exact Submodule.zero_mem _
    by_cases hy0 : y = 0
    · rw [hy0, lie_zero]; exact Submodule.zero_mem _
    rcases mem_wallSubmodule_cases d ℳ p ℒ H hxW hx0 with hxC | hxC <;>
      rcases mem_wallSubmodule_cases d ℳ p ℒ H hyW hy0 with hyC | hyC
    · obtain ⟨n, m₀, x, rfl, rfl, hx, rfl⟩ := hxC
      obtain ⟨q, m₁, y, rfl, rfl, hy, rfl⟩ := hyC
      rw [← LieHom.map_lie]
      simp only [Prod.mk_add_mk, zero_add, wallBracketNormal_base_base, wallSubmodule_base]
      exact Submodule.mem_map.mpr ⟨⁅x, y⁆, H.bracket_mem hx hy, rfl⟩
    · obtain ⟨n, m₀, x, rfl, rfl, hx, rfl⟩ := hxC
      obtain ⟨q, c, rfl, hc, rfl, hy⟩ := hyC
      simpa only [Prod.mk_add_mk, zero_add, wallBracketNormal_base_probe] using
        mixed_bracket_mem d ℳ p ℒ H hc hx hy
    · obtain ⟨q, c, rfl, hc, rfl, hx⟩ := hxC
      obtain ⟨n, m₀, y, rfl, rfl, hy, rfl⟩ := hyC
      rw [← lie_skew]
      have h := (wallSubmodule d ℳ p ℒ H (n + q, 1, 0)
        ((m₀ (ρ q) * c) • probeNormal)).neg_mem
          (mixed_bracket_mem d ℳ p ℒ H hc hy hx)
      have hs := wallSubmodule_rescale d ℳ p ℒ H (q + n, 1, 0)
        ((m₀ (ρ q) * c) • probeNormal) (-1) (by norm_num)
      simp only [neg_one_smul] at hs
      simpa only [Prod.mk_add_mk, add_zero, zero_add, wallBracketNormal_probe_base,
        neg_smul, hs, add_comm] using h
    · obtain ⟨q, c, rfl, hc, rfl, hx⟩ := hxC
      obtain ⟨q', c', rfl, hc', rfl, hy⟩ := hyC
      obtain ⟨hxR, hxL⟩ := (mem_grading_module d ℳ p ℒ q x).mp hx
      obtain ⟨hyR, hyL⟩ := (mem_grading_module d ℳ p ℒ q' y).mp hy
      have he (z : ProbeLie d ℳ p ℒ) (hz : z.right = 0) :
          z = moduleInclusion d ℳ p ℒ z.left := by
        apply LieAlgebra.SemiDirectSum.ext <;> simp [hz]
      rw [he x hxR, he y hyR, lie_moduleInclusion]
      exact Submodule.zero_mem _

end

/-- The bundled wall spaces have the stated degree and normal cases. -/
@[simp]
theorem wallSpaces_wall [IsWallAnnihilating H ℳ]
    (a : Γ × ℤ × ℤ) (m : (Λ × ℤ × ℤ) →+ ℤ) :
    (wallSpaces d ℳ p ℒ H).wall a m = wallSubmodule d ℳ p ℒ H a m := (rfl)

end Mei.ModuleProbe
