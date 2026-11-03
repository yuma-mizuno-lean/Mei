/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Limit
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Map.Basic
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Append
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Correction.Splitting
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction.Existence
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Refinement
import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Restriction

/-!
# Relative outgoing completion over a split extension

Let `π : ℒ → ℳ` be a fixed-degree graded Lie homomorphism with a graded Lie section `sec`,
both preserving wall spaces. Consider a diagram `D` whose walls are lifted along `sec`, with
arbitrary supports, or are full affine hyperplanes, and whose image under `π` is consistent
at every order. `exists_relativeOutgoingCompletion` states that `D` has a consistent outgoing
completion all of whose added walls are `exp z` for a homogeneous `z` in the kernel of `π` and
of an actual degree of the wall's supported ray. The image of the completion under `π` is
equivalent to the image of `D`, because the added walls are killed by `π`.

This is the compatible induction of Mandel, *Scattering diagrams, theta functions, and
refined tropical curve counts*, proof of Theorem 2.6, run over an ideal as in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei Mei.Convex

universe u v w

namespace Mei.DirectedDiagram

variable {Γ : Type u} {V : Type v} {Λ R ι : Type*} {L L' : Type w}
  [AddCommGroup Γ] [AddCommGroup Λ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq Γ] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {d : PositiveDegrees Γ} {ℒ : Γ → Submodule R L} {ℳ : Γ → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ ℳ}
  (D : DirectedDiagram (d := d) h H ι)
  (π : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
  (hπ : ∀ n m, ∀ x ∈ H.wall n m, π x ∈ H'.wall n m)

/-- Adjoining a finite list of walls commutes with mapping coefficients. -/
theorem map_listDiagram (s : List (DirectedWall (d := d) h H)) :
    (D.listDiagram s).map π hπ = (D.map π hπ).append
      (ofFinite (fun j : Fin s.length => (s[j]).map π hπ)) := by
  apply DirectedDiagram.ext
  funext j
  cases j <;> simp

variable {D π hπ} [Module.Free ℤ Γ]

/-- Over a split extension `sec` of `π`, if the image `D.map π hπ` is consistent and each wall of
`D` is lifted along `sec` or is a full affine hyperplane, then `D` has a correction step for
logarithms in the kernel of `π`. -/
private theorem correctionStep_ker
    (sec : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ) (hsπ : ∀ x, π (sec x) = x)
    (hs : ∀ n m, ∀ x ∈ H'.wall n m, sec x ∈ H.wall n m)
    (hq : (D.map π hπ).Consistent)
    (hwall : ∀ j, (∃ y, (D.wall j).label = sec.completedMap y) ∨
      ∃ a : ℝ, (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) :
    D.CorrectionStep {z | π z = 0} := by
  classical
  rw [correctionStep_def]
  intro k s hk hw
  let E := D.listDiagram s
  -- The walls added so far are killed by `π`, so they do not change the quotient diagram.
  have hkill (j : Fin s.length) (l : ℕ) :
      CompletedGroup.projection l ((s[j]).map π hπ).label = 1 := by
    obtain ⟨n, -, -, z, -, hz, hlabel, -⟩ :=
      DirectedWall.hasPureBirthLog_def.mp (hw s[j] (List.getElem_mem j.isLt)).2
    rw [DirectedWall.map_label, hlabel, GradedLieHom.completedMap_expToCompletion,
      show π z = 0 from hz, PositiveDegrees.expToCompletion_zero, map_one]
  have hqE : (E.map π hπ).LevelConsistent (k + 1) := by
    rw [map_listDiagram, append_levelConsistent_iff _ _
      (fun j => by simpa only [ofFinite_wall] using hkill j (k + 1))]
    exact (consistent_iff _).mp hq (k + 1)
  obtain ⟨σ, hσ, cross, b, _, t, ht, τ, hτ, _⟩ :=
    E.exists_chamber_trivialization hk (fun _ => 1) (fun _ => zero_lt_one)
  obtain ⟨κ, _, F, hleft, hconsistent, -, hnew⟩ :=
    exists_consistent_kernel_extension (D := E) π sec hsπ hπ hs σ hσ cross hk b t ht τ hτ hqE
      {j | ∃ y, (E.wall j).label = sec.completedMap y}
      (fun j hj => hj)
      (by rintro (j | j) hj
          · left
            have hy : ¬∃ y, (D.wall j).label = sec.completedMap y := fun hy =>
              hj (by simpa only [E, mem_ofPred_eq, listDiagram_wall_inl] using hy)
            simpa only [E, listDiagram_wall_inl] using (hwall j).resolve_left hy
          · right
            obtain ⟨n, -, hd, a, ha, -, hlabel, -⟩ := DirectedWall.hasPureBirthLog_def.mp
              (hw s[j] (List.getElem_mem j.isLt)).2
            exact ⟨n, by omega, a, ha, by simpa only [E, listDiagram_wall_inr] using hlabel⟩)
  refine ⟨κ, inferInstance, F, hleft, hconsistent, fun a => ?_⟩
  obtain ⟨hout, ⟨n, hn, hd, z, hz, hπz, hlabel⟩, hborn, -⟩ := hnew a
  refine ⟨hout, DirectedWall.hasPureBirthLog_def.mpr
    ⟨n, hn, by omega, z, hz, hπz, hlabel, fun l => ?_⟩, ?_⟩
  · simpa only [mem_active] using (hborn l).trans (by omega : k + 1 ≤ l ↔ d.degree n ≤ l)
  · simpa only [mem_active, Nat.not_succ_le_self, iff_false, not_not] using hborn k

/-- A diagram each of whose walls is lifted along `sec`, with arbitrary support, or is a full
affine hyperplane, and whose image under `π` is consistent, has a consistent outgoing completion
by walls `exp z` with `z` in the kernel of `π`. Each added label has a homogeneous logarithm in
an actual degree of its supported ray and is active exactly from that degree onward. The image
of the completion under `π` is equivalent to the image of `D`. No consistency of `D` is
assumed. -/
theorem exists_relativeOutgoingCompletion
    (sec : GradedLieHom (PositiveDegreeMap.id d) ℳ ℒ) (hsπ : ∀ x, π (sec x) = x)
    (hs : ∀ n m, ∀ x ∈ H'.wall n m, sec x ∈ H.wall n m)
    (hq : (D.map π hπ).Consistent)
    (hwall : ∀ j, (∃ y, (D.wall j).label = sec.completedMap y) ∨
      ∃ a : ℝ, (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = a}) :
    ∃ (κ : Type) (_ : Countable κ) (F : DirectedDiagram (d := d) h H (ι ⊕ κ)),
      IsOutgoingCompletion D.wall F ∧
      (∀ j, ∃ n ∈ (F.wall (.inr j)).ray.rayDegrees, ∃ z ∈ ℒ n, π z = 0 ∧
        (F.wall (.inr j)).label = d.expToCompletion ℒ z ∧
          ∀ k : ℕ, Sum.inr j ∈ F.active k ↔ d.degree n ≤ k) ∧
      (F.map π hπ).Equivalent (D.map π hπ) := by
  obtain ⟨κ, hκ, F, hF, hbirth⟩ := D.exists_outgoingCompletion_of_step
    (correctionStep_ker sec hsπ hs hq hwall)
  have hker (j : κ) : ∃ n ∈ (F.wall (.inr j)).ray.rayDegrees, ∃ z ∈ ℒ n, π z = 0 ∧
      (F.wall (.inr j)).label = d.expToCompletion ℒ z ∧
        ∀ k : ℕ, Sum.inr j ∈ F.active k ↔ d.degree n ≤ k := by
    obtain ⟨k, hk⟩ := hbirth j
    obtain ⟨n, hn, -, z, hz, hπz, hlabel, hproj⟩ := DirectedWall.hasPureBirthLog_def.mp hk
    exact ⟨n, hn, z, hz, hπz, hlabel, fun l => by simpa only [mem_active] using hproj l⟩
  refine ⟨κ, hκ, F, hF, hker, (equivalent_iff _ _).mpr fun k => ?_⟩
  -- The added walls have trivial image, so only the retained walls are active.
  have hactive : (F.map π hπ).active k ⊆ range (Sum.inl : ι → ι ⊕ κ) := by
    rintro (j | j) hj
    · exact ⟨j, rfl⟩
    · obtain ⟨n, -, z, -, hπz, hlabel, -⟩ := hker j
      refine ((mem_active _ _ _).mp hj ?_).elim
      rw [map_wall, DirectedWall.map_label, hlabel, GradedLieHom.completedMap_expToCompletion,
        hπz, PositiveDegrees.expToCompletion_zero, map_one]
  exact ((F.map π hπ).levelEquivalent_restrict hactive).trans
    ((Refinement.ofEquiv (Equiv.ofInjective (Sum.inl : ι → ι ⊕ κ) Sum.inl_injective) (fun j => by
      rw [restrict_wall, Equiv.ofInjective_apply, map_wall, map_wall,
        hF.wall_inl])).levelEquivalent k)

end Mei.DirectedDiagram
