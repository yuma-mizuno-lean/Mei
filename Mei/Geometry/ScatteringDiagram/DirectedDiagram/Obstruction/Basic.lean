/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Joint
public import Mei.Geometry.ScatteringDiagram.LinearTerm
public import Mei.Geometry.Convex.Polyhedron.Path.Log

/-!
# Tangent-degree vanishing of directed loop obstructions

Consider a closed admissible path whose crossed wall normals annihilate a fixed
lattice submonoid of tangent vectors. The nonlinear part of its logarithm lies
in the transverse joint submodule. If the initial walls are full hyperplanes and
all other labels are exponentials of homogeneous elements of lower degree, the
linear part in the correction degree cancels. Thus the loop logarithm has zero
component in any degree tangent to the joint, including every zero-direction
degree. In transverse degrees it lies in the sum of wall spaces annihilating the
joint, and in a single wall space when those eligible normals form a cyclic group.

No consistency assumption is needed for these vanishing and membership results.
Lower-order consistency is used separately to make the loop logarithm central.
Only crossed normals are constrained; unrelated walls may occur elsewhere.

The argument combines `DirectedWallSpaces.transverseJointSubmodule`, the
logarithmic transport estimate `LieSubalgebra.log_wallPathProduct_sub_crossingSum_mem`,
and the hyperplane cancellation in `Quiver.Path.wallCrossingSum_loop_eq_zero`.
It follows the linear/nonlinear separation in Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, proof of Theorem 2.6,
and Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
Appendix C.3. No freeness or dimension assumption on the homogeneous pieces is used.
-/

public section

noncomputable section

open Set Mei Mei.Convex WallComplement BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  {k : ℕ} {x y : WallComplement (fun j : D.active k => (D.wall j).support)}

/-- The nonlinear remainder of an actual directed path product is transverse to
any joint direction annihilated by the normals of all crossed walls. -/
theorem log_levelPathProduct_sub_crossingSum_mem (p : AdmissiblePLPath x y)
    (W : AddSubmonoid Λ)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0) :
    log (D.levelPathProduct k p) -
      p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => log (CompletedGroup.projection k (D.wall j).label)) ∈
      (H.truncated d k).transverseJointSubmodule W := by
  rw [D.levelPathProduct_eq_wallPathProduct k p (D.activeLabels_commute k)]
  exact ((H.truncated d k).jointSubalgebra W).log_wallPathProduct_sub_crossingSum_mem
    _ (fun _ ha _ hb => (H.truncated d k).lie_mem_transverseJointSubmodule ha hb)
    _ _ _ p (fun S hS a ha =>
      H.projection_mem_bchSubgroup_jointSubalgebra (D.wall a.1).label_mem
        (hnormal S hS a ha) k)

/-- In the correction degree, the linear crossing sum vanishes: initial full
hyperplanes cancel, and the other homogeneous logarithms have smaller degree. -/
theorem decompose_crossingSum_loop_eq_zero
    (p : AdmissiblePLPath x x) (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a)
    {n : Γ} (hn : d.degree n = k) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => log (CompletedGroup.projection k (D.wall j).label))) n :
      d.truncatedLie ℒ k) = 0 := by
  classical
  let f := ((d.truncatedGrading ℒ k n).subtype.comp
    ((DirectSum.component R Γ (fun m => d.truncatedGrading ℒ k m) n).comp
      (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ k)).toLinearMap)).toAddMonoidHom
  have hzero (j : ι) (hj : j ∉ initial) :
      f (log (CompletedGroup.projection k (D.wall j).label)) = 0 := by
    obtain ⟨m, hm, a, ha, he⟩ := hpure j hj
    have hmn : m ≠ n := by intro he; subst m; omega
    rw [he, PositiveDegrees.projection_expToCompletion, log_exp]
    exact DirectSum.decompose_of_mem_ne (d.truncatedGrading ℒ k)
      ((d.mem_truncatedGrading_iff ℒ).mpr ⟨a, ha, rfl⟩) hmn
  let b (j : D.active k) : ℝ := if hj : j.val ∈ initial then (hfull j hj).choose else 0
  have hc : ∀ j : D.active k,
      f (log (CompletedGroup.projection k (D.wall j).label)) ≠ 0 →
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b j} := by
    intro j hj
    have hi : j.val ∈ initial := by
      by_contra hi
      exact hj (hzero j hi)
    simpa only [b, dite_eq_left hi] using (hfull j hi).choose_spec
  have he := p.map_sum_log_signedCrossingEvents_loop_eq_zero (L := d.truncatedLie ℒ k)
    (fun j : D.active k => h.realCharacter (D.wall j).normal) b
    (fun j => CompletedGroup.projection k (D.wall j).label) f hc
  rw [Quiver.Path.sum_log_signedCrossingEvents p
    (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j : D.active k => (CompletedGroup.projection k (D.wall j).label :
      d.truncatedGroup ℒ k))] at he
  exact he

/-- At the correction order, the loop obstruction vanishes in every degree
whose geometric direction is tangent to the joint. Zero directions are included. -/
theorem decompose_log_levelPathProduct_loop_eq_zero_of_tangent
    (p : AdmissiblePLPath x x) (W : AddSubmonoid Λ)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a)
    {n : Γ} (hn : d.degree n = k) (htangent : ρ n ∈ W) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  have he := (H.truncated d k).decompose_eq_zero_of_mem_transverseJointSubmodule
    (D.log_levelPathProduct_sub_crossingSum_mem p W hnormal) htangent
  simpa [DirectSum.decompose_sub, DFinsupp.sub_apply,
    D.decompose_crossingSum_loop_eq_zero p initial hfull hpure hn] using he

/-- At the correction order, each degree component of a loop obstruction belongs
to the sum of the wall spaces whose normals annihilate the joint. -/
theorem decompose_log_levelPathProduct_loop_mem
    (p : AdmissiblePLPath x x) (W : AddSubmonoid Λ)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a)
    {n : Γ} (hn : d.degree n = k) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) ∈
      ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), (H.truncated d k).wall n m := by
  have he := (H.truncated d k).decompose_mem_of_mem_transverseJointSubmodule W
    (D.log_levelPathProduct_sub_crossingSum_mem p W hnormal) n
  simpa [DirectSum.decompose_sub, DFinsupp.sub_apply,
    D.decompose_crossingSum_loop_eq_zero p initial hfull hpure hn] using he

/-- Zero-direction components of the correction-order loop logarithm vanish.
This requires no joint or local normal condition: every normal annihilates zero. -/
theorem decompose_log_levelPathProduct_loop_eq_zero_of_direction_eq_zero
    (p : AdmissiblePLPath x x) (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a)
    {n : Γ} (hn : d.degree n = k) (hzero : ρ n = 0) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  apply D.decompose_log_levelPathProduct_loop_eq_zero_of_tangent p ⊥
    (fun _ _ _ _ v hv => by simp only [AddSubmonoid.mem_bot.mp hv, map_zero]) initial hfull hpure hn
  simpa using hzero

end Mei.DirectedDiagram
