/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Adapted
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Obstruction
public import Mei.Geometry.ScatteringDiagram.WallSpace.Normal
public import Mei.Geometry.Convex.PolyhedralComplex.Joint

/-!
# Wall spaces of local geometric joint obstructions

Near a relative interior point of an adapted joint, every active wall met by
an admissible path contains the joint. Consequently its normal annihilates the
actual tangent lattice of that joint. At a correction order, the homogeneous
logarithm of a local loop product vanishes in tangent degrees; in a transverse
degree it lies in one wall space. The computed integral normal is nonzero and
its real kernel is the joint direction plus the degree direction. Thus it spans
the required one-dimensional conormal space without choosing a primitive normal.

The results combine `DirectedDiagram.decompose_log_levelPathProduct_loop_mem`,
`DirectedWallSpaces.iSup_wall_eq_wall_of_inf_ker`, the adapted support coverage,
and `FinitePolyhedralComplex.eventually_subset_of_mem_cell`. The geometric attachment is
the local obstruction calculation in Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, proof of Theorem 2.6. No lower-order consistency
is required here; it is used separately to place the loop product in the central
truncation kernel.
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

/-- If every active support meeting a convex region contains a set `J`, all
normals crossed by a path in that region annihilate the lattice tangent vectors
of `J`. It suffices that the path's vertices lie in the region. -/
theorem normal_eq_zero_of_mem_signedCrossingEvents {k : ℕ} {J U : Set V}
    (hU : Convex ℝ U)
    (hlocal : ∀ j : D.active k, (U ∩ (D.wall j).support).Nonempty → J ⊆ (D.wall j).support)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (hp : ∀ z ∈ p.vertices, z.val ∈ U)
    {S : Finset (D.active k × ℤ)}
    (hS : S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal))
    {a : D.active k × ℤ} (ha : a ∈ S) {v : Λ}
    (hv : i v ∈ (affineSpan ℝ J).direction) : (D.wall a.1).normal v = 0 := by
  have hsub := hlocal a.1 (p.inter_nonempty_of_mem_signedCrossingEvents _ hU hp hS ha)
  have hv' := AffineSubspace.direction_le (affineSpan_mono ℝ hsub) hv
  rw [(D.wall a.1).direction_support, LinearMap.mem_ker, h.realCharacter_apply,
    Int.cast_eq_zero] at hv'
  exact hv'

/-- At any actual joint, local correction-order loop logarithms vanish in all
tangent degrees and lie in the computed single wall space in every transverse
degree. The radius works simultaneously for every loop and every degree.
Initial supports are full hyperplanes; all other logarithms have pure birth
strictly below the correction order. -/
theorem exists_pos_joint_loop_obstruction {k : ℕ} {J : Set V}
    (hJ : J ∈ (D.adaptedComplex k).joints) {q : V}
    (hq : q ∈ intrinsicInterior ℝ J) (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ r > 0, ∀ (x : WallComplement (fun j : D.active k => (D.wall j).support))
      (p : AdmissiblePLPath x x), (∀ z ∈ p.vertices, z.val ∈ Metric.ball q r) →
      ∀ n : Γ, d.degree n = k →
        (i (ρ n) ∈ (affineSpan ℝ J).direction →
          (DirectSum.decompose (d.truncatedGrading ℒ k)
            (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0) ∧
        (i (ρ n) ∉ (affineSpan ℝ J).direction → ∃ m : Λ →+ ℤ, m ≠ 0 ∧
          (h.realCharacter m).ker = (affineSpan ℝ J).direction ⊔ ℝ ∙ i (ρ n) ∧
          (DirectSum.decompose (d.truncatedGrading ℒ k)
            (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) ∈
              (H.truncated d k).wall n m) := by
  obtain ⟨r, hr, hlocal⟩ := D.exists_pos_subset_support_of_inter_ball
    (((D.adaptedComplex k).mem_cellsOfCodimension 2 J).mp hJ).1 hq
  refine ⟨r, hr, fun x p hp n hn => ?_⟩
  let W : AddSubmonoid Λ :=
    ((affineSpan ℝ J).direction.toAddSubgroup.comap i).toAddSubmonoid
  have hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0 := by
    intro S hS a ha v hv
    exact D.normal_eq_zero_of_mem_signedCrossingEvents (convex_ball q r) hlocal p hp hS ha hv
  constructor
  · intro htangent
    exact D.decompose_log_levelPathProduct_loop_eq_zero_of_tangent p W hnormal
      initial hfull hpure hn htangent
  · intro htransverse
    obtain ⟨f, g, hfg, hμ, hker⟩ :=
      (D.adaptedComplex k).exists_joint_transverse_normal hJ (ρ n) htransverse
    refine ⟨f (ρ n) • g - g (ρ n) • f, hμ, hker, ?_⟩
    have hW : W = (f.ker ⊓ g.ker).toAddSubmonoid := by
      ext v
      simp only [W, AddSubgroup.mem_toAddSubmonoid, AddSubgroup.mem_comap,
        Submodule.mem_toAddSubgroup, hfg, Submodule.mem_inf, LinearMap.mem_ker,
        h.realCharacter_apply, Int.cast_eq_zero, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
    have hnot : ρ n ∉ f.ker ⊓ g.ker := by
      intro hv
      apply htransverse
      rw [hfg]
      simpa only [Submodule.mem_inf, LinearMap.mem_ker, h.realCharacter_apply,
        Int.cast_eq_zero] using
        And.intro (AddMonoidHom.mem_ker.mp hv.1) (AddMonoidHom.mem_ker.mp hv.2)
    have hmem := D.decompose_log_levelPathProduct_loop_mem p W hnormal initial hfull hpure hn
    rw [hW] at hmem
    simpa only [AddSubgroup.mem_toAddSubmonoid,
      (H.truncated d k).iSup_wall_eq_wall_of_inf_ker f g hnot] using hmem

end Mei.DirectedDiagram
