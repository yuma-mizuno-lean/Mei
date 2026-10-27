/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Meridian
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Localization
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.Convex.PolyhedralCochain.Transverse

/-!
# Joint obstruction cochains

For a diagram consistent at order `k`, the logarithm of an order-`(k + 1)`
loop product belongs to the successive Lie kernel. Summing these logarithms
on the oriented joints of an adapted complex gives a finite obstruction
cochain. Simultaneously reversing the joint orientations and the loops leaves
this cochain unchanged.

Positive isolating triangular meridians can be chosen so that every homogeneous
component of correction degree is transverse to its geometric degree direction.
Consequently these components belong to the domain of the negative-ray sweep;
zero spatial directions give zero components. The cochain retains its specified
meridians. Independence of those choices and comparison with the coboundary of
crossing defects are separate geometric statements.

The construction combines `DirectedDiagram.exists_positive_isolating_joint_triangle`,
`DirectedDiagram.exists_pos_joint_loop_obstruction`, and
`PolyhedralCochain.transverseSubmodule`. It follows the central obstruction
construction in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei Mei.Convex BCHGroup

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)
  {k : ℕ}

/-- The logarithm of a loop product, valued in the successive Lie kernel.
Only lower-order consistency is required. -/
def loopObstruction (hk : D.LevelConsistent k)
    {x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (γ : AdmissiblePLPath x x) : (d.truncationMap ℒ (Nat.le_succ k)).ker :=
  ⟨log (D.levelPathProduct (k + 1) γ), by
    rw [LieHom.mem_ker, ← LieHom.log_bchGroupMap,
      D.truncation_levelPathProduct (Nat.le_succ k),
      (D.levelConsistent_iff_loops k).mp hk, log_one]⟩

/-- The underlying obstruction coefficient is the actual loop logarithm. -/
@[simp]
theorem coe_loopObstruction (hk : D.LevelConsistent k)
    {x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (γ : AdmissiblePLPath x x) :
    (D.loopObstruction hk γ : d.truncatedLie ℒ (k + 1)) =
      log (D.levelPathProduct (k + 1) γ) := (rfl)

/-- Reversing a loop negates its obstruction. -/
@[simp]
theorem loopObstruction_reverse (hk : D.LevelConsistent k)
    {x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (γ : AdmissiblePLPath x x) :
    D.loopObstruction hk γ.reverse = -D.loopObstruction hk γ := by
  apply Subtype.ext
  simp [D.levelPathProduct_reverse]

/-- An obstruction vanishes precisely when its loop has trivial holonomy. -/
@[simp]
theorem loopObstruction_eq_zero_iff (hk : D.LevelConsistent k)
    {x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (γ : AdmissiblePLPath x x) :
    D.loopObstruction hk γ = 0 ↔ D.levelPathProduct (k + 1) γ = 1 := by
  rw [← Subtype.val_inj, coe_loopObstruction, ZeroMemClass.coe_zero,
    ← log_one (L := d.truncatedLie ℒ (k + 1)), log_injective.eq_iff]

variable (σ : (D.adaptedComplex (k + 1)).joints → OrientedCell h 2)
  (x : (D.adaptedComplex (k + 1)).joints →
    WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
  (γ : ∀ J, AdmissiblePLPath (x J) (x J))

/-- The finite central obstruction cochain for specified oriented joint cells
and meridians. The geometric meridians are supplied by
`exists_jointObstructionCochain`. -/
def jointObstructionCochain (_hσ : ∀ J, (σ J).carrier = (J : Set V))
    (hk : D.LevelConsistent k) :
    PolyhedralCochain R h (d.truncationMap ℒ (Nat.le_succ k)).ker 2 := by
  classical
  let := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
  exact ∑ J, PolyhedralCochain.mk (σ J) (D.loopObstruction hk (γ J))

/-- The obstruction cochain is the signed sum of its joint loop coefficients. -/
theorem jointObstructionCochain_def (hσ : ∀ J, (σ J).carrier = (J : Set V))
    (hk : D.LevelConsistent k) :
    let _ := Fintype.ofFinite (D.adaptedComplex (k + 1)).joints
    D.jointObstructionCochain σ x γ hσ hk =
      ∑ J, PolyhedralCochain.mk (σ J) (D.loopObstruction hk (γ J)) := by
  classical
  rfl

/-- Reversing every joint orientation and its loop preserves the cochain. -/
@[simp]
theorem jointObstructionCochain_reverse (hσ : ∀ J, (σ J).carrier = (J : Set V))
    (hk : D.LevelConsistent k) :
    D.jointObstructionCochain (fun J => (σ J).reverse) x (fun J => (γ J).reverse)
      (fun J => (σ J).reverse_carrier.trans (hσ J)) hk =
      D.jointObstructionCochain σ x γ hσ hk := by
  classical
  simp only [jointObstructionCochain_def, loopObstruction_reverse,
    map_neg, PolyhedralCochain.mk_reverse, neg_neg]

/-- Consistency at the next order makes the entire obstruction cochain zero. -/
theorem jointObstructionCochain_eq_zero (hσ : ∀ J, (σ J).carrier = (J : Set V))
    (hk : D.LevelConsistent k)
    (hk' : D.LevelConsistent (k + 1)) : D.jointObstructionCochain σ x γ hσ hk = 0 := by
  classical
  rw [jointObstructionCochain_def]
  apply Finset.sum_eq_zero
  intro J _
  rw [(D.loopObstruction_eq_zero_iff hk (γ J)).mpr
    ((D.levelConsistent_iff_loops (k + 1)).mp hk' _ _), map_zero]

/-- Choose actual positive isolating meridians on all oriented adapted joints,
arbitrarily small at each joint. For full initial hyperplanes and lower pure
birth logarithms, every correction-degree component of their central cochain
is transverse to its geometric direction, hence can be swept. No consistency
at order `k + 1` is assumed. -/
theorem exists_jointObstructionCochain (hk : D.LevelConsistent k)
    (hσ : ∀ J, (σ J).carrier = (J : Set V))
    (ε : (D.adaptedComplex (k + 1)).joints → ℝ) (hε : ∀ J, 0 < ε J)
    (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k + 1 ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    ∃ (x : (D.adaptedComplex (k + 1)).joints →
        WallComplement (fun j : D.active (k + 1) => (D.wall j).support))
      (γ : ∀ J, AdmissiblePLPath (x J) (x J)),
      (∀ J, ∃ s : Affine.Triangle ℝ V,
        0 < (σ J).orientation.someVector (fun j : Fin 2 => s.points j.succ - s.points 0) ∧
        s.centroid ∈ intrinsicInterior ℝ (J : Set V) ∧
        (γ J).vertices.map WallComplement.val =
          [s.points 0, s.points 1, s.points 2, s.points 0] ∧
        IsCompl (affineSpan ℝ (J : Set V)).direction (vectorSpan ℝ (range s.points)) ∧
        convexHull ℝ (range s.points) ⊆ Metric.ball s.centroid (ε J) ∧
        convexHull ℝ (range s.points) ∩
          ((D.adaptedComplex (k + 1)).codimensionAtLeast 2).support = {s.centroid} ∧
        Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ (J : Set V)) ∧
        (∀ Q ∈ (D.adaptedComplex (k + 1)).joints, Q ≠ (J : Set V) →
          Disjoint (convexHull ℝ (range s.points)) Q) ∧
        ∀ j : D.active (k + 1),
          (convexHull ℝ (range s.points) ∩ (D.wall j).support).Nonempty →
            (J : Set V) ⊆ (D.wall j).support) ∧
      ∀ n : Γ, d.degree n = (k : ℤ) + 1 →
        let π := (DirectSum.component R Γ (fun m => d.truncatedGrading ℒ (k + 1) m) n) ∘ₗ
          (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ (k + 1))).toLinearMap ∘ₗ
          (d.truncationMap ℒ (Nat.le_succ k)).ker.subtype
        PolyhedralCochain.map π (D.jointObstructionCochain σ x γ hσ hk) ∈
          PolyhedralCochain.transverseSubmodule (i (ρ n)) := by
  classical
  have := h.finiteDimensional
  let C := D.adaptedComplex (k + 1)
  let := Fintype.ofFinite C.joints
  have hpoint (J : C.joints) : (intrinsicInterior ℝ (J : Set V)).Nonempty := by
    have hJC := ((C.mem_cellsOfCodimension 2 J).mp J.property).1
    exact Set.Nonempty.intrinsicInterior (C.isConvexPolyhedron hJC).convex (C.nonempty J hJC)
  -- Choose a center and a radius where the local obstruction theorem applies.
  choose q hq using hpoint
  choose r hr hlocal using fun J =>
    D.exists_pos_joint_loop_obstruction J.property (hq J) initial hfull hpure
  have ho (J : C.joints) : (σ J).orientation.IsConormal (affineSpan ℝ (J : Set V)).direction := by
    rw [← hσ J]
    exact (σ J).isConormal
  -- The smaller of the requested radius and the obstruction radius works for all degrees.
  choose s x γ hpos hcenter hvertices hcompl hball hskeleton hfrontier hother hcontains using
    fun J : C.joints => D.exists_positive_isolating_joint_triangle J.property (hq J)
      (σ J).orientation (ho J) (lt_min (hε J) (hr J))
  refine ⟨x, γ, ?_, ?_⟩
  · intro J
    refine ⟨s J, hpos J, ?_, hvertices J, hcompl J, ?_, ?_, hfrontier J, hother J, hcontains J⟩
    · rw [hcenter J]
      exact hq J
    · rw [hcenter J]
      exact (hball J).trans (Metric.ball_subset_ball (min_le_left _ _))
    · rw [hcenter J]
      exact hskeleton J
  -- Tangent coefficients vanish; all remaining generators are transverse.
  · intro n hn
    dsimp only
    rw [jointObstructionCochain_def, map_sum]
    apply Submodule.sum_mem
    intro J _
    rw [PolyhedralCochain.map_mk]
    by_cases ht : i (ρ n) ∈ (affineSpan ℝ (σ J).carrier).direction
    · have hvertices_ball : ∀ z ∈ (γ J).vertices, z.val ∈ Metric.ball (q J) (r J) := by
        intro z hz
        have hm : z.val ∈ [((s J).points 0), (s J).points 1, (s J).points 2, (s J).points 0] := by
          rw [← hvertices J]
          exact List.mem_map.mpr ⟨z, hz, rfl⟩
        have hp : z.val ∈ range (s J).points := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with he | he | he | he
          all_goals rw [he]; exact mem_range_self _
        exact Metric.ball_subset_ball (min_le_right _ _) (hball J (subset_convexHull ℝ _ hp))
      have hz := (hlocal J (x J) (γ J) hvertices_ball n (by exact_mod_cast hn)).1
        (by simpa only [hσ J] using ht)
      have hz' : DirectSum.decompose (d.truncatedGrading ℒ (k + 1))
          (log (D.levelPathProduct (k + 1) (γ J))) n = 0 := Subtype.ext hz
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, coe_loopObstruction,
        LinearEquiv.coe_coe]
      rw [← DirectSum.apply_eq_component (R := R),
        DirectSum.decomposeLinearEquiv_apply, hz', map_zero]
      exact Submodule.zero_mem _
    · exact PolyhedralCochain.mk_mem_transverseSubmodule (i (ρ n)) (σ J) ht _

end Mei.DirectedDiagram
