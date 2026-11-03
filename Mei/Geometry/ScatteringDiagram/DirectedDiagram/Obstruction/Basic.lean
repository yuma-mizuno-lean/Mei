/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Consistency
public import Mei.Geometry.ScatteringDiagram.WallSpace.Joint
public import Mei.Geometry.ScatteringDiagram.LinearTerm
public import Mei.Geometry.Convex.Polyhedron.Path.Log
import Mei.Algebra.Lie.BCH.CentralExtension
import Mei.Algebra.Lie.Graded.Truncation.Transition

/-!
# Directed loop obstructions and tangent-degree vanishing

Consider a closed admissible path whose crossed wall normals annihilate a fixed
lattice submonoid of tangent vectors. The nonlinear part of its logarithm lies
in the transverse joint submodule. The linear part is controlled by a
`LoopProjection`: a graded projection preserving wall spaces that fixes loop
logarithms and kills the correction-degree label component of every wall whose
support is not a full hyperplane. After the projection, the linear part in the
correction degree cancels. Thus the loop logarithm has zero component in any
degree tangent to the joint, including every zero-direction degree. In transverse
degrees it lies in the sum of wall spaces annihilating the joint, and in a single
wall space when those eligible normals form a cyclic group.

If the initial walls are full hyperplanes and all other labels are exponentials of
homogeneous elements of lower degree, the identity is a loop projection
(`LoopProjection.ofFullPure`), which gives the full-hyperplane statements. For a
split extension, `id - s ∘ π` is one whose lifted walls may have arbitrary supports
(`Obstruction/Splitting.lean`).

No consistency assumption is needed for these vanishing and membership results.
Under lower-order consistency, `loopObstruction` places the loop logarithm in
the successive Lie kernel and characterizes its reversal and vanishing.
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

/-- Under lower-order consistency, conjugating a loop product at the next order
by any chamber lift leaves it unchanged. -/
theorem inv_mul_levelPathProduct_loop_mul (hk : D.LevelConsistent k)
    {x : WallComplement (fun j : D.active (k + 1) => (D.wall j).support)}
    (γ : AdmissiblePLPath x x) (g : d.truncatedGroup ℒ (k + 1)) :
    g⁻¹ * D.levelPathProduct (k + 1) γ * g = D.levelPathProduct (k + 1) γ := by
  have hm : D.levelPathProduct (k + 1) γ ∈
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap.ker := by
    rw [MonoidHom.mem_ker, D.truncation_levelPathProduct (Nat.le_succ k)]
    exact (D.levelConsistent_iff_loops k).mp hk _ _
  have hc := Subgroup.mem_center_iff.mp
    ((d.truncationMap ℒ (Nat.le_succ k)).ker_bchGroupMap_le_center
      (d.ker_truncationMap_succ_le_center ℒ k) hm) g⁻¹
  rw [hc, mul_assoc, inv_mul_cancel, mul_one]

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

variable {x y : WallComplement (fun j : D.active k => (D.wall j).support)}

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

/-- A graded linear projection of the order-`k` Lie algebra adapted to the loops of a
diagram. It fixes every loop logarithm, preserves the wall spaces, and kills the
correction-degree component of every label whose support is not a full hyperplane.

For full initial hyperplanes and lower pure walls the identity is such a projection
(`LoopProjection.ofFullPure`). For a split extension `h = g ⋉ I` with a consistent
quotient diagram, `id - s ∘ π` is one; it kills the lifted quotient labels, so their
supports are unrestricted. -/
structure LoopProjection (k : ℕ) where
  /-- The projection of the order-`k` Lie algebra. -/
  toLinearMap : d.truncatedLie ℒ k →ₗ[R] d.truncatedLie ℒ k
  /-- The projection commutes with every homogeneous component. -/
  decompose_map : ∀ (x : d.truncatedLie ℒ k) (n : Γ),
    (DirectSum.decompose (d.truncatedGrading ℒ k) (toLinearMap x) n : d.truncatedLie ℒ k) =
      toLinearMap (DirectSum.decompose (d.truncatedGrading ℒ k) x n)
  /-- The projection preserves every truncated wall space. -/
  map_wall : ∀ (n : Γ) (m : Λ →+ ℤ) (x : d.truncatedLie ℒ k),
    x ∈ (H.truncated d k).wall n m → toLinearMap x ∈ (H.truncated d k).wall n m
  /-- The projection fixes the logarithm of every loop product. -/
  map_log_loop : ∀ {x : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x x),
    toLinearMap (log (D.levelPathProduct k p)) = log (D.levelPathProduct k p)
  /-- The map is a projection. -/
  isIdempotentElem : IsIdempotentElem toLinearMap
  /-- A wall whose projected correction-degree label component is nonzero has a full
  hyperplane support. -/
  full_of_ne_zero : ∀ (j : D.active k) {n : Γ}, d.degree n = k →
    toLinearMap (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (CompletedGroup.projection k (D.wall j).label)) n) ≠ 0 →
    ∃ b : ℝ, (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b}

namespace LoopProjection

variable {D} (P : D.LoopProjection k)

/-- The projection fixes every homogeneous component of a loop logarithm. -/
theorem map_decompose_log_loop (p : AdmissiblePLPath x x) (n : Γ) :
    P.toLinearMap (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n) =
      (DirectSum.decompose (d.truncatedGrading ℒ k) (log (D.levelPathProduct k p)) n :
        d.truncatedLie ℒ k) := by
  rw [← P.decompose_map, P.map_log_loop p]

/-- In the correction degree, the projected linear crossing sum of a loop vanishes. -/
theorem map_decompose_crossingSum_loop_eq_zero (p : AdmissiblePLPath x x)
    {n : Γ} (hn : d.degree n = k) :
    P.toLinearMap (DirectSum.decompose (d.truncatedGrading ℒ k)
      (p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => log (CompletedGroup.projection k (D.wall j).label))) n) = 0 := by
  classical
  let f := (P.toLinearMap.comp ((d.truncatedGrading ℒ k n).subtype.comp
    ((DirectSum.component R Γ (fun m => d.truncatedGrading ℒ k m) n).comp
      (DirectSum.decomposeLinearEquiv (d.truncatedGrading ℒ k)).toLinearMap))).toAddMonoidHom
  let b (j : D.active k) : ℝ := if hj : ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b} then hj.choose else 0
  have hc : ∀ j : D.active k,
      f (log (CompletedGroup.projection k (D.wall j).label)) ≠ 0 →
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b j} := by
    intro j hj
    have hfull := P.full_of_ne_zero j hn hj
    simpa only [b, dite_eq_left hfull] using hfull.choose_spec
  have he := p.map_sum_log_signedCrossingEvents_loop_eq_zero (L := d.truncatedLie ℒ k)
    (fun j : D.active k => h.realCharacter (D.wall j).normal) b
    (fun j => CompletedGroup.projection k (D.wall j).label) f hc
  rw [Quiver.Path.sum_log_signedCrossingEvents p
    (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j : D.active k => (CompletedGroup.projection k (D.wall j).label :
      d.truncatedGroup ℒ k))] at he
  exact he

/-- In the correction degree, the loop logarithm equals the projection of its
nonlinear remainder. -/
theorem decompose_log_levelPathProduct_loop_eq (p : AdmissiblePLPath x x)
    {n : Γ} (hn : d.degree n = k) :
    (DirectSum.decompose (d.truncatedGrading ℒ k) (log (D.levelPathProduct k p)) n :
      d.truncatedLie ℒ k) =
      P.toLinearMap (DirectSum.decompose (d.truncatedGrading ℒ k)
        (log (D.levelPathProduct k p) -
          p.wallCrossingSum (fun j : D.active k => h.realCharacter (D.wall j).normal)
            (fun j => log (CompletedGroup.projection k (D.wall j).label))) n) := by
  rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, map_sub,
    P.map_decompose_crossingSum_loop_eq_zero p hn, sub_zero, ← P.decompose_map,
    P.map_log_loop p]

include P in
/-- At the correction order, the loop obstruction vanishes in every degree whose
geometric direction is tangent to the joint. Zero directions are included. -/
theorem decompose_log_levelPathProduct_loop_eq_zero_of_tangent
    (p : AdmissiblePLPath x x) (W : AddSubmonoid Λ)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    {n : Γ} (hn : d.degree n = k) (htangent : ρ n ∈ W) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  have he := (H.truncated d k).decompose_eq_zero_of_mem_transverseJointSubmodule
    (D.log_levelPathProduct_sub_crossingSum_mem p W hnormal) htangent
  rw [P.decompose_log_levelPathProduct_loop_eq p hn]
  simpa using congrArg P.toLinearMap he

include P in
/-- At the correction order, each degree component of a loop obstruction belongs to
the sum of the wall spaces whose normals annihilate the joint. -/
theorem decompose_log_levelPathProduct_loop_mem
    (p : AdmissiblePLPath x x) (W : AddSubmonoid Λ)
    (hnormal : ∀ S ∈ p.signedCrossingEvents
      (fun j : D.active k => h.realCharacter (D.wall j).normal),
      ∀ a ∈ S, ∀ v ∈ W, (D.wall a.1).normal v = 0)
    {n : Γ} (hn : d.degree n = k) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) ∈
      ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), (H.truncated d k).wall n m := by
  have he := (H.truncated d k).decompose_mem_of_mem_transverseJointSubmodule W
    (D.log_levelPathProduct_sub_crossingSum_mem p W hnormal) n
  have hle : (⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), (H.truncated d k).wall n m).map
      P.toLinearMap ≤ ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), (H.truncated d k).wall n m := by
    simp only [Submodule.map_iSup]
    exact iSup₂_mono fun m _ =>
      Submodule.map_le_iff_le_comap.mpr fun x hx => P.map_wall n m x hx
  rw [P.decompose_log_levelPathProduct_loop_eq p hn]
  exact hle (Submodule.mem_map_of_mem he)

include P in
/-- Zero-direction components of the correction-order loop logarithm vanish. This
requires no joint or local normal condition: every normal annihilates zero. -/
theorem decompose_log_levelPathProduct_loop_eq_zero_of_direction_eq_zero
    (p : AdmissiblePLPath x x) {n : Γ} (hn : d.degree n = k) (hzero : ρ n = 0) :
    (DirectSum.decompose (d.truncatedGrading ℒ k)
      (log (D.levelPathProduct k p)) n : d.truncatedLie ℒ k) = 0 := by
  apply P.decompose_log_levelPathProduct_loop_eq_zero_of_tangent p ⊥
    (fun _ _ _ _ v hv => by simp only [AddSubmonoid.mem_bot.mp hv, map_zero]) hn
  simpa using hzero

variable (D) in
/-- Full initial hyperplanes and walls whose labels are exponentials of homogeneous
elements of lower degree make the identity a loop projection. -/
def ofFullPure (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    D.LoopProjection k where
  toLinearMap := LinearMap.id
  decompose_map _ _ := rfl
  map_wall _ _ _ hx := hx
  map_log_loop _ := rfl
  isIdempotentElem := IsIdempotentElem.one
  full_of_ne_zero j n hn hne := by
    by_cases hj : j.val ∈ initial
    · exact hfull j hj
    · obtain ⟨m, hm, a, ha, he⟩ := hpure j hj
      have hmn : m ≠ n := by intro he; subst m; omega
      refine (hne ?_).elim
      rw [he, PositiveDegrees.projection_expToCompletion, log_exp, LinearMap.id_apply]
      exact DirectSum.decompose_of_mem_ne (d.truncatedGrading ℒ k)
        ((d.mem_truncatedGrading_iff ℒ).mpr ⟨a, ha, rfl⟩) hmn

@[simp]
theorem ofFullPure_toLinearMap (initial : Set ι)
    (hfull : ∀ j ∈ initial, ∃ b : ℝ,
      (D.wall j).support = {v | h.realCharacter (D.wall j).normal v = b})
    (hpure : ∀ j ∉ initial, ∃ m : Γ, d.degree m < k ∧
      ∃ a ∈ ℒ m, (D.wall j).label = d.expToCompletion ℒ a) :
    (ofFullPure D initial hfull hpure).toLinearMap = LinearMap.id := (rfl)

end LoopProjection

end Mei.DirectedDiagram
