/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Basic
public import Mei.Algebra.Lie.Graded.Ray

/-!
# Label groups of KS walls are supported-ray groups

Let `σ` be a subset of a KS space whose vector span is the kernel of the normal of a nonzero
allowed degree `n`, for instance a wall of a finite KS complex cooriented by `n`. In a free
degree lattice every nonzero allowed degree vanishing on `σ` lies on the supported ray of `n`:
nested normal kernels force equal positive multiples, read off at the degree point. Hence the
Lie algebra `g(σ) = ⨁_{σ ⊆ m⊥} g_m` orthogonal to `σ` is the ray Lie algebra of that supported
ray, for every positive grading.

For a wall `P` of a `KSComplex`, its label group, the BCH subgroup of `g(P)` at the retained
order, is therefore the finite supported-ray group of its coorienting degree, and every wall
label lies in it. When rays are abelian (`IsAbelianRays`), any two elements of the label group
of one wall commute. This identifies the labels of KS walls with labels in supported-ray groups,
and lets finitely many labels on one wall be multiplied without choosing an order, as in the
abelian-ray presentations of scattering diagrams of Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), and Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §§2–3 (arXiv:1603.00416v4).

The commensurability argument uses `LinearMap.exists_pos_smul_eq_of_ker_le_ker` and
`KSSpace.normal_eq_zero_iff`; ray uniqueness is `SupportedRay.eq_of_mem_rayDegrees`, and
commutation is `BCHGroup.commute_of_lie_log_eq_zero`.
-/

public section

namespace Mei

namespace KSSpace

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (s : KSSpace h)
  {d : PositiveDegrees N}

/-- Degrees on two supported rays whose normals have nested kernels lie on the same ray. -/
theorem eq_of_mem_rayDegrees_of_ker_normal_le [Module.Free ℤ N] {v w : SupportedRay d}
    {n m : N} (hn : n ∈ v.rayDegrees) (hm : m ∈ w.rayDegrees)
    (hker : LinearMap.ker (s.normal n) ≤ LinearMap.ker (s.normal m)) : v = w := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  obtain ⟨a, b, ha, hb, hab⟩ := s.exists_nsmul_eq_nsmul_of_ker_normal_le d
    (v.rayDegrees_subset hn) (SupportedRay.ne_zero_of_mem_rayDegrees hn)
    (w.rayDegrees_subset hm) (SupportedRay.ne_zero_of_mem_rayDegrees hm) hker
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact SupportedRay.eq_of_mem_rayDegrees (SupportedRay.succ_nsmul_mem_rayDegrees hn b)
    (hab ▸ SupportedRay.succ_nsmul_mem_rayDegrees hm a)

/-- Every degree on a supported ray vanishes on a set on which one degree of the ray vanishes. -/
theorem evaluation_eq_zero_of_mem_rayDegrees {σ : Set V} {w : SupportedRay d} {n m : N}
    (hn : n ∈ w.rayDegrees) (hσ : ∀ θ ∈ σ, s.evaluation θ n = 0) (hm : m ∈ w.rayDegrees) :
    ∀ θ ∈ σ, s.evaluation θ m = 0 := by
  obtain ⟨-, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  obtain ⟨-, b, -, rfl⟩ := SupportedRay.mem_rayDegrees.mp hm
  intro θ hθ
  have hg := hσ θ hθ
  rw [map_zsmul, zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at hg
  rw [map_zsmul, hg.resolve_left ha.ne', smul_zero]

/-- The normal of a degree on a supported ray is a positive multiple of the normal of the
primitive generator. -/
theorem exists_normal_eq_smul_of_mem_rayDegrees {w : SupportedRay d} {n : N}
    (hn : n ∈ w.rayDegrees) : ∃ a : ℝ, 0 < a ∧ s.normal n = a • s.normal w.generator := by
  obtain ⟨-, a, ha, rfl⟩ := SupportedRay.mem_rayDegrees.mp hn
  refine ⟨a, Int.cast_pos.mpr ha, LinearMap.ext fun θ => ?_⟩
  simp [zsmul_eq_mul]

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : N → Submodule R L) [SetLike.GradedBracket ℒ ℒ]

/-- The Lie algebra of a supported ray is orthogonal to every set on which one of its degrees
vanishes. -/
theorem rayLieSubalgebra_le_orthogonalLieSubalgebra {σ : Set V} {w : SupportedRay d} {n : N}
    (hn : n ∈ w.rayDegrees) (hσ : ∀ θ ∈ σ, s.evaluation θ n = 0) :
    rayLieSubalgebra ℒ w ≤ orthogonalLieSubalgebra ℒ (s.evaluation '' σ) := by
  refine (rayLieSubalgebra_le_iff ℒ w _).mpr fun m hm => le_orthogonalLieSubalgebra ℒ ?_
  rintro _ ⟨θ, hθ, rfl⟩
  exact s.evaluation_eq_zero_of_mem_rayDegrees hn hσ hm θ hθ

/-- If the vector span of `σ` is the kernel of the normal of a degree on a supported ray, the
Lie algebra orthogonal to `σ` is the Lie algebra of that ray. -/
theorem orthogonalLieSubalgebra_eq_rayLieSubalgebra [Module.Free ℤ N] [IsPositiveGrading d ℒ]
    {σ : Set V} {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees)
    (hσ : ∀ θ ∈ σ, s.evaluation θ n = 0)
    (hker : LinearMap.ker (s.normal n) ≤ vectorSpan ℝ σ) :
    orthogonalLieSubalgebra ℒ (s.evaluation '' σ) = rayLieSubalgebra ℒ w := by
  refine le_antisymm ?_ (s.rayLieSubalgebra_le_orthogonalLieSubalgebra ℒ hn hσ)
  rw [orthogonalLieSubalgebra_def, supportedLieSubalgebra_le_iff]
  intro m hm
  simp only [AddSubsemigroup.mem_iInf, AddSubmonoid.mem_toSubsemigroup, AddMonoidHom.mem_mker,
    Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hm
  by_cases hm0 : m ∉ d.monoid ∨ m = 0
  · rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) m hm0]
    exact bot_le
  simp only [not_or, not_not] at hm0
  obtain ⟨v, hv⟩ := d.exists_supportedRay hm0.1 hm0.2
  -- The normal of `m` vanishes on `σ`, hence on its vector span.
  have hspan : vectorSpan ℝ σ ≤ LinearMap.ker (s.normal m) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨θ, hθ, θ', hθ', rfl⟩
    simp [hm θ hθ, hm θ' hθ']
  obtain rfl := s.eq_of_mem_rayDegrees_of_ker_normal_le hn hv (hker.trans hspan)
  exact le_rayLieSubalgebra ℒ hv

/-- With abelian rays, elements of the BCH group of the Lie algebra orthogonal to `σ` commute
when the vector span of `σ` is the kernel of the normal of a nonzero allowed degree. -/
theorem commute_of_mem_bchSubgroup [Module.Free ℤ N] [IsPositiveGrading d ℒ] [IsAbelianRays d ℒ]
    [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieRing.IsNilpotent L]
    {σ : Set V} {n : N} (hn : n ∈ d.monoid) (hn0 : n ≠ 0)
    (hσ : ∀ θ ∈ σ, s.evaluation θ n = 0)
    (hker : LinearMap.ker (s.normal n) ≤ vectorSpan ℝ σ) {g g' : BCHGroup L}
    (hg : g ∈ (orthogonalLieSubalgebra ℒ (s.evaluation '' σ)).bchSubgroup)
    (hg' : g' ∈ (orthogonalLieSubalgebra ℒ (s.evaluation '' σ)).bchSubgroup) :
    Commute g g' := by
  obtain ⟨w, hw⟩ := d.exists_supportedRay hn hn0
  rw [s.orthogonalLieSubalgebra_eq_rayLieSubalgebra ℒ hw hσ hker,
    LieSubalgebra.mem_bchSubgroup] at hg hg'
  exact BCHGroup.commute_of_lie_log_eq_zero g g' (lie_eq_zero_of_mem_rayLieSubalgebra ℒ hg hg')

end KSSpace

namespace KSComplex

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : FinitePolyhedralComplex h} {k : ℕ} (D : KSComplex s d ℒ C k)

/-- The supported primitive ray of the coorienting degree of a KS wall. -/
noncomputable def wallRay [Module.Free ℤ N] (P : C.walls) : SupportedRay d :=
  (d.exists_supportedRay (D.degree_mem P) (D.degree_ne_zero P)).choose

/-- The original coorienting degree is an actual degree of its supported ray. -/
theorem degree_mem_wallRay [Module.Free ℤ N] (P : C.walls) :
    D.degree P ∈ (D.wallRay P).rayDegrees :=
  (d.exists_supportedRay (D.degree_mem P) (D.degree_ne_zero P)).choose_spec

/-- The Lie algebra orthogonal to a wall of a KS complex is the Lie algebra of the supported ray
of its coorienting degree, for every positive grading. -/
theorem orthogonalLieSubalgebra_eq_rayLieSubalgebra [Module.Free ℤ N]
    {R' L' : Type*} [CommRing R'] [LieRing L'] [LieAlgebra R' L']
    (ℳ : N → Submodule R' L') [SetLike.GradedBracket ℳ ℳ] [IsPositiveGrading d ℳ]
    (P : C.walls) {w : SupportedRay d} (hw : D.degree P ∈ w.rayDegrees) :
    orthogonalLieSubalgebra ℳ (s.evaluation '' (P : Set V)) = rayLieSubalgebra ℳ w :=
  s.orthogonalLieSubalgebra_eq_rayLieSubalgebra ℳ hw (D.evaluation_eq_zero P)
    (by rw [D.ker_normal P, direction_affineSpan])

/-- The label group of a wall is the finite supported-ray group of its coorienting degree. -/
theorem bchSubgroup_orthogonalLieSubalgebra_eq [Module.Free ℤ N] (P : C.walls)
    {w : SupportedRay d} (hw : D.degree P ∈ w.rayDegrees) :
    (orthogonalLieSubalgebra (d.truncatedGrading ℒ k) (s.evaluation '' (P : Set V))).bchSubgroup =
      (rayLieSubalgebra (d.truncatedGrading ℒ k) w).bchSubgroup := by
  rw [D.orthogonalLieSubalgebra_eq_rayLieSubalgebra _ P hw]

/-- Every wall label lies in the finite supported-ray group of its coorienting degree. -/
theorem label_mem_bchSubgroup_rayLieSubalgebra [Module.Free ℤ N] (P : C.walls)
    {w : SupportedRay d} (hw : D.degree P ∈ w.rayDegrees) :
    D.label P ∈ (rayLieSubalgebra (d.truncatedGrading ℒ k) w).bchSubgroup :=
  D.bchSubgroup_orthogonalLieSubalgebra_eq P hw ▸ D.label_mem P

/-- With abelian rays, any two elements of the label group of a wall commute. -/
theorem commute_of_mem_bchSubgroup [Module.Free ℤ N] [IsAbelianRays d ℒ]
    (D : KSComplex s d ℒ C k) (P : C.walls) {g g' : d.truncatedGroup ℒ k}
    (hg : g ∈ (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
      (s.evaluation '' (P : Set V))).bchSubgroup)
    (hg' : g' ∈ (orthogonalLieSubalgebra (d.truncatedGrading ℒ k)
      (s.evaluation '' (P : Set V))).bchSubgroup) :
    Commute g g' :=
  s.commute_of_mem_bchSubgroup (d.truncatedGrading ℒ k) (D.degree_mem P) (D.degree_ne_zero P)
    (D.evaluation_eq_zero P) (by rw [D.ker_normal P, direction_affineSpan]) hg hg'

/-- With abelian rays, the labels of two KS complexes on a common wall commute, so coincident
walls can be merged without choosing an order. -/
theorem commute_label [Module.Free ℤ N] [IsAbelianRays d ℒ]
    (D E : KSComplex s d ℒ C k) (P : C.walls) : Commute (D.label P) (E.label P) :=
  D.commute_of_mem_bchSubgroup P (D.label_mem P) (E.label_mem P)

/-- With abelian rays, wall labels of a KS complex commute when their walls have the same
affine span. -/
theorem commute_label_of_affineSpan_eq [Module.Free ℤ N] [IsAbelianRays d ℒ]
    (P P' : C.walls) (hPP' : affineSpan ℝ (P : Set V) = affineSpan ℝ (P' : Set V)) :
    Commute (D.label P) (D.label P') := by
  obtain ⟨w, hw⟩ := d.exists_supportedRay (D.degree_mem P) (D.degree_ne_zero P)
  obtain ⟨w', hw'⟩ := d.exists_supportedRay (D.degree_mem P') (D.degree_ne_zero P')
  obtain rfl : w = w' := s.eq_of_mem_rayDegrees_of_ker_normal_le hw hw'
    (by rw [D.ker_normal P, D.ker_normal P', hPP'])
  have hg := D.label_mem_bchSubgroup_rayLieSubalgebra P hw
  have hg' := D.label_mem_bchSubgroup_rayLieSubalgebra P' hw'
  rw [LieSubalgebra.mem_bchSubgroup] at hg hg'
  exact BCHGroup.commute_of_lie_log_eq_zero _ _
    (lie_eq_zero_of_mem_rayLieSubalgebra (d.truncatedGrading ℒ k) hg hg')

end KSComplex

end Mei
