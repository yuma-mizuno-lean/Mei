/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall.Hyperplane
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.KS.Basic

/-!
# Projected principal walls of full KS hyperplanes

Let `A : M°_ℝ → U` be a `SkewLatticeDatum.KSRestriction` and let `n` be the generator of a
supported ray. The restriction of `p₁*(n)` is the character `{n, -}` of `N_uf`, which vanishes at
`n` because the form is alternating
(`SkewLatticeDatum.KSRestriction.apply_principalCharacter_mem_ker_normal`). So the full KS
hyperplane `n⊥` (`IndexedWall.hyperplane`) is KS-incoming, for every degree. Its projected
principal wall is the full hyperplane `ker κ(n)⟨n, -⟩` of `M°_ℝ`
(`SkewLatticeDatum.KSRestriction.projectedWall_hyperplane_support`), and this wall and its
principal cylinder are incoming
(`SkewLatticeDatum.KSRestriction.projectedWall_hyperplane_incoming`,
`SkewLatticeDatum.KSRestriction.cylinder_projectedWall_hyperplane_incoming`).

The principal realization follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, §1 and Appendix B (arXiv:1411.1394v2).
-/

public section

open TauCeti (PositiveDegrees SupportedRay)

noncomputable section

namespace Mei.SkewLatticeDatum.KSRestriction

variable {N V U : Type*} [AddCommGroup N] [Module.Free ℤ N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {D : SkewLatticeDatum N}
  {i : Module.Dual ℤ D.sublattice →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {j : (D.unfrozen →+ ℤ) →+ U} {hj : TauCeti.Toric.IsIntegralLattice j} {s : KSSpace hj}
  (A : D.KSRestriction h s)

omit [Module.Free ℤ N] in
/-- The restriction of `p₁*(n)` lies on the KS hyperplane `n⊥`, since `{n, n} = 0`. -/
theorem apply_principalCharacter_mem_ker_normal (n : D.unfrozen) :
    A.toLinearMap (i (D.principalCharacter n)) ∈ LinearMap.ker (s.normal n) := by
  rw [LinearMap.mem_ker, KSSpace.normal_apply, A.evaluation_principalCharacter, D.form_self,
    Rat.cast_zero]

variable {R : Type*} [CommRing R] [Algebra ℚ R] {d : PositiveDegrees D.unfrozen}
  [DecidableEq D.unfrozen] [DecidableEq (Module.Dual ℤ D.sublattice)]
  (w : SupportedRay d)
  (g : d.completedBCHGroup
    (SkewLieAlgebra.positiveGrading (D.coefficientForm R) (D.isAlt_coefficientForm R) d))
  (hg : g ∈ d.completedRaySubgroup _ w)

/-- The projected principal wall of the full KS hyperplane `n⊥` is the full hyperplane
`ker κ(n)⟨n, -⟩` of `M°_ℝ`. -/
theorem projectedWall_hyperplane_support :
    (A.projectedWall (IndexedWall.hyperplane s w g hg)).support =
      LinearMap.ker (h.realCharacter (D.projectedPrincipalNormal w.generator).toAddMonoidHom) := by
  have hκ : (D.sublattice.toAddSubgroup.rayIndex (w.generator : N) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (D.rayIndex_unfrozen_pos w.generator_ne_zero).ne'
  rw [A.realCharacter_projectedPrincipalNormal, LinearMap.ker_smul _ _ hκ, LinearMap.ker_comp,
    projectedWall_support, IndexedWall.hyperplane_support, Submodule.comap_coe]

/-- The projected principal wall of a full KS hyperplane is incoming. -/
theorem projectedWall_hyperplane_incoming :
    (A.projectedWall (IndexedWall.hyperplane s w g hg)).Incoming := by
  rw [projectedWall_incoming_iff, IndexedWall.hyperplane_ray, IndexedWall.hyperplane_support]
  exact A.apply_principalCharacter_mem_ker_normal w.generator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : D.unfrozen →+ E}
  (hk : TauCeti.Toric.IsIntegralLattice k)

/-- The principal cylinder of a full KS hyperplane is incoming. -/
theorem cylinder_projectedWall_hyperplane_incoming :
    ((A.projectedWall (IndexedWall.hyperplane s w g hg)).cylinder hk).Incoming :=
  (DirectedWall.cylinder_incoming_iff _ hk).mpr (A.projectedWall_hyperplane_incoming w g hg)

end Mei.SkewLatticeDatum.KSRestriction
