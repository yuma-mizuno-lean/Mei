/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Group
public import Mei.Geometry.ScatteringDiagram.WallSpace.Truncation

/-!
# Wall spaces at a joint

Fix a submonoid `W` of tangent vectors; at a joint of a scattering diagram it is the lattice
of tangent vectors along the joint. The walls through the joint have normals annihilating `W`,
so their labels lie in the exponential subgroup of the *joint subalgebra*: the sum of all wall
spaces whose normal annihilates `W`. By the contracted-bracket law this sum is a Lie
subalgebra, and every bracket of two of its elements lies in the *transverse* part, spanned
by the wall spaces of degrees `n` with `ρ n ∉ W`. Brackets landing in degrees with `ρ n ∈ W`
vanish.

Consequently, for a product of labels at a joint, the logarithm differs from the sum of the
logarithms of its factors only by transverse terms. In a degree `n` with `ρ n ∈ W` the two
components agree, and in particular they agree whenever `ρ n = 0`. In any other degree the
difference lies in the wall spaces whose normal annihilates both `W` and `ρ n`, and hence in a
single wall space if those normals are the integer multiples of one normal. For a rational
joint of codimension two and a degree whose geometric direction is transverse to it, these
normals form the integral points of a line.

Completed wall labels with normals annihilating `W` project at each finite order into the
exponential subgroup of the joint subalgebra of the truncated wall spaces.

The comparison with the sum of logarithms uses `LieSubalgebra.log_list_prod_sub_sum_mem`. The
vanishing in degrees along `W` is `Mei.DirectedWallSpaces.lie_eq_zero_of_normal_total_eq_zero`;
the corresponding statement for iterated brackets is
`Mei.DirectedWallSpaces.word_eq_zero_of_direction_mem`. The local analysis of joints follows
Gross, Hacking, Keel and Kontsevich, *Canonical bases for cluster algebras*, Appendix C.3,
in the directed setting of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Theorem 2.6.
-/

public section

namespace Mei.DirectedWallSpaces

open Mei BCHGroup

variable {Γ Λ R L : Type*} [AddCommMonoid Λ] [CommRing R] [LieRing L] [LieAlgebra R L]

section Joint

variable [AddCommMonoid Γ] {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  (W : AddSubmonoid Λ)

/-- The sum of the wall spaces whose degree has geometric direction outside `W` and whose
normal annihilates `W`. -/
def transverseJointSubmodule : Submodule R L :=
  ⨆ (n : Γ) (_ : ρ n ∉ W) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m

/-- The transverse joint submodule is the sum of its wall spaces. -/
theorem transverseJointSubmodule_def :
    H.transverseJointSubmodule W =
      ⨆ (n : Γ) (_ : ρ n ∉ W) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m := (rfl)

variable {W} in
/-- A wall space of a direction outside `W`, with normal annihilating `W`, is transverse. -/
theorem wall_le_transverseJointSubmodule {n : Γ} {m : Λ →+ ℤ} (hn : ρ n ∉ W)
    (hm : ∀ v ∈ W, m v = 0) : H.wall n m ≤ H.transverseJointSubmodule W :=
  le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le m (le_iSup_of_le hm le_rfl)))

/-- Brackets of sums of wall elements with normals annihilating `W` are transverse. -/
private theorem lie_mem_transverseJointSubmodule_aux {x y : L}
    (hx : x ∈ ⨆ (n : Γ) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m)
    (hy : y ∈ ⨆ (n : Γ) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m) :
    ⁅x, y⁆ ∈ H.transverseJointSubmodule W := by
  let T := H.transverseJointSubmodule W
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ ∈ T) hx
    (fun n x hx => ?_) (by simp [T])
    (fun x z hx hz => by simpa only [add_lie] using T.add_mem hx hz)
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ ∈ T) hx
    (fun m x hx => ?_) (by simp [T])
    (fun x z hx hz => by simpa only [add_lie] using T.add_mem hx hz)
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x, y⁆ ∈ T) hx
    (fun hm x hx => ?_) (by simp [T])
    (fun x z hx hz => by simpa only [add_lie] using T.add_mem hx hz)
  refine Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ ∈ T) hy
    (fun n' y hy => ?_) (by simp [T])
    (fun y z hy hz => by simpa only [lie_add] using T.add_mem hy hz)
  refine Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ ∈ T) hy
    (fun m' y hy => ?_) (by simp [T])
    (fun y z hy hz => by simpa only [lie_add] using T.add_mem hy hz)
  refine Submodule.iSup_induction _ (motive := fun y => ⁅x, y⁆ ∈ T) hy
    (fun hm' y hy => ?_) (by simp [T])
    (fun y z hy hz => by simpa only [lie_add] using T.add_mem hy hz)
  by_cases hn : ρ (n + n') ∈ W
  · rw [H.lie_eq_zero_of_normal_total_eq_zero hx hy (hm _ hn) (hm' _ hn)]
    exact T.zero_mem
  · refine H.wall_le_transverseJointSubmodule hn (fun v hv => ?_) (H.bracket_mem hx hy)
    simp [hm v hv, hm' v hv]

/-- The joint subalgebra: the sum of all wall spaces whose normal annihilates `W`. It contains
the wall spaces of all walls through a joint along `W`, and is closed under brackets by the
contracted-bracket law. -/
def jointSubalgebra : LieSubalgebra R L where
  toSubmodule := ⨆ (n : Γ) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m
  lie_mem' {x y} hx hy := by
    have hle : H.transverseJointSubmodule W ≤
        ⨆ (n : Γ) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m :=
      iSup_le fun n => iSup_le fun _ => iSup_le fun m => iSup_le fun hm =>
        le_iSup_of_le n (le_iSup_of_le m (le_iSup_of_le hm le_rfl))
    exact hle (H.lie_mem_transverseJointSubmodule_aux W hx hy)

/-- The joint subalgebra is the sum of the wall spaces whose normal annihilates `W`. -/
theorem jointSubalgebra_toSubmodule :
    (H.jointSubalgebra W).toSubmodule =
      ⨆ (n : Γ) (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m := (rfl)

variable {W} in
/-- A wall space whose normal annihilates `W` lies in the joint subalgebra. -/
theorem wall_le_jointSubalgebra {n : Γ} {m : Λ →+ ℤ} (hm : ∀ v ∈ W, m v = 0) :
    H.wall n m ≤ (H.jointSubalgebra W).toSubmodule := by
  rw [jointSubalgebra_toSubmodule]
  exact le_iSup_of_le n (le_iSup_of_le m (le_iSup_of_le hm le_rfl))

/-- The transverse wall spaces lie in the joint subalgebra. -/
theorem transverseJointSubmodule_le_jointSubalgebra :
    H.transverseJointSubmodule W ≤ (H.jointSubalgebra W).toSubmodule :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hm =>
    H.wall_le_jointSubalgebra hm

variable {W} in
/-- Brackets in the joint subalgebra are transverse: they have no component in degrees whose
geometric direction lies in `W`. -/
theorem lie_mem_transverseJointSubmodule {x y : L} (hx : x ∈ H.jointSubalgebra W)
    (hy : y ∈ H.jointSubalgebra W) : ⁅x, y⁆ ∈ H.transverseJointSubmodule W :=
  H.lie_mem_transverseJointSubmodule_aux W hx hy

variable {W} in
/-- If the normals annihilating `W` and the geometric direction of `n` are the integer
multiples of `μ`, then all wall spaces of degree `n` with normals annihilating `W` lie in the
wall space with normal `μ`. -/
theorem iSup_wall_le_wall_of_forall_mem_zmultiples {n : Γ} {μ : Λ →+ ℤ}
    (hμ : ∀ m : Λ →+ ℤ, (∀ v ∈ W, m v = 0) → m (ρ n) = 0 → m ∈ AddSubgroup.zmultiples μ) :
    ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m ≤ H.wall n μ := by
  refine iSup_le fun m => iSup_le fun hm => ?_
  by_cases hmn : m (ρ n) = 0
  · obtain ⟨c, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hμ m hm hmn)
    by_cases hc : c = 0
    · simp [hc, H.zero_normal]
    · rw [H.rescale n μ c hc]
  · simp [H.nontangent n m hmn]

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

variable {W} in
/-- A transverse element has no component in a degree whose geometric direction lies
in `W`. -/
theorem decompose_eq_zero_of_mem_transverseJointSubmodule {x : L}
    (hx : x ∈ H.transverseJointSubmodule W) {n : Γ} (hn : ρ n ∈ W) :
    (DirectSum.decompose ℒ x n : L) = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
    (fun n' x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
    (fun hn' x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
    (fun m x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) = 0) hx
    (fun _ x hx => ?_) (by simp) (fun x y hx hy => by simp [hx, hy])
  exact DirectSum.decompose_of_mem_ne ℒ (H.wall_le_piece n' m hx) (by rintro rfl; exact hn' hn)

/-- Every component of a transverse element lies in the wall spaces of its degree with
normals annihilating `W`. -/
theorem decompose_mem_of_mem_transverseJointSubmodule {x : L}
    (hx : x ∈ H.transverseJointSubmodule W) (n : Γ) :
    (DirectSum.decompose ℒ x n : L) ∈
      ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m := by
  let S := ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ W, m v = 0), H.wall n m
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ S) hx
    (fun n' x hx => ?_) (by simp [S]) (fun x y hx hy => by simpa using S.add_mem hx hy)
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ S) hx
    (fun _ x hx => ?_) (by simp [S]) (fun x y hx hy => by simpa using S.add_mem hx hy)
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ S) hx
    (fun m x hx => ?_) (by simp [S]) (fun x y hx hy => by simpa using S.add_mem hx hy)
  refine Submodule.iSup_induction _ (motive := fun x => (DirectSum.decompose ℒ x n : L) ∈ S) hx
    (fun hm x hx => ?_) (by simp [S]) (fun x y hx hy => by simpa using S.add_mem hx hy)
  by_cases hn : n' = n
  · subst n'
    rw [DirectSum.decompose_of_mem_same ℒ (H.wall_le_piece n m hx)]
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem hm hx)
  · rw [DirectSum.decompose_of_mem_ne ℒ (H.wall_le_piece n' m hx) hn]
    exact S.zero_mem

end Joint

section Product

variable [AddCommMonoid Γ] {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} (H : DirectedWallSpaces ρ ℒ)
  {W : AddSubmonoid Λ} [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing.IsNilpotent L] {l : List (BCHGroup L)}

/-- The logarithm of a product of labels at a joint differs from the sum of the logarithms of
the factors by a transverse element. -/
theorem log_list_prod_sub_sum_mem_transverseJointSubmodule
    (hl : ∀ g ∈ l, g ∈ (H.jointSubalgebra W).bchSubgroup) :
    log l.prod - (l.map log).sum ∈ H.transverseJointSubmodule W :=
  (H.jointSubalgebra W).log_list_prod_sub_sum_mem _
    (fun _ hx _ hy => H.lie_mem_transverseJointSubmodule hx hy) hl

variable [DecidableEq Γ] [DirectSum.Decomposition ℒ]

/-- In a degree whose geometric direction lies along the joint, the logarithm of a product of
labels at the joint has the same component as the sum of the logarithms of its factors. In
particular this holds in every degree of zero geometric direction. -/
theorem decompose_log_list_prod_of_mem
    (hl : ∀ g ∈ l, g ∈ (H.jointSubalgebra W).bchSubgroup) {n : Γ} (hn : ρ n ∈ W) :
    (DirectSum.decompose ℒ (log l.prod) n : L) = DirectSum.decompose ℒ (l.map log).sum n := by
  have h := H.decompose_eq_zero_of_mem_transverseJointSubmodule
    (H.log_list_prod_sub_sum_mem_transverseJointSubmodule hl) hn
  rwa [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, sub_eq_zero] at h

/-- In a degree `n` whose geometric direction is transverse to the joint, the logarithm of a
product of labels at the joint differs from the sum of the logarithms of its factors by an
element of the wall space with normal `μ`, provided the normals annihilating `W` and `ρ n` are
the integer multiples of `μ`. -/
theorem decompose_log_list_prod_sub_mem_wall
    (hl : ∀ g ∈ l, g ∈ (H.jointSubalgebra W).bchSubgroup) {n : Γ} {μ : Λ →+ ℤ}
    (hμ : ∀ m : Λ →+ ℤ, (∀ v ∈ W, m v = 0) → m (ρ n) = 0 → m ∈ AddSubgroup.zmultiples μ) :
    (DirectSum.decompose ℒ (log l.prod - (l.map log).sum) n : L) ∈ H.wall n μ :=
  H.iSup_wall_le_wall_of_forall_mem_zmultiples hμ
    (H.decompose_mem_of_mem_transverseJointSubmodule W
      (H.log_list_prod_sub_sum_mem_transverseJointSubmodule hl) n)

end Product

section Completed

variable [AddCommGroup Γ] [DecidableEq Γ] {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L}
  {d : PositiveDegrees Γ} [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (H : DirectedWallSpaces ρ ℒ) {W : AddSubmonoid Λ}

/-- The finite image of a supported-ray wall Lie algebra with normal annihilating `W` lies in
the joint subalgebra of the truncated wall spaces. -/
theorem truncatedRayLieSubalgebra_le_jointSubalgebra {m : Λ →+ ℤ} (hm : ∀ v ∈ W, m v = 0)
    (w : SupportedRay d) (k : ℕ) :
    H.truncatedRayLieSubalgebra w m k ≤ (H.truncated d k).jointSubalgebra W := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (H.mem_truncatedRayLieSubalgebra w m k x).mp hx
  have hle : (H.raySubmodule w m).map (d.degreeIdeal ℒ k).mkQ.toLinearMap ≤
      ((H.truncated d k).jointSubalgebra W).toSubmodule := by
    rw [raySubmodule_def, Submodule.map_iSup]
    exact iSup_le fun n => (H.truncated_wall d k n m).symm.le.trans
      ((H.truncated d k).wall_le_jointSubalgebra hm)
  exact hle (Submodule.mem_map_of_mem hy)

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- At every finite order, a completed wall label whose normal annihilates `W` lies in the
exponential subgroup of the truncated joint subalgebra. -/
theorem projection_mem_bchSubgroup_jointSubalgebra {w : SupportedRay d} {m : Λ →+ ℤ}
    {g : d.completedBCHGroup ℒ} (hg : g ∈ H.wallGroup w m) (hm : ∀ v ∈ W, m v = 0) (k : ℕ) :
    CompletedGroup.projection k g ∈ ((H.truncated d k).jointSubalgebra W).bchSubgroup :=
  (LieSubalgebra.bchSubgroup_le_bchSubgroup.mpr
    (H.truncatedRayLieSubalgebra_le_jointSubalgebra hm w k))
    ((LieSubalgebra.mem_bchSubgroup _ _).mpr ((H.mem_wallGroup w m g).mp hg k))

end Completed

end Mei.DirectedWallSpaces
