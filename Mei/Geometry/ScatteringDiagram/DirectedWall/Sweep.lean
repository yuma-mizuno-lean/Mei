/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Normal
public import Mei.Geometry.ScatteringDiagram.WallSpace.Coorientation
public import Mei.Geometry.Convex.PolyhedralComplex.Joint
public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep
public import Mei.Geometry.Convex.Sweep

/-!
# Outgoing walls from transverse joint coefficients

A homogeneous wall-space coefficient at a joint gives a directed wall on the
negative-ray sweep of that joint. The label is the completed exponential of the
negative coefficient. Its logarithms are homogeneous, and a nonzero coefficient
first becomes visible at its degree. This constructs the individual walls used
to correct a central obstruction; it does not assert consistency of their union.

`exists_swept_correction_wall` computes an eligible nonzero integral normal from
two equations for the actual joint direction. Its coefficient may initially lie
in the sum of wall spaces annihilating the joint: the contracted-normal theorem
places it in the required single wall space. The supported primitive generator
need not belong to the positive monoid. Sweeping along it gives the same support
as sweeping along the actual allowed degree.

`exists_cooriented_sweep` realizes a retained coefficient with the integral normal
inducing the contraction orientation of an oriented joint sweep. It reuses
`DirectedWallSpaces.exists_cooriented_sweep_normal`; changing the normal this way
preserves the coefficient's wall space, while fixing the positive side of its label.

The construction combines `FinitePolyhedralComplex.exists_joint_transverse_normal`,
`DirectedWallSpaces.iSup_wall_eq_wall_of_inf_ker`, the rational sweep presentation,
and `Convex.sweep_strictlyOutgoing`. It is the geometric wall construction of
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*,
proof of Theorem 2.6, and Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, Appendix C.3.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedWall

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ}

/-- Construct a wall on a sweep with a chosen supporting integral conormal and
supported ray. The coefficient lies in the homogeneous wall space at an actual
degree on that ray; the label is its negative completed exponential. -/
def ofSweep (P : Set V) (hP : P.Nonempty) (hPrat : IsRationalNormalPolyhedron h P)
    (w : SupportedRay d) (n : Γ) (hn : n ∈ w.rayDegrees)
    (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) : DirectedWall (d := d) h H where
  normal := m
  normal_ne_zero := hm
  ray := w
  normal_direction := by
    have hmn : m (ρ n) = 0 := by
      have hv : i (ρ n) ∈ (h.realCharacter m).ker := by
        rw [hker]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      simpa only [LinearMap.mem_ker, h.realCharacter_apply, Int.cast_eq_zero] using hv
    obtain ⟨_, a, ha, he⟩ := SupportedRay.mem_rayDegrees.mp hn
    rw [he, map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_id] at hmn
    exact (mul_eq_zero.mp hmn).resolve_left (ne_of_gt ha)
  support := sweep P (i (ρ n))
  support_nonempty := sweep_nonempty hP _
  rational_support := hPrat.sweep (ρ n)
  direction_support := by
    rw [direction_affineSpan, vectorSpan_sweep hP, ← direction_affineSpan, hker]
  label := d.expToCompletion ℒ (-c)
  label_mem := H.expToCompletion_mem_wallGroup
    (H.wall_le_raySubmodule w m hn ((H.wall n m).neg_mem hc))

@[simp]
theorem ofSweep_support (P : Set V) (hP : P.Nonempty)
    (hPrat : IsRationalNormalPolyhedron h P) (w : SupportedRay d) (n : Γ)
    (hn : n ∈ w.rayDegrees) (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) :
    (ofSweep P hP hPrat w n hn m hm hker c hc).support = sweep P (i (ρ n)) := (rfl)

@[simp]
theorem ofSweep_ray (P : Set V) (hP : P.Nonempty)
    (hPrat : IsRationalNormalPolyhedron h P) (w : SupportedRay d) (n : Γ)
    (hn : n ∈ w.rayDegrees) (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) :
    (ofSweep P hP hPrat w n hn m hm hker c hc).ray = w := (rfl)

@[simp]
theorem ofSweep_normal (P : Set V) (hP : P.Nonempty)
    (hPrat : IsRationalNormalPolyhedron h P) (w : SupportedRay d) (n : Γ)
    (hn : n ∈ w.rayDegrees) (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) :
    (ofSweep P hP hPrat w n hn m hm hker c hc).normal = m := (rfl)

@[simp]
theorem ofSweep_label (P : Set V) (hP : P.Nonempty)
    (hPrat : IsRationalNormalPolyhedron h P) (w : SupportedRay d) (n : Γ)
    (hn : n ∈ w.rayDegrees) (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) :
    (ofSweep P hP hPrat w n hn m hm hker c hc).label = d.expToCompletion ℒ (-c) := (rfl)

/-- A transverse swept wall is outgoing, tested on its actual allowed degree. -/
theorem ofSweep_outgoing (P : Set V) (hP : P.Nonempty)
    (hPrat : IsRationalNormalPolyhedron h P) (w : SupportedRay d) (n : Γ)
    (hn : n ∈ w.rayDegrees) (m : Λ →+ ℤ) (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    (c : L) (hc : c ∈ H.wall n m) (htrans : i (ρ n) ∉ (affineSpan ℝ P).direction) :
    (ofSweep P hP hPrat w n hn m hm hker c hc).Outgoing := by
  let W := ofSweep P hP hPrat w n hn m hm hker c hc
  have hray : n ∈ W.ray.rayDegrees := by simpa [W] using hn
  have hnot : i (ρ n) ∉ recessionCone W.support := by
    rw [ofSweep_support, mem_recessionCone]
    exact sweep_strictlyOutgoing hP (by simpa only [direction_affineSpan] using htrans)
  apply W.outgoing_iff.mpr
  intro hrec
  exact hnot ((W.incoming_iff_of_mem_rayDegrees hray).mp
    (W.incoming_iff.mpr (mem_recessionCone.mp hrec)))

/-- A transverse swept polyhedron with a homogeneous wall coefficient gives an
actual outgoing wall. Its normal, supported ray, support and label are prescribed,
and it is invisible below the coefficient's degree. -/
theorem exists_outgoing_sweep {P : Set V} (hP : IsRationalNormalPolyhedron h P)
    (hne : P.Nonempty) {n : Γ} {w : SupportedRay d} (hn : n ∈ w.rayDegrees)
    (htrans : i (ρ n) ∉ (affineSpan ℝ P).direction)
    {m : Λ →+ ℤ} (hm : m ≠ 0)
    (hker : (h.realCharacter m).ker = (affineSpan ℝ P).direction ⊔ ℝ ∙ i (ρ n))
    {a : L} (ha : a ∈ H.wall n m) :
    ∃ W : DirectedWall (d := d) h H,
      W.normal = m ∧ W.ray = w ∧ W.support = Convex.sweep P (i (ρ n)) ∧
      W.label = d.expToCompletion ℒ a ∧ W.Outgoing ∧
      ∀ l : ℕ, (l : ℤ) < d.degree n → CompletedGroup.projection l W.label = 1 := by
  let W := ofSweep P hne hP w n hn m hm hker (-a) ((H.wall n m).neg_mem ha)
  refine ⟨W, ofSweep_normal .., ofSweep_ray .., ofSweep_support .., ?_,
    ofSweep_outgoing _ _ _ _ _ _ _ _ _ _ _ htrans, ?_⟩
  · rw [ofSweep_label, neg_neg]
  · intro l hl
    rw [ofSweep_label, d.projection_expToCompletion_eq_one_iff ℒ
      (H.wall_le_piece _ _ ((H.wall n m).neg_mem ((H.wall n m).neg_mem ha)))]
    exact Or.inr hl

/-- Every transverse joint coefficient produces an outgoing wall with pure birth
logarithm. If the coefficient is nonzero, its first active order is exactly its
degree. No primitive-normal or saturation assumption is needed. -/
theorem exists_swept_correction_wall [Module.Free ℤ Γ]
    (C : FinitePolyhedralComplex h) {J : Set V} (hJ : J ∈ C.joints)
    (n : Γ) (hn : n ∈ d.monoid) (htrans : i (ρ n) ∉ (affineSpan ℝ J).direction)
    (c : L) (hc : c ∈ ⨆ (m : Λ →+ ℤ)
      (_ : ∀ v : Λ, i v ∈ (affineSpan ℝ J).direction → m v = 0), H.wall n m) :
    ∃ W : DirectedWall (d := d) h H,
      W.support = sweep J (i (ρ n)) ∧
      W.support = sweep J (i (ρ W.ray.generator)) ∧
      n ∈ W.ray.rayDegrees ∧ W.label = d.expToCompletion ℒ (-c) ∧
      W.Outgoing ∧ ∀ k : ℕ,
        CompletedGroup.projection k W.label = 1 ↔ c = 0 ∨ (k : ℤ) < d.degree n := by
  obtain ⟨f, g, hdir, hm, hker⟩ := C.exists_joint_transverse_normal hJ (ρ n) htrans
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact htrans (by simp)
  obtain ⟨w, hw⟩ := d.exists_supportedRay hn hn0
  have hmem (v : Λ) : i v ∈ (affineSpan ℝ J).direction ↔ v ∈ f.ker ⊓ g.ker := by
    simp only [hdir, Submodule.mem_inf, LinearMap.mem_ker, h.realCharacter_apply,
      Int.cast_eq_zero, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
  have hnfg : ρ n ∉ f.ker ⊓ g.ker := fun hv => htrans ((hmem _).mpr hv)
  have hc' : c ∈ H.wall n (f (ρ n) • g - g (ρ n) • f) := by
    rw [← H.iSup_wall_eq_wall_of_inf_ker f g hnfg]
    have hle : (⨆ (m : Λ →+ ℤ)
        (_ : ∀ v : Λ, i v ∈ (affineSpan ℝ J).direction → m v = 0), H.wall n m) ≤
        ⨆ (m : Λ →+ ℤ) (_ : ∀ v ∈ f.ker ⊓ g.ker, m v = 0), H.wall n m :=
      iSup_le fun m => iSup_le fun hm => le_iSup_of_le m
        (le_iSup_of_le (fun v hv => hm v ((hmem v).mpr hv)) le_rfl)
    exact hle hc
  have hcell := ((C.mem_cellsOfCodimension 2 J).mp hJ).1
  let W := ofSweep J (C.nonempty J hcell) (C.rational J hcell) w n hw
    (f (ρ n) • g - g (ρ n) • f) hm hker c hc'
  refine ⟨W, ofSweep_support .., ?_, by simpa [W] using hw, ofSweep_label ..,
    ofSweep_outgoing _ _ _ _ _ _ _ _ _ _ _ htrans, ?_⟩
  · rw [ofSweep_support, ofSweep_ray]
    obtain ⟨_, a, ha, he⟩ := SupportedRay.mem_rayDegrees.mp hw
    rw [he, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact sweep_smul_of_pos J _ (by exact_mod_cast ha)
  · intro k
    rw [ofSweep_label, d.projection_expToCompletion_eq_one_iff ℒ
      (H.wall_le_piece _ _ ((H.wall _ _).neg_mem hc'))]
    simp only [neg_eq_zero]

/-- A coefficient in a retained homogeneous piece of a finite-order joint
obstruction lifts to an outgoing swept wall in the original completed group.
Its finite logarithm is the negative obstruction coefficient, and it has a pure
birth logarithm with exactly the expected active cutoffs. -/
theorem exists_swept_correction_wall_of_truncated [Module.Free ℤ Γ]
    (C : FinitePolyhedralComplex h) {J : Set V} (hJ : J ∈ C.joints)
    (n : Γ) (hn : n ∈ d.monoid) (htrans : i (ρ n) ∉ (affineSpan ℝ J).direction)
    (k : ℕ) (hnk : d.degree n ≤ k) (c : d.truncatedLie ℒ k)
    (hc : c ∈ ⨆ (m : Λ →+ ℤ)
      (_ : ∀ v : Λ, i v ∈ (affineSpan ℝ J).direction → m v = 0),
      (H.truncated d k).wall n m) :
    ∃ W : DirectedWall (d := d) h H,
      W.support = sweep J (i (ρ n)) ∧
      W.support = sweep J (i (ρ W.ray.generator)) ∧
      n ∈ W.ray.rayDegrees ∧
      (∃ a ∈ ℒ n, W.label = d.expToCompletion ℒ (-a)) ∧ W.Outgoing ∧
      BCHGroup.log (CompletedGroup.projection k W.label) = -c ∧
      ∀ l : ℕ, CompletedGroup.projection l W.label = 1 ↔ c = 0 ∨ (l : ℤ) < d.degree n := by
  let S : Submodule R L := ⨆ (m : Λ →+ ℤ)
    (_ : ∀ v : Λ, i v ∈ (affineSpan ℝ J).direction → m v = 0), H.wall n m
  have hmap : (⨆ (m : Λ →+ ℤ)
      (_ : ∀ v : Λ, i v ∈ (affineSpan ℝ J).direction → m v = 0),
      (H.truncated d k).wall n m) = S.map (d.degreeIdeal ℒ k).mkQ.toLinearMap := by
    simp only [S, Submodule.map_iSup, H.truncated_wall]
  obtain ⟨a, haS, hac⟩ := Submodule.mem_map.mp (hmap ▸ hc)
  have hle : S ≤ ℒ n := iSup_le fun m => iSup_le fun _ => H.wall_le_piece n m
  have ha : a ∈ ℒ n := hle haS
  have haz : a = 0 ↔ c = 0 := by
    constructor
    · rintro rfl
      simpa using hac.symm
    · intro hc0
      have hai := (d.degreeIdeal ℒ k).mkQ_eq_zero.mp (hac.trans hc0)
      have hai' : a ∈ d.degreeSubmodule ℒ k := by
        simpa only [← LieSubmodule.mem_toSubmodule, PositiveDegrees.degreeIdeal_toSubmodule]
          using hai
      exact ((d.mem_degreeSubmodule_of_mem_iff ℒ ha).mp hai').resolve_right (not_lt.mpr hnk)
  obtain ⟨W, hs, hsr, hnW, hlabel, hout, hproj⟩ :=
    exists_swept_correction_wall C hJ n hn htrans a haS
  refine ⟨W, hs, hsr, hnW, ⟨a, ha, hlabel⟩, hout, ?_, ?_⟩
  · rw [hlabel, PositiveDegrees.projection_expToCompletion, BCHGroup.log_exp, map_neg]
    exact congrArg Neg.neg hac
  · intro l
    rw [hproj l, haz]

/-- Realize a retained homogeneous coefficient as an outgoing swept wall whose
integral normal agrees with the contraction orientation of the swept cell.
The input equation may have either sign or any nonzero integral scale.
The logarithm is the negative coefficient, and the active cutoffs are exact,
including when the coefficient is zero. -/
theorem exists_cooriented_sweep [Module.Free ℤ Γ]
    (σ : OrientedCell h 2) {n : Γ} (hn : n ∈ d.monoid)
    (htrans : i (ρ n) ∉ (affineSpan ℝ σ.carrier).direction)
    (m₀ : Λ →+ ℤ)
    (h₀ : (h.realCharacter m₀).ker =
      (affineSpan ℝ σ.carrier).direction ⊔ ℝ ∙ i (ρ n))
    (k : ℕ) (hnk : d.degree n ≤ k) (c : d.truncatedLie ℒ k)
    (hc : c ∈ (H.truncated d k).wall n m₀) :
    ∃ W : DirectedWall (d := d) h H,
      W.support = (σ.sweep (ρ n) htrans).carrier ∧
      (∀ v : V, SignType.sign (h.realCharacter W.normal v) =
        (σ.sweep (ρ n) htrans).orientation.evalSign (fun _ : Fin 1 => v)) ∧
      n ∈ W.ray.rayDegrees ∧
      (∃ a ∈ ℒ n, W.label = d.expToCompletion ℒ (-a)) ∧ W.Outgoing ∧
      BCHGroup.log (CompletedGroup.projection k W.label) = -c ∧
      ∀ l : ℕ, CompletedGroup.projection l W.label = 1 ↔
        c = 0 ∨ (l : ℤ) < d.degree n := by
  obtain ⟨m, hm, hker, hsign, hwall⟩ := H.exists_cooriented_sweep_normal σ (ρ n) htrans m₀ h₀
  have hc' : c ∈ (H.truncated d k).wall n m := by
    simpa only [H.truncated_wall, hwall] using hc
  rw [H.truncated_wall] at hc'
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.mp hc'
  have hap : a ∈ ℒ n := H.wall_le_piece n m ha
  have haz : a = 0 ↔ c = 0 := by
    have he := d.projection_expToCompletion_eq_one_iff ℒ hap k
    rw [or_iff_left (not_lt.mpr hnk)] at he
    have hquot : BCHGroup.exp ((d.degreeIdeal ℒ k).mkQ a) =
        (1 : d.truncatedGroup ℒ k) ↔ c = 0 := by
      rw [← (BCHGroup.log_injective (L := d.truncatedLie ℒ k)).eq_iff,
        BCHGroup.log_exp, BCHGroup.log_one]
      exact (congrArg (fun x : d.truncatedLie ℒ k => x = 0) hac).to_iff
    -- Compare the categorical tower projection with the concrete BCH quotient.
    have hc0 : CompletedGroup.projection k (d.expToCompletion ℒ a) = 1 ↔ c = 0 :=
      (d.projection_expToCompletion ℒ k a).symm ▸ hquot
    exact he.symm.trans hc0
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact htrans (by simp)
  obtain ⟨w, hw⟩ := d.exists_supportedRay hn hn0
  let W := ofSweep σ.carrier σ.nonempty σ.rational w n hw m hm hker a ha
  refine ⟨W, by rw [OrientedCell.sweep_carrier]; exact ofSweep_support ..,
    hsign, by simpa only [W, ofSweep_ray] using hw,
    ⟨a, hap, ofSweep_label ..⟩, ofSweep_outgoing _ _ _ _ _ _ _ _ _ _ _ htrans, ?_, ?_⟩
  · rw [ofSweep_label, PositiveDegrees.projection_expToCompletion, BCHGroup.log_exp, map_neg]
    exact congrArg Neg.neg hac
  · intro l
    rw [ofSweep_label, d.projection_expToCompletion_eq_one_iff ℒ
      ((ℒ n).neg_mem hap), neg_eq_zero, haz]

end Mei.DirectedWall
