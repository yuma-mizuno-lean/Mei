/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.DecoratedRay
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Examples of decorated broken lines

Two checks on the actual decorated fibers `DecoratedAdmissibleRay`, whose direction is the
negative of the forward velocity.

* *No walls.* With no encounters, no walls and no singular sets, a nonzero homogeneous input
  `a` of degree `p` has exactly one decorated ray ending at each point `Q`. It is the line
  `t ↦ Q - t • velocity p` on the negative half-line, and its single decoration is `a` itself
  (`DecoratedAdmissibleRay.nonempty_of_isEmpty`, the `Subsingleton` instance,
  `DecoratedAdmissibleRay.ray_apply_of_nonpos`, `decoratedRayEvaluation_of_isEmpty`). The
  history is the empty one for every `Q`.

* *One wall with a nilpotent label.* Let `A = ℚ[x, x⁻¹, t] / (t²)` be graded by the exponents of
  `x` and `t`, with `ρ(r, s) = r`. The wall `{0} ⊂ ℝ` with coorientation `u ↦ u` has label
  `θ(x) = x (1 + t)`, `θ(t) = t`. A path crossing the wall from right to left with incoming
  decoration `x` continues with decoration exactly `x` or `t x`, each with velocity `1`; the ray,
  whose direction is the negative of the velocity, has slope `-1` in the backward parameter
  (`DualNumberWall.historySupport_eq`, `DualNumberWall.range_decoration_eq`,
  `DualNumberWall.ray_apply_of_nonpos`). The weighted evaluation at every endpoint `Q < 0` is
  `θ x = x + t x`, and no ray ends at `Q ≥ 0` (`DualNumberWall.evaluation_of_neg`,
  `DualNumberWall.evaluation_of_nonneg`).
  Since `t² = 0`, the module `A` has the monomials `x^r t^s`, `s ∈ {0, 1}`, as a basis. Only
  this ℚ-module structure enters the decorated fibers, so `A` is modelled by the ℚ-module with
  basis indexed by `ℤ × Fin 2`. The ring structure of the model is not that of `A`, and the
  index set is not a submonoid of `ℤ²`.

The decorated broken lines follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, Definition 3.1 (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta functions,
and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public section

open Set Filter Mei.Convex

namespace Mei

section NoWalls

variable {R M Γ V J K : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq Γ] (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : Fin 0 → Module.End R M) (p₀ : Γ) (a : ℳ p₀)
  (velocity : Γ → V) (f : Fin 0 → V →L[ℝ] ℝ) (c : Fin 0 → ℝ)
  (ε : Fin 0 → SignType) (P : Fin 0 → Set V) (W : J → Set V) (S : K → Set V) (C : Set V)

namespace DecoratedAdmissibleRay

variable {ℳ T p₀ a velocity f c ε P W S C} {Q : V}

/-- A decorated ray with no encounters is the straight line in the velocity of its input. -/
theorem ray_apply_of_nonpos (r : DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q)
    {t : ℝ} (ht : t ≤ 0) : r.2.ray t = Q - t • velocity p₀ := by
  -- the single direction is `velocity p₀`, since the history is the empty one
  have hv : ∀ i : Fin 1, velocity (Fin.snoc (α := fun _ => Γ) r.1.1 p₀ i) = velocity p₀ :=
    fun i => by rw [Fin.snoc_zero, Fin.fin_one_eq_zero i]
  simpa [hv] using r.2.ray_eq_endpoint_sub_smul_of_directions_eq
    (fun i => by simp [hv]) ht

/-- With no encounters there is at most one decorated ray at each endpoint. -/
instance : Subsingleton (DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S C Q) where
  allEq r s := by
    obtain ⟨⟨p, hp⟩, r⟩ := r
    obtain ⟨⟨p', hp'⟩, s⟩ := s
    obtain rfl : p = p' := Subsingleton.elim _ _
    obtain rfl : r = s := Subsingleton.elim _ _
    rfl

/-- Without walls or singular sets, a nonzero input has a decorated ray ending at every point.
Its history is the empty one, and its only decoration is the input. -/
theorem nonempty_of_isEmpty [IsEmpty J] [IsEmpty K] (ha : (a : M) ≠ 0) :
    Nonempty (DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S univ Q) :=
  (nonempty_decoratedAdmissibleRay_iff ℳ T p₀ a velocity f c ε P W S univ Q).mpr
    ⟨isEmptyElim, (mem_decoratedHistorySupport ℳ T p₀ a velocity f ε _).mpr
      ⟨by simpa using ha, fun j => j.elim0⟩, mem_admissibleBackwardDomain_of_isEmpty f c P W S Q⟩

end DecoratedAdmissibleRay

/-- Without walls or singular sets, the weighted evaluation of a nonzero input is the input
itself at every endpoint: the unique decorated ray is the straight incoming line. -/
theorem decoratedRayEvaluation_of_isEmpty [IsEmpty J] [IsEmpty K] (ha : (a : M) ≠ 0) (Q : V) :
    decoratedRayEvaluation ℳ T p₀ a velocity f c ε P W S univ Q = a := by
  obtain ⟨r⟩ := DecoratedAdmissibleRay.nonempty_of_isEmpty (ℳ := ℳ) (T := T) (velocity := velocity)
    (f := f) (c := c) (ε := ε) (P := P) (W := W) (S := S) (Q := Q) ha
  let := Fintype.ofFinite (DecoratedAdmissibleRay ℳ T p₀ a velocity f c ε P W S univ Q)
  let := uniqueOfSubsingleton r
  rw [decoratedRayEvaluation_def, Fintype.sum_unique]
  exact r.decoration_last

end NoWalls

namespace DualNumberWall

open AddMonoidAlgebra

/-- The exponents `(r, s)` of the monomials `x^r t^s`, `s ∈ {0, 1}`, of `ℚ[x, x⁻¹, t] / (t²)`.
This is only an index set: `Fin 2` carries addition mod 2, not that of exponents of `t`. -/
abbrev Degree := ℤ × Fin 2

/-- A ℚ-module model of `ℚ[x, x⁻¹, t] / (t²)`, with basis the monomials
`single (r, s) 1 = x^r t^s`. Its homogeneous pieces `AddMonoidAlgebra.grade ℚ (r, s)` are the
lines spanned by `x^r t^s`. Only the module structure is used: the ring structure of this group
algebra is not the dual-number ring (here `t² = 1`, not `0`). -/
abbrev Coefficients := AddMonoidAlgebra ℚ Degree

/-- The label `θ`, as a linear map on the monomial basis:
`x^r t^s ↦ x^r (1 + t)^r t^s`, that is `x^r ↦ x^r + r t x^r` and `x^r t ↦ x^r t`. -/
noncomputable def theta : Coefficients →ₗ[ℚ] Coefficients :=
  (coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.linearCombination ℚ (fun γ : Degree =>
      Finsupp.single γ (1 : ℚ) + if γ.2 = 0 then Finsupp.single (γ.1, 1) (γ.1 : ℚ) else 0) ∘ₗ
    (coeffLinearEquiv ℚ).toLinearMap

/-- `θ(x^r) = x^r + r t x^r`. -/
theorem theta_single_zero (r : ℤ) :
    theta (single (r, 0) 1) = single (r, 0) 1 + single (r, 1) (r : ℚ) := by
  simp [theta]

/-- `θ(x^r t) = x^r t`. -/
theorem theta_single_one (r : ℤ) : theta (single (r, 1) 1) = single (r, 1) 1 := by
  simp [theta]

/-- The incoming decoration `x`, of degree `(1, 0)`. -/
noncomputable def incoming : grade ℚ ((1, 0) : Degree) :=
  ⟨single (1, 0) 1, single_mem_grade _ _⟩

/-- The velocity `i(ρ(r, s)) = r` of a decoration of degree `(r, s)`. -/
def velocity (γ : Degree) : ℝ := γ.1

/-- The decorated rays ending at `Q` that cross the wall `{0}` of `ℝ` once. The coorientation
is `u ↦ u`, so a crossing from right to left has forward derivative `-1`, hence the label
contributes `θ`, and the pairing of the normal with the velocity of the decorations has
sign `1`. -/
abbrev Ray (Q : ℝ) :=
  DecoratedAdmissibleRay (grade ℚ : Degree → Submodule ℚ Coefficients)
    (fun _ : Fin 1 => theta) (1, 0) incoming velocity
    (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0) (fun _ => 1) (fun _ => univ)
    (fun _ : Unit => {0}) (fun _ : Empty => ∅) univ Q

/-- The decoration histories of the crossing that survive the sign and velocity conditions. -/
noncomputable abbrev historySupport : Finset (Fin 1 → Degree) :=
  decoratedHistorySupport (grade ℚ : Degree → Submodule ℚ Coefficients)
    (fun _ : Fin 1 => theta) (1, 0) incoming velocity (fun _ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => 1)

/-- The endpoints admitted by the geometry of the crossing when the decoration history is `p`. -/
noncomputable abbrev backwardDomain (p : Fin 1 → Degree) : Set ℝ :=
  admissibleBackwardDomain (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0)
    (fun j => velocity (Fin.snoc (α := fun _ => Degree) p (1, 0) j)) (fun _ => univ)
    (fun _ : Unit => ({0} : Set ℝ)) (fun _ : Empty => (∅ : Set ℝ)) univ

/-- The last decoration of the crossing history `fun _ => q` followed by `d` is `d`. Here
`(1 : Fin 2)` is `Fin.last 1` by definition. -/
theorem snoc_const_one (q d : Degree) :
    Fin.snoc (α := fun _ => Degree) (fun _ : Fin 1 => q) d 1 = d :=
  Fin.snoc_last _ _

/-- The history `x ↦ θ x` with final degree `p 0` has the component of `θ x` in that degree. -/
theorem homogeneousHistory_incoming (p : Fin 1 → Degree) :
    homogeneousHistory (grade ℚ : Degree → Submodule ℚ Coefficients) (fun _ : Fin 1 => theta)
      p incoming.1 =
      if p 0 = (1, 0) then single (1, 0) 1 else if p 0 = (1, 1) then single (1, 1) 1 else 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = fun _ => q := ⟨_, eq_const_of_unique p⟩
  have hx : theta incoming.1 = single (1, 0) 1 + single (1, 1) 1 := by
    simp [incoming, theta_single_zero]
  have h₀ : (single (1, 0) 1 : Coefficients) ∈ grade ℚ ((1, 0) : Degree) := single_mem_grade _ _
  have h₁ : (single (1, 1) 1 : Coefficients) ∈ grade ℚ ((1, 1) : Degree) := single_mem_grade _ _
  rw [homogeneousHistory_succ_apply, homogeneousHistory_zero, LinearMap.id_apply, hx,
    DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
  by_cases h0 : q = (1, 0)
  · subst h0
    simp [DirectSum.decompose_of_mem_same _ h₀, DirectSum.decompose_of_mem_ne _ h₁]
  · by_cases h1 : q = (1, 1)
    · subst h1
      simp [DirectSum.decompose_of_mem_same _ h₁, DirectSum.decompose_of_mem_ne _ h₀]
    · simp [h0, h1, DirectSum.decompose_of_mem_ne _ h₀ (Ne.symm h0),
        DirectSum.decompose_of_mem_ne _ h₁ (Ne.symm h1)]

/-- After the crossing the decoration is exactly `x` or `t x`: these are the histories
with nonzero whole decoration, positive crossing sign and preserved normal velocity. -/
theorem historySupport_eq : historySupport = {fun _ => (1, 0), fun _ => (1, 1)} := by
  ext p
  obtain ⟨q, rfl⟩ : ∃ q, p = fun _ => q := ⟨_, eq_const_of_unique p⟩
  rw [historySupport, mem_decoratedHistorySupport, homogeneousHistory_incoming]
  simp only [Finset.mem_insert, Finset.mem_singleton, funext_iff, forall_const,
    Fin.forall_fin_one, Fin.succ_zero_eq_one, snoc_const_one]
  by_cases h0 : q = (1, 0)
  · subst h0
    simp [velocity]
  · by_cases h1 : q = (1, 1)
    · subst h1
      simp [velocity]
    · simp [h0, h1]

/-- For the straight line of velocity `1` across the wall `{0}`, the admissible backward domain
is exactly `{Q | Q < 0}`. -/
private theorem mem_admissibleBackwardDomain_iff_neg (Q : ℝ) :
    Q ∈ admissibleBackwardDomain (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ) (fun _ => 0)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ => univ) (fun _ : Unit => ({0} : Set ℝ))
      (fun _ : Empty => (∅ : Set ℝ)) univ ↔ Q < 0 := by
  rw [← nonempty_admissibleRayRealization_iff]
  constructor
  · -- a realization meets the wall at its parameter `r.parameter 1 < 0`, on the backward ray
    rintro ⟨r⟩
    have h1 : r.parameter 1 < r.parameter 0 := r.strictAnti_parameter (by decide)
    have hb := r.ray_eq_add_smul_of_before_parameter 0 (t := r.parameter 1) h1.le
      (fun j hj => by rw [Fin.eq_one_of_ne_zero j hj.ne'])
    have hh := r.height_eq 0
    simp only [Fin.succ_zero_eq_one, ContinuousLinearMap.id] at hh
    rw [hb, r.parameter_zero, FiniteAffineRay.eval_zero, r.endpoint_eq] at hh
    have hh' : Q + -r.parameter 1 = 0 := by simpa using hh
    rw [r.parameter_zero] at h1
    linarith
  · -- for `Q < 0` the straight ray reaches the wall at backward time `Q`
    intro hQ
    refine ⟨{
      ray := FiniteAffineRay.straight Q 1
      parameter := ![0, Q]
      parameter_zero := rfl
      strictAnti_parameter := ?_
      transverse := fun j => by simp
      endpoint_eq := by simp
      directionAt_eq := fun j => by simp
      bends_recorded := fun t ht => by simp at ht
      height_eq := fun j => ?_
      incidence := fun j => mem_univ _
      avoids_walls := fun a t ht hne => ?_
      incoming := Eventually.of_forall fun t => mem_univ _
      avoids_singular := fun a => isEmptyElim a
      off_walls := fun a => ?_ }⟩
    · refine Fin.strictAnti_iff_succ_lt.mpr fun i => ?_
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      simpa using hQ
    · simp [FiniteAffineRay.eval_def]
    · intro h0
      apply hne 0
      have h : -t + Q = 0 := by simpa [FiniteAffineRay.eval_def] using h0
      simp
      linarith
    · simpa using hQ.ne

/-- After either decoration the velocity is still `1`: the direction is unchanged. -/
private theorem velocity_snoc_of_mem_historySupport {p : Fin 1 → Degree}
    (hp : p ∈ historySupport) :
    (fun j => velocity (Fin.snoc (α := fun _ => Degree) p (1, 0) j)) = fun _ : Fin 2 => 1 := by
  rw [historySupport_eq, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> funext j <;> fin_cases j <;>
    simp [snoc_const_one, velocity]

/-- The endpoint domain of either decoration is the half-line `Q < 0`. -/
private theorem mem_backwardDomain_iff_neg {p : Fin 1 → Degree} (hp : p ∈ historySupport)
    (Q : ℝ) : Q ∈ backwardDomain p ↔ Q < 0 := by
  rw [backwardDomain, velocity_snoc_of_mem_historySupport hp]
  exact mem_admissibleBackwardDomain_iff_neg Q

/-- No ray ends on the far side of the wall or on it. -/
theorem isEmpty_ray_of_nonneg {Q : ℝ} (hQ : 0 ≤ Q) : IsEmpty (Ray Q) := by
  refine ⟨fun r => ?_⟩
  have h := (nonempty_decoratedAdmissibleRay_iff _ _ _ _ _ _ _ _ _ _ _ _ Q).mp ⟨r⟩
  obtain ⟨p, hp, hQ'⟩ := h
  exact absurd ((mem_backwardDomain_iff_neg hp Q).mp hQ') hQ.not_gt

/-- Every history of the support is realized by a ray ending at each point left of the wall. -/
theorem exists_ray_of_neg {Q : ℝ} (hQ : Q < 0) {p : Fin 1 → Degree}
    (hp : p ∈ historySupport) : ∃ r : Ray Q, r.1.1 = p :=
  ⟨⟨⟨p, hp⟩, admissibleRayRealization _ _ _ _ _ _ _ _
    ((mem_backwardDomain_iff_neg hp Q).mpr hQ)⟩, rfl⟩

/-- Both rays have velocity `1` before and after the crossing, so each is the line of slope `-1`
in the backward parameter through `Q`. -/
theorem ray_apply_of_nonpos {Q : ℝ} (r : Ray Q) {t : ℝ} (ht : t ≤ 0) : r.2.ray t = Q - t := by
  have hv := velocity_snoc_of_mem_historySupport r.1.2
  have h := r.2.ray_eq_endpoint_sub_smul_of_directions_eq
    (fun i => by rw [congrFun hv i, congrFun hv 0]) ht
  simpa only [congrFun hv 0, smul_eq_mul, mul_one] using h

/-- The final decoration of a ray is the component of `θ x` in its degree. -/
theorem decoration_zero_eq {Q : ℝ} (r : Ray Q) :
    r.decoration 0 =
      if r.1.1 0 = (1, 0) then single (1, 0) 1 else if r.1.1 0 = (1, 1) then single (1, 1) 1
      else 0 := by
  rw [DecoratedAdmissibleRay.decoration_zero, homogeneousHistory_incoming]

/-- The possible next decorations at a point left of the wall are exactly `x` and `t x`. -/
theorem range_decoration_eq {Q : ℝ} (hQ : Q < 0) :
    Set.range (fun r : Ray Q => r.decoration 0) = {single (1, 0) 1, single (1, 1) 1} := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    have hp : r.1.1 ∈ ({fun _ => (1, 0), fun _ => (1, 1)} : Finset (Fin 1 → Degree)) := by
      rw [← historySupport_eq]
      exact r.1.2
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    dsimp only
    rw [decoration_zero_eq]
    rcases hp with hp | hp <;> simp [hp]
  · rintro (rfl | rfl)
    · obtain ⟨r, hr⟩ := exists_ray_of_neg hQ (p := fun _ => (1, 0))
        (by simp [historySupport_eq])
      refine ⟨r, ?_⟩
      dsimp only
      rw [decoration_zero_eq, hr]
      simp
    · obtain ⟨r, hr⟩ := exists_ray_of_neg hQ (p := fun _ => (1, 1))
        (by simp [historySupport_eq])
      refine ⟨r, ?_⟩
      dsimp only
      rw [decoration_zero_eq, hr]
      simp

/-- The weighted evaluation of the crossing at `Q`. -/
noncomputable abbrev evaluation (Q : ℝ) : Coefficients :=
  decoratedRayEvaluation (grade ℚ : Degree → Submodule ℚ Coefficients)
    (fun _ : Fin 1 => theta) (1, 0) incoming velocity (fun _ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => 0) (fun _ => 1) (fun _ => univ) (fun _ : Unit => {0}) (fun _ : Empty => ∅) univ Q

/-- Left of the wall, every history of the support contributes to the weighted evaluation. -/
theorem evaluation_eq_sum_of_neg {Q : ℝ} (hQ : Q < 0) :
    evaluation Q = ∑ p ∈ historySupport,
      homogeneousHistory (grade ℚ : Degree → Submodule ℚ Coefficients)
        (fun _ : Fin 1 => theta) p incoming.1 := by
  classical
  rw [evaluation, decoratedRayEvaluation_eq_sum, Finset.sum_coe_sort historySupport
    (fun p => if Q ∈ backwardDomain p then
      homogeneousHistory (grade ℚ : Degree → Submodule ℚ Coefficients)
        (fun _ : Fin 1 => theta) p incoming.1 else 0)]
  exact Finset.sum_congr rfl fun p hp => by
    simp [(mem_backwardDomain_iff_neg hp Q).mpr hQ]

/-- Left of the wall the weighted evaluation is `θ x = x + t x`. -/
theorem evaluation_of_neg {Q : ℝ} (hQ : Q < 0) :
    evaluation Q = single (1, 0) 1 + single (1, 1) 1 := by
  rw [evaluation_eq_sum_of_neg hQ, historySupport_eq,
    Finset.sum_pair (by simp [funext_iff])]
  simp only [homogeneousHistory_incoming]
  simp

/-- On or right of the wall no ray ends, and the weighted evaluation vanishes. -/
theorem evaluation_of_nonneg {Q : ℝ} (hQ : 0 ≤ Q) : evaluation Q = 0 := by
  classical
  have := isEmpty_ray_of_nonneg hQ
  rw [evaluation, decoratedRayEvaluation_def]
  exact Finset.sum_eq_zero fun r _ => isEmptyElim r

/-- Left of the wall, the weighted evaluation is the action of the label on the incoming
decoration. -/
theorem evaluation_of_neg_eq_theta {Q : ℝ} (hQ : Q < 0) : evaluation Q = theta incoming.1 := by
  rw [evaluation_of_neg hQ]
  simp [incoming, theta_single_zero]

end DualNumberWall

end Mei
