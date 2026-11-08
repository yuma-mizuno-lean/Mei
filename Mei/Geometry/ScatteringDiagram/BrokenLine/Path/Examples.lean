/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Path.Family
public import Mei.Geometry.Convex.Sweep.Admissible.Terminal
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Examples of decorated broken lines through chamber modules

Two checks on the actual decorated fibers `PathDecoratedRay`, whose direction is the
negative of the forward velocity.

* *No walls.* Along the empty encounter path, with no walls and no singular sets, a
  nonzero homogeneous input `x` of degree `i₀` has exactly one decorated ray ending at each
  point `X`. It is the line `t ↦ X - t • v a i₀` on the negative half-line, and its
  decoration is `x` itself (`PathDecoratedRay.nonempty_nil_of_isEmpty`, the `Subsingleton`
  instance, `PathDecoratedRay.ray_apply_nil`, `pathDecoratedEvaluation_nil_of_isEmpty`).

* *One wall with a nilpotent label.* Let `A = ℚ[x, x⁻¹, t] / (t²)` be graded by the exponents
  of `x` and `t`, with `ρ(r, s) = r`. The wall `{0} ⊂ ℝ` with coorientation `u ↦ u` has label
  `θ(x) = x (1 + t)`, `θ(t) = t`. A path crossing the wall from right to left with incoming
  decoration `x` continues with decoration exactly `x` or `t x`, each with velocity `1`; the
  ray, whose direction is the negative of the velocity, has slope `-1` in the backward
  parameter (`DualNumberWall.historySupport_eq`, `DualNumberWall.range_decoration_eq`,
  `DualNumberWall.ray_apply_of_nonpos`). The weighted evaluation at every endpoint `Q < 0`
  is `θ x = x + t x`, and no ray ends at `Q ≥ 0` (`DualNumberWall.evaluation_of_neg`,
  `DualNumberWall.evaluation_of_nonneg`). The crossing is the one arrow of the one-object
  quiver on `Unit`.
  Since `t² = 0`, the module `A` has the monomials `x^r t^s`, `s ∈ {0, 1}`, as a basis. Only
  this ℚ-module structure enters the decorated fibers, so `A` is modelled by the ℚ-module
  with basis indexed by `ℤ × Fin 2`. The ring structure of the model is not that of `A`, and
  the index set is not a submonoid of `ℤ²`.

The decorated broken lines follow Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, Definition 3.1 (arXiv:1411.1394v2), and Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public section

open Set Filter Quiver Mei.Convex

namespace Mei

section NoWalls

variable {Q R V J K : Type*} [Quiver Q] [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  {T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c}
  {ℳ : ∀ q, ι q → Submodule R (M q)} [∀ q, DirectSum.Decomposition (ℳ q)]
  {a : Q} {i₀ : ι a} {x : ℳ a i₀}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {v : ∀ q, ι q → V} {ν : ∀ {b c : Q}, (b ⟶ c) → V →L[ℝ] ℝ}
  {ε : ∀ {b c : Q}, (b ⟶ c) → SignType} {c : ∀ {b c : Q}, (b ⟶ c) → ℝ}
  {P : ∀ {b c : Q}, (b ⟶ c) → Set V} {W : J → Set V} {S : K → Set V} {C : Set V} {X : V}

namespace PathDecoratedRay

/-- A decorated ray along the empty path is the straight line in the velocity of its input. -/
theorem ray_apply_nil
    (r : PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (Path.nil : Path a a) X)
    {t : ℝ} (ht : t ≤ 0) : r.2.ray t = X - t • v a i₀ := by
  simpa only [Path.Degrees.reverseVertexLabels_nil] using
    r.2.ray_eq_endpoint_sub_smul_of_directions_eq
      (fun _ => by simp only [Path.Degrees.reverseVertexLabels_nil]) ht

/-- Along the empty path there is at most one decorated ray at each endpoint. -/
instance : Subsingleton (PathDecoratedRay T ℳ i₀ x v ν ε c P W S C (Path.nil : Path a a) X) :=
  ⟨fun r s => ext_history r s (Subsingleton.elim _ _)⟩

/-- Without walls or singular sets, a nonzero input has a decorated ray along the empty
path ending at every point. Its history is the empty one. -/
theorem nonempty_nil_of_isEmpty [IsEmpty J] [IsEmpty K] (hx : (x : M a) ≠ 0) :
    Nonempty (PathDecoratedRay T ℳ i₀ x v ν ε c P W S univ (Path.nil : Path a a) X) :=
  ⟨⟨⟨PUnit.unit, (mem_pathDecoratedHistorySupport T ℳ i₀ x v ν ε _ _).mpr
      ⟨by simpa using hx, fun j => j.elim0⟩⟩,
    admissibleRayRealization _ _ _ _ _ _ _ _
      (mem_admissibleBackwardDomain_of_isEmpty _ _ _ W S X)⟩⟩

end PathDecoratedRay

/-- Without walls or singular sets, the weighted evaluation of a nonzero input over the
inventory of the empty path is the input itself at every endpoint. -/
theorem pathDecoratedEvaluation_nil_of_isEmpty [IsEmpty J] [IsEmpty K] (hx : (x : M a) ≠ 0)
    (X : V) :
    pathDecoratedEvaluation T ℳ i₀ x {(Path.nil : Path a a)} v ν ε c P W S univ X = x := by
  obtain ⟨r⟩ := PathDecoratedRay.nonempty_nil_of_isEmpty (T := T) (ν := ν) (ε := ε) (c := c)
    (P := P) (W := W) (S := S) (X := X) (v := v) hx
  let z : Σ p : ({(Path.nil : Path a a)} : Finset (Path a a)),
      PathDecoratedRay T ℳ i₀ x v ν ε c P W S univ p.val X :=
    ⟨⟨Path.nil, Finset.mem_singleton_self _⟩, r⟩
  have hsub : Subsingleton (Σ p : ({(Path.nil : Path a a)} : Finset (Path a a)),
      PathDecoratedRay T ℳ i₀ x v ν ε c P W S univ p.val X) := by
    refine ⟨fun ⟨p, r⟩ ⟨q, s⟩ => ?_⟩
    obtain rfl : p = q := Subsingleton.elim _ _
    obtain rfl : r = s := by
      obtain ⟨p, hp⟩ := p
      rw [Finset.mem_singleton] at hp
      subst hp
      exact PathDecoratedRay.ext_history r s (Subsingleton.elim _ _)
    rfl
  let := Fintype.ofFinite (Σ p : ({(Path.nil : Path a a)} : Finset (Path a a)),
      PathDecoratedRay T ℳ i₀ x v ν ε c P W S univ p.val X)
  let := uniqueOfSubsingleton z
  rw [pathDecoratedEvaluation_def]
  calc _ = z.2.decoration := Fintype.sum_unique _
    _ = x := by
      rw [PathDecoratedRay.decoration_def, Path.homogeneousHistory_nil, LinearMap.id_apply]

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

/-- The single crossing, as the one arrow of the one-object quiver on `Unit`. -/
abbrev crossing : Path (SingleObj.star Unit) (SingleObj.star Unit) :=
  (Path.nil : Path (SingleObj.star Unit) (SingleObj.star Unit)).cons ()

/-- The decorated rays ending at `Q` that cross the wall `{0}` of `ℝ` once. The coorientation
is `u ↦ u`, so a crossing from right to left has forward derivative `-1`, hence the label
contributes `θ`, and the pairing of the normal with the velocity of the decorations has
sign `1`. -/
abbrev Ray (Q : ℝ) :=
  PathDecoratedRay (Q := SingleObj Unit) (M := fun _ => Coefficients) (ι := fun _ => Degree)
    (fun _ => theta) (fun _ => grade ℚ) ((1, 0) : Degree) incoming (fun _ => velocity)
    (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 1) (fun _ => 0) (fun _ => univ)
    (fun _ : Unit => {0}) (fun _ : Empty => ∅) univ crossing Q

/-- The decoration histories of the crossing that survive the sign and velocity conditions. -/
noncomputable abbrev historySupport : Finset (PUnit × Degree) :=
  pathDecoratedHistorySupport (Q := SingleObj Unit) (M := fun _ => Coefficients)
    (ι := fun _ => Degree) (fun _ => theta) (fun _ => grade ℚ) ((1, 0) : Degree) incoming
    (fun _ => velocity) (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 1) crossing

/-- The two segment velocities of a crossing history: after and before the crossing. -/
private theorem dirs_crossing (q : Degree) :
    Path.Degrees.reverseVertexLabels (Q := SingleObj Unit) (ι := fun _ => Degree)
      (fun _ => velocity) ((1, 0) : Degree) crossing ((PUnit.unit, q) : PUnit × Degree) =
      ![velocity q, velocity (1, 0)] := by
  funext j
  fin_cases j
  · exact Path.Degrees.reverseVertexLabels_cons_zero _ _ _ _ _ _
  · exact (Path.Degrees.reverseVertexLabels_cons_succ _ _ _ _ _ _ 0).trans
      (congrFun (Path.Degrees.reverseVertexLabels_nil _ _ _) 0)

/-- The arrow labels of the crossing are those of its single arrow. -/
private theorem reverseArrowLabels_crossing {A : Type*} (g : A) :
    crossing.reverseArrowLabels (fun {_ _ : SingleObj Unit} _ => g) = fun _ => g := by
  funext j
  rw [Path.reverseArrowLabels_cons]
  exact Fin.cases rfl (fun k => k.elim0) j

/-- The history `x ↦ θ x` with final degree `q` has the component of `θ x` in that degree. -/
theorem homogeneousHistory_incoming (q : Degree) :
    crossing.homogeneousHistory (M := fun _ => Coefficients) (ι := fun _ => Degree)
      (fun _ => theta) (fun _ => grade ℚ) ((PUnit.unit, q) : PUnit × Degree) incoming.1 =
      if q = (1, 0) then single (1, 0) 1 else if q = (1, 1) then single (1, 1) 1 else 0 := by
  have hx : theta incoming.1 = single (1, 0) 1 + single (1, 1) 1 := by
    simp [incoming, theta_single_zero]
  have h₀ : (single (1, 0) 1 : Coefficients) ∈ grade ℚ ((1, 0) : Degree) := single_mem_grade _ _
  have h₁ : (single (1, 1) 1 : Coefficients) ∈ grade ℚ ((1, 1) : Degree) := single_mem_grade _ _
  rw [Path.homogeneousHistory_cons_apply, Path.homogeneousHistory_nil, LinearMap.id_apply, hx,
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
theorem historySupport_eq :
    historySupport = {(PUnit.unit, (1, 0)), (PUnit.unit, (1, 1))} := by
  ext ⟨u, q⟩
  cases u
  rw [historySupport, mem_pathDecoratedHistorySupport, homogeneousHistory_incoming,
    dirs_crossing, reverseArrowLabels_crossing, reverseArrowLabels_crossing]
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
private theorem velocity_of_mem_historySupport {d : PUnit × Degree} (hd : d ∈ historySupport) :
    Path.Degrees.reverseVertexLabels (Q := SingleObj Unit) (ι := fun _ => Degree)
      (fun _ => velocity) ((1, 0) : Degree) crossing d = fun _ : Fin 2 => 1 := by
  rw [historySupport_eq, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl <;> rw [dirs_crossing] <;> funext j <;> fin_cases j <;>
    simp [velocity]

/-- The geometric data of the crossing are the constant tuples of the straight line. -/
private theorem mem_domain_iff_neg {d : PUnit × Degree} (hd : d ∈ historySupport) (Q : ℝ) :
    Q ∈ admissibleBackwardDomain
      (crossing.reverseArrowLabels fun {_ _ : SingleObj Unit} _ => ContinuousLinearMap.id ℝ ℝ)
      (crossing.reverseArrowLabels fun {_ _ : SingleObj Unit} _ => (0 : ℝ))
      (Path.Degrees.reverseVertexLabels (Q := SingleObj Unit) (ι := fun _ => Degree)
        (fun _ => velocity) ((1, 0) : Degree) crossing d)
      (crossing.reverseArrowLabels fun {_ _ : SingleObj Unit} _ => (univ : Set ℝ))
      (fun _ : Unit => ({0} : Set ℝ)) (fun _ : Empty => (∅ : Set ℝ)) univ ↔ Q < 0 := by
  rw [reverseArrowLabels_crossing, reverseArrowLabels_crossing, reverseArrowLabels_crossing,
    velocity_of_mem_historySupport hd]
  exact mem_admissibleBackwardDomain_iff_neg Q

/-- No ray ends on the far side of the wall or on it. -/
theorem isEmpty_ray_of_nonneg {Q : ℝ} (hQ : 0 ≤ Q) : IsEmpty (Ray Q) :=
  ⟨fun r => absurd ((mem_domain_iff_neg r.1.2 Q).mp r.2.mem_admissibleBackwardDomain)
    hQ.not_gt⟩

/-- Every history of the support is realized by a ray ending at each point left of the wall. -/
theorem exists_ray_of_neg {Q : ℝ} (hQ : Q < 0) {d : PUnit × Degree}
    (hd : d ∈ historySupport) : ∃ r : Ray Q, r.1.1 = d :=
  ⟨⟨⟨d, hd⟩, admissibleRayRealization _ _ _ _ _ _ _ _ ((mem_domain_iff_neg hd Q).mpr hQ)⟩, rfl⟩

/-- Both rays have velocity `1` before and after the crossing, so each is the line of slope `-1`
in the backward parameter through `Q`. -/
theorem ray_apply_of_nonpos {Q : ℝ} (r : Ray Q) {t : ℝ} (ht : t ≤ 0) : r.2.ray t = Q - t := by
  have hv := velocity_of_mem_historySupport r.1.2
  have h := r.2.ray_eq_endpoint_sub_smul_of_directions_eq
    (fun i => by rw [congrFun hv i, congrFun hv 0]) ht
  simpa only [congrFun hv 0, smul_eq_mul, mul_one] using h

/-- The final decoration of a ray is the component of `θ x` in its degree. -/
theorem decoration_eq {Q : ℝ} (r : Ray Q) :
    r.decoration =
      if r.1.1.2 = (1, 0) then single (1, 0) 1 else if r.1.1.2 = (1, 1) then single (1, 1) 1
      else 0 := by
  rw [PathDecoratedRay.decoration_def, ← homogeneousHistory_incoming]

/-- The possible next decorations at a point left of the wall are exactly `x` and `t x`. -/
theorem range_decoration_eq {Q : ℝ} (hQ : Q < 0) :
    Set.range (fun r : Ray Q => r.decoration) = {single (1, 0) 1, single (1, 1) 1} := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    have hp : r.1.1 ∈ historySupport := r.1.2
    rw [historySupport_eq, Finset.mem_insert, Finset.mem_singleton] at hp
    dsimp only
    rw [decoration_eq]
    rcases hp with hp | hp <;> simp [hp]
  · rintro (rfl | rfl)
    · obtain ⟨r, hr⟩ := exists_ray_of_neg hQ (d := (PUnit.unit, (1, 0)))
        (by simp [historySupport_eq])
      exact ⟨r, by simp [hr, homogeneousHistory_incoming]⟩
    · obtain ⟨r, hr⟩ := exists_ray_of_neg hQ (d := (PUnit.unit, (1, 1)))
        (by simp [historySupport_eq])
      exact ⟨r, by simp [hr, homogeneousHistory_incoming]⟩

/-- The weighted evaluation of the crossing at `Q`, over the inventory of the one crossing. -/
noncomputable abbrev evaluation (Q : ℝ) : Coefficients :=
  pathDecoratedEvaluation (Q := SingleObj Unit) (M := fun _ => Coefficients)
    (ι := fun _ => Degree) (fun _ => theta) (fun _ => grade ℚ) ((1, 0) : Degree) incoming
    {crossing} (fun _ => velocity) (fun _ => ContinuousLinearMap.id ℝ ℝ) (fun _ => 1)
    (fun _ => 0) (fun _ => univ) (fun _ : Unit => {0}) (fun _ : Empty => ∅) univ Q

end DualNumberWall

end Mei
