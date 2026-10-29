/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.ChargeZero
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Classification
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Field
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.LocalConstancy
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.Transport
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Invariance

/-!
# Transport of probe coefficients along base paths

Suppose the charge-zero part of a probe diagram is equivalent, at a relative cutoff,
to the cylinder over a base diagram. Then base projection carries every probe
transport to the base transport between the projected endpoints, whatever the
auxiliary coordinates of those endpoints.

For a consistent probe diagram the endpoint field of probe coefficients is then
transported by the base action: for an admissible base path `γ` between generic
endpoints `Q` and `Q'`, the coefficient at `Q'` is the order-`k` base path product
along `γ` acting on the coefficient at `Q`. The path `γ` may cross arbitrary base
walls. The comparison takes short upward crossings at one common regular height
and joins their endpoints inside thin slabs just above and just below the probe
hyperplane. Charge-one walls lie in level sets of the probe coordinate, so these
slabs meet only walls with lifted base normals, whose labels have no module part.
In particular the field of an outgoing completion of a cylinder input and its probe
wall is transported along admissible paths for any outgoing completion of the base input.

This is the transport of coefficients obtained from the module probe in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*, §3.3.3
(arXiv:1503.06183v5). It combines `ModuleProbe.verticalCoefficient_eq_action_of_paths`
with the charge-zero comparison `DirectedDiagram.levelTransport_map` and
`ModuleProbe.levelTransport_cylinderDiagram`.
-/

public noncomputable section

open Set Filter Topology Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Γ Λ V E ι κ : Type*} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : (ℤ × ℤ) →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h') (wallSpaces d ℳ p ℒ H) ι)
  (B : DirectedDiagram (d := d) h H κ)

local notation "v" => (0, j (0, 1))
local notation "π" => baseQuotientProjection d ℳ p ℒ

/-- If the charge-zero image of a consistent probe diagram is equivalent at order `k`
to the cylinder over a base diagram, then base projection carries each probe path
product to the base path product between the projected endpoints. The auxiliary
coordinates of the two probe endpoints are arbitrary and may differ. -/
theorem baseBCHProjection_levelPathProduct (k : ℕ) (hD : D.LevelConsistent k)
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    {a b : WallComplement (fun c : D.active k => (D.wall c).support)}
    (r : AdmissiblePLPath a b)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (γ : AdmissiblePLPath x y) (ha : a.val.1 = x.val) (hb : b.val.1 = y.val) :
    (π k).bchGroupMap (D.levelPathProduct k r) = B.levelPathProduct k γ := by
  let f := chargeZeroGradedLieHom d ℳ p ℒ
  let hf := chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H
  have hD₀ := hD.map D f hf
  have hC := hB.consistent hD₀
  have hBc := (cylinderDiagram_levelConsistent_iff d ℳ p ℒ H h h' B k).mp hC
  let x' := (cylinderPathLift d ℳ p ℒ H h h' B k a.val.2).obj x
  let y' := (cylinderPathLift d ℳ p ℒ H h h' B k b.val.2).obj y
  have hx' : ((D.mapPathPrefunctor f hf k).obj a).val = x'.val := by
    simp [x', ← ha]
  have hy' : ((D.mapPathPrefunctor f hf k).obj b).val = y'.val := by
    simp [y', ← hb]
  have hpx : (cylinderPathProjection d ℳ p ℒ H h h' B k).obj x' = x :=
    WallComplement.ext (by simp [x'])
  have hpy : (cylinderPathProjection d ℳ p ℒ H h h' B k).obj y' = y :=
    WallComplement.ext (by simp [y'])
  apply LieHom.bchGroupMap_injective
    (Function.LeftInverse.injective (baseQuotientProjection_base d ℳ p ℒ k))
  have he := (D.levelTransport_map f hf hD a b).symm.trans
    ((hB.levelTransport_eq hD₀ hC hx' hy').trans
      (levelTransport_cylinderDiagram d ℳ p ℒ H h h' B hBc x' y'))
  rw [hpx, hpy, B.levelTransport_eq_levelPathProduct hBc γ,
    D.levelTransport_eq_levelPathProduct hD r, truncatedMap_chargeZeroGradedLieHom,
    LieHom.bchGroupMap_comp] at he
  exact he

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- The probe coordinate is constant on the support of every active wall that is not
tangent to the probe direction: such a wall has a nonzero multiple of the probe normal. -/
private theorem realCharacter_probeNormal_eq_of_ne_zero (k : ℕ) (a : D.active k)
    (hv : (h.prod h').realCharacter (D.wall a).normal v ≠ 0)
    {w w' : V × E} (hw : w ∈ (D.wall a).support) (hw' : w' ∈ (D.wall a).support) :
    (h.prod h').realCharacter (probeNormal (Λ := Λ)) w =
      (h.prod h').realCharacter (probeNormal (Λ := Λ)) w' := by
  rcases wallGroup_cases_of_ne_one d ℳ p ℒ H (D.wall a).label_mem
      (D.label_ne_one_of_mem_active a.property) with
    ⟨_, m, _, hm⟩ | ⟨_, _, c, hc, _, hm⟩
  · exact (hv (by simp [hm])).elim
  · have hd : w - w' ∈ (affineSpan ℝ (D.wall a).support).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hw) (subset_affineSpan ℝ _ hw')
    rw [(D.wall a).direction_support, LinearMap.mem_ker, hm, map_zsmul, LinearMap.smul_apply,
      map_sub] at hd
    exact sub_eq_zero.mp ((smul_eq_zero.mp hd).resolve_left hc)

omit [LieAlgebra ℚ L] [IsScalarTower ℚ R L] in
/-- At each cutoff there is a slab width such that thin slabs of probe levels away from
the probe hyperplane meet only walls with lifted base normals. Allowed points in such a
slab are joined by admissible paths whose products have no module part. -/
private theorem exists_pos_forall_exists_levelPathProduct_eq (k : ℕ) :
    ∃ s > 0, ∀ I : Set ℝ, IsOpen I → I.OrdConnected → I ⊆ Ioo (-s) s → (0 : ℝ) ∉ I →
      ∀ z w : WallComplement (fun a : D.active k => (D.wall a).support),
        (h.prod h').realCharacter (probeNormal (Λ := Λ)) z.val ∈ I →
        (h.prod h').realCharacter (probeNormal (Λ := Λ)) w.val ∈ I →
        ∃ q : AdmissiblePLPath z w,
          ((chargeZeroGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
            (D.levelPathProduct k q) = D.levelPathProduct k q := by
  let := h.finiteDimensional
  let := h'.finiteDimensional
  let ζ := (h.prod h').realCharacter (probeNormal (Λ := Λ))
  -- Walls transverse to the probe direction lie at finitely many probe levels.
  let level (a : D.active k) : ℝ := ζ (D.wall a).support_nonempty.some
  obtain ⟨s, hs, hlevel⟩ : ∃ s > 0, ∀ a : D.active k, |level a| < s → level a = 0 := by
    have hfin : (Set.range level \ {0}).Finite := (Set.finite_range level).sdiff
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl 0 (by simp)
    refine ⟨s, hs, fun a ha => ?_⟩
    by_contra hne
    exact hball (by simpa [Real.dist_eq] using ha) ⟨⟨a, rfl⟩, hne⟩
  refine ⟨s, hs, fun I hIo hIc hI hI0 z w hz hw => ?_⟩
  obtain ⟨q, -, hq⟩ := AdmissiblePLPath.exists_length_eq_two_vertices_mem_of_isOpen
    (fun a : D.active k => (D.wall a).isConvexPolyhedron)
    (fun a => (D.wall a).finrank_direction_add_one)
    (hIo.preimage ζ.continuous_of_finiteDimensional) hz hw
  refine ⟨q, D.bchGroupMap_levelPathProduct_eq_self _ k (hIc.convex.linear_preimage ζ) q hq ?_⟩
  rintro a ⟨u, huI, hu⟩
  refine completedMap_chargeZeroGradedLieHom_label_of_normal_mem_range d ℳ p ℒ H h h'
    (D.wall a) ?_
  refine (mem_range_baseNormal _).mpr ⟨normal_height_eq_zero_of_label_ne_one d ℳ p ℒ H h h'
    (D.wall a) (D.label_ne_one_of_mem_active a.property), ?_⟩
  by_contra hz
  have he := realCharacter_probeNormal_eq_of_ne_zero d ℳ p ℒ H h h' D k a
    (by simpa using hz) hu (D.wall a).support_nonempty.some_mem
  have h0 : level a = 0 :=
    hlevel a (abs_lt.mpr (by rw [show level a = ζ u from he.symm]; exact hI huI))
  exact hI0 ((show ζ u = 0 from he.trans h0) ▸ huI)

/-- In a consistent probe diagram, consider a quadrilateral of admissible paths whose two
sides `e` and `f` have trivial base projection and whose other two sides `r₀` and `r₁`
have no module part. Then `r₀` and `r₁` have equal products. -/
private theorem levelPathProduct_eq_of_baseBCHProjection_eq_one (k : ℕ)
    (hD : D.LevelConsistent k)
    {x₀ x₁ y₀ y₁ : WallComplement (fun a : D.active k => (D.wall a).support)}
    (e : AdmissiblePLPath x₀ x₁) (f : AdmissiblePLPath y₀ y₁)
    (r₀ : AdmissiblePLPath x₀ y₀) (r₁ : AdmissiblePLPath x₁ y₁)
    (he : (π k).bchGroupMap (D.levelPathProduct k e) = 1)
    (hf : (π k).bchGroupMap (D.levelPathProduct k f) = 1)
    (hr₀ : ((chargeZeroGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
      (D.levelPathProduct k r₀) = D.levelPathProduct k r₀)
    (hr₁ : ((chargeZeroGradedLieHom d ℳ p ℒ).truncatedMap (a := k) k (by simp)).bchGroupMap
      (D.levelPathProduct k r₁) = D.levelPathProduct k r₁) :
    D.levelPathProduct k r₁ = D.levelPathProduct k r₀ := by
  have hc := congrArg (π k).bchGroupMap
    ((D.levelConsistent_def k).mp hD (e.comp r₁) (r₀.comp f))
  rw [DirectedDiagram.levelPathProduct_comp, DirectedDiagram.levelPathProduct_comp, map_mul,
    map_mul, he, hf, mul_one, one_mul] at hc
  rw [← hr₁, ← hr₀, truncatedMap_chargeZeroGradedLieHom, LieHom.bchGroupMap_comp,
    MonoidHom.comp_apply, MonoidHom.comp_apply, hc]

/-- Transport of the endpoint field of probe coefficients along base paths. Suppose the
charge-zero image of a consistent probe diagram is equivalent at relative order `k` to
the cylinder over a base diagram. Then for every admissible base path between generic
endpoints, the coefficient at the final endpoint is the order-`k` base path product
acting on the coefficient at the initial endpoint. -/
theorem coefficientField_eq_truncatedBCHAction_levelPathProduct (k : ℕ)
    (hD : D.LevelConsistent (k + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) k)
    {x y : WallComplement (fun c : B.active k => (B.wall c).support)}
    (γ : AdmissiblePLPath x y)
    (hx : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric x.val)
    (hy : (coefficientArrangement d ℳ p ℒ H h h' D k).IsGeneric y.val) :
    coefficientField d ℳ p ℒ H h h' D k y.val hy =
      (d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k (B.levelPathProduct k γ)
        (coefficientField d ℳ p ℒ H h h' D k x.val hx) := by
  -- Choose one height regular above both endpoints.
  obtain ⟨t, ht⟩ := ((finite_bad_heights d ℳ p ℒ H h h' D k x.val hx).union
    (finite_bad_heights d ℳ p ℒ H h h' D k y.val hy)).infinite_compl.nonempty
  have hθ : (x.val, t • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
    fun hs => ht (Or.inl (Or.inl hs))
  have hθ' : (y.val, t • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support) :=
    fun hs => ht (Or.inr (Or.inl hs))
  have hv := vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k x.val hx t
  have hv' := vertical_transverse_of_isGeneric d ℳ p ℒ H h h' D k y.val hy t
  -- Short upward crossings at both endpoints, of a common length below the slab width.
  obtain ⟨s, hs, hslab⟩ := exists_pos_forall_exists_levelPathProduct_eq d ℳ p ℒ H h h' D (k + 1)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (s / 2) := Ioo_mem_nhdsGT (half_pos hs)
  obtain ⟨ε, ⟨hε, hεs⟩, ⟨x₀, x₁, e, hx₀, hx₁, he⟩, ⟨y₀, y₁, f, hy₀, hy₁, hf⟩⟩ :=
    (hsmall.and
      ((D.eventually_exists_levelPathProduct_eq_combinedLabel (k + 1) _ v hθ hv).and
        (D.eventually_exists_levelPathProduct_eq_combinedLabel (k + 1) _ v hθ' hv'))).exists
  have hζ (Q : V) (c : ℝ) :
      (h.prod h').realCharacter (probeNormal (Λ := Λ)) ((Q, t • j (1, 0)) + c • v) = c ∧
        (h.prod h').realCharacter (probeNormal (Λ := Λ)) ((Q, t • j (1, 0)) - c • v) = -c := by
    simp [realCharacter_probeNormal h h']
  -- Join the upper and the lower endpoints inside thin slabs.
  obtain ⟨r₁, hr₁⟩ := hslab (Ioo 0 (2 * ε)) isOpen_Ioo ordConnected_Ioo
    (Ioo_subset_Ioo (by linarith) (by linarith)) (by simp) x₁ y₁
    (by rw [hx₁, (hζ _ _).1]; constructor <;> linarith)
    (by rw [hy₁, (hζ _ _).1]; constructor <;> linarith)
  obtain ⟨r₀, hr₀⟩ := hslab (Ioo (-(2 * ε)) 0) isOpen_Ioo ordConnected_Ioo
    (Ioo_subset_Ioo (by linarith) (by linarith)) (by simp) x₀ y₀
    (by rw [hx₀, (hζ _ _).2]; constructor <;> linarith)
    (by rw [hy₀, (hζ _ _).2]; constructor <;> linarith)
  -- Upward crossings carry module labels only, so the two slab paths agree.
  have hπC (Q : V) (hQ : (Q, t • j (1, 0)) ∉
      singularSupport (fun a : D.active (k + 1) => (D.wall a).support))
      (hQv : ∀ a : D.active (k + 1), (Q, t • j (1, 0)) ∈ (D.wall a).support →
        (h.prod h').realCharacter (D.wall a).normal v ≠ 0) :
      (π (k + 1)).bchGroupMap (D.combinedLabel (k + 1) (Q, t • j (1, 0)) v hQ) = 1 := by
    rw [← moduleBCHInclusion_neg_verticalCoefficient d ℳ p ℒ H h h' D k _ hQ hQv]
    exact (baseBCHProjection_eq_one_iff d ℳ p ℒ k _).mpr
      ⟨_, rfl, fun _ hb => moduleBCHInclusion_injective d ℳ p ℒ k hb⟩
  have hr := levelPathProduct_eq_of_baseBCHProjection_eq_one d ℳ p ℒ H h h' D (k + 1) hD
    e.toPath f.toPath r₀ r₁ (he ▸ hπC _ hθ hv) (hf ▸ hπC _ hθ' hv') hr₀ hr₁
  have hmain := verticalCoefficient_eq_action_of_paths d ℳ p ℒ H h h' D k hD _ _ hθ hθ' hv hv'
    e.toPath f.toPath r₀ r₁ he hf hr
  rw [← coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD y.val hy t hθ',
    ← coefficientField_eq_verticalCoefficient d ℳ p ℒ H h h' D k hD x.val hx t hθ] at hmain
  rw [hmain]
  congr 2
  -- Truncate the lower slab transport and compare it with the base path product.
  have hcomm : (d.truncationMap ℒ (Nat.le_succ k)).comp (π (k + 1)) =
      (π k).comp ((positiveDegrees d p).truncationMap (grading d ℳ p ℒ) (Nat.le_succ k)) :=
    LieHom.ext (truncationMap_baseQuotientProjection d ℳ p ℒ (Nat.le_succ k))
  have ht' := DFunLike.congr_fun (congrArg LieHom.bchGroupMap hcomm)
    (D.levelPathProduct (k + 1) r₀)
  simp only [LieHom.bchGroupMap_comp, MonoidHom.comp_apply] at ht'
  rw [ht', D.truncation_levelPathProduct (Nat.le_succ k) r₀]
  exact baseBCHProjection_levelPathProduct d ℳ p ℒ H h h' D B k
    (hD.mono (Nat.le_succ k)) hB _ γ (by simp [hx₀]) (by simp [hy₀])

/-- Transport of the probe coefficient field of an outgoing completion of a cylinder
input and its probe wall: along every admissible path for an outgoing completion of
the base input, the field is transported by the order-`k` base path product. -/
theorem coefficientField_eq_truncatedBCHAction_levelPathProduct_of_isOutgoingCompletion
    {ι₀ κ' : Type*} (D₀ : DirectedDiagram (d := d) h H ι₀)
    (C : DirectedDiagram (d := d) h H (ι₀ ⊕ κ)) (a : ℳ p)
    (F : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
      (wallSpaces d ℳ p ℒ H) ((ι₀ ⊕ Unit) ⊕ κ'))
    (hC : DirectedDiagram.IsOutgoingCompletion D₀.wall C)
    (hF : DirectedDiagram.IsOutgoingCompletion (initialDiagram d ℳ p ℒ H h h' D₀ a).wall F)
    (k : ℕ) {x y : WallComplement (fun c : C.active k => (C.wall c).support)}
    (γ : AdmissiblePLPath x y)
    (hx : (coefficientArrangement d ℳ p ℒ H h h' F k).IsGeneric x.val)
    (hy : (coefficientArrangement d ℳ p ℒ H h h' F k).IsGeneric y.val) :
    coefficientField d ℳ p ℒ H h h' F k y.val hy =
      (d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction d ℒ k (C.levelPathProduct k γ)
        (coefficientField d ℳ p ℒ H h h' F k x.val hx) :=
  coefficientField_eq_truncatedBCHAction_levelPathProduct d ℳ p ℒ H h h' F C k
    ((F.consistent_iff.mp hF.consistent) (k + 1))
    ((DirectedDiagram.equivalent_iff _ _).mp
      (map_chargeZeroGradedLieHom_equivalent_cylinderDiagram_of_isOutgoingCompletion
        d ℳ p ℒ H h h' D₀ C a F hC hF) k) γ hx hy

end Mei.ModuleProbe
