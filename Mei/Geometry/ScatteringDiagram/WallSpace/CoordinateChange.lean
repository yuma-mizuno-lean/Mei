/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.WallSpace.Hom

/-!
# Coordinate changes of directed wall spaces

An algebraic coordinate change identifies the degree groups and tangent monoids, the
positive monoids, the homogeneous Lie pieces and the wall submodules. Normals
transform by the inverse tangent map. The positive degree functions need not
agree: the finite-maximum cutoff modulus gives the maps at finite order.

Coordinate changes induce isomorphisms of completed wall groups, with identity
and composition laws. Supported primitive generators are transported in the
ambient degree group, including generators outside the positive monoid.

The construction uses `PositiveDegreeMap.ofInjectiveOn`,
`SupportedRay.congr` and the wall-preservation API of `GradedLieHom`.
The completed inverse laws use independence of the cutoff modulus for
`GradedLieHom.completedMap`; restriction uses Mathlib's `MulEquiv.subgroupMap`.
-/

public section

namespace Mei.DirectedWallSpaces

universe u

variable {Γ Γ' Γ'' Λ Λ' Λ'' R : Type*} {L L' L'' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Γ'']
  [AddCommMonoid Λ] [AddCommMonoid Λ'] [AddCommMonoid Λ'']
  [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
  [LieRing L''] [LieAlgebra R L'']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'} {ρ'' : Γ'' →+ Λ''}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'} {ℋ : Γ'' → Submodule R L''}
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {p : PositiveDegrees Γ''}
  (H : DirectedWallSpaces ρ ℒ) (H' : DirectedWallSpaces ρ' ℳ)

/-- Algebraic coordinate changes for directed wall spaces. The degree functions
may differ, but the allowed monoids and all wall submodules are identified. -/
structure CoordinateChange where
  /-- The change of degree coordinates. -/
  degreeEquiv : Γ ≃+ Γ'
  /-- The change of tangent coordinates. -/
  tangentEquiv : Λ ≃+ Λ'
  /-- The isomorphism of coefficient Lie algebras. -/
  lieEquiv : L ≃ₗ⁅R⁆ L'
  /-- Allowed degrees are preserved and reflected. -/
  monoid_mem_iff : ∀ n, degreeEquiv n ∈ e.monoid ↔ n ∈ d.monoid
  /-- The degree and tangent maps commute with geometric directions. -/
  map_direction : ∀ n, tangentEquiv (ρ n) = ρ' (degreeEquiv n)
  /-- Homogeneous pieces are identified. -/
  piece_mem_iff : ∀ n x, lieEquiv x ∈ ℳ (degreeEquiv n) ↔ x ∈ ℒ n
  /-- Wall spaces are identified, with contravariant transport of normals. -/
  wall_mem_iff : ∀ n m x,
    lieEquiv x ∈ H'.wall (degreeEquiv n) (m.comp tangentEquiv.symm) ↔
      x ∈ H.wall n m

namespace CoordinateChange

variable {H H'} {H'' : DirectedWallSpaces ρ'' ℋ}

/-- A coordinate change is determined by its three equivalences. -/
@[ext]
theorem ext {E F : CoordinateChange (d := d) (e := e) H H'}
    (hΓ : E.degreeEquiv = F.degreeEquiv) (hΛ : E.tangentEquiv = F.tangentEquiv)
    (hL : E.lieEquiv = F.lieEquiv) : E = F := by
  cases E
  cases F
  congr

/-- Identity coordinates preserve every directed wall space. -/
def refl (H : DirectedWallSpaces ρ ℒ) : CoordinateChange (d := d) (e := d) H H where
  degreeEquiv := AddEquiv.refl Γ
  tangentEquiv := AddEquiv.refl Λ
  lieEquiv := LieEquiv.refl
  monoid_mem_iff _ := Iff.rfl
  map_direction _ := rfl
  piece_mem_iff _ _ := Iff.rfl
  wall_mem_iff _ _ _ := by simp

/-- Invert the degree, tangent and Lie coordinate maps. -/
def symm (E : CoordinateChange (d := d) (e := e) H H') :
    CoordinateChange (d := e) (e := d) H' H where
  degreeEquiv := E.degreeEquiv.symm
  tangentEquiv := E.tangentEquiv.symm
  lieEquiv := E.lieEquiv.symm
  monoid_mem_iff n := by simpa using (E.monoid_mem_iff (E.degreeEquiv.symm n)).symm
  map_direction n := by
    apply E.tangentEquiv.injective
    simpa using (E.map_direction (E.degreeEquiv.symm n)).symm
  piece_mem_iff n x := by
    simpa using (E.piece_mem_iff (E.degreeEquiv.symm n) (E.lieEquiv.symm x)).symm
  wall_mem_iff n m x := by
    simpa [AddMonoidHom.comp_assoc] using
      (E.wall_mem_iff (E.degreeEquiv.symm n) (m.comp E.tangentEquiv)
        (E.lieEquiv.symm x)).symm

/-- Compose coordinate changes, applying the left one first. -/
def trans (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    CoordinateChange (d := d) (e := p) H H'' where
  degreeEquiv := E.degreeEquiv.trans F.degreeEquiv
  tangentEquiv := E.tangentEquiv.trans F.tangentEquiv
  lieEquiv := E.lieEquiv.trans F.lieEquiv
  monoid_mem_iff n := (F.monoid_mem_iff _).trans (E.monoid_mem_iff n)
  map_direction n := by simp [E.map_direction, F.map_direction]
  piece_mem_iff n x := (F.piece_mem_iff _ _).trans (E.piece_mem_iff n x)
  wall_mem_iff n m x := by
    have hn : m.comp (E.tangentEquiv.trans F.tangentEquiv).symm =
        (m.comp (E.tangentEquiv.symm : Λ' →+ Λ)).comp
          (F.tangentEquiv.symm : Λ'' →+ Λ') := by ext v; rfl
    rw [hn]
    exact (F.wall_mem_iff _ _ _).trans (E.wall_mem_iff n m x)

@[simp]
theorem refl_degreeEquiv : (refl (d := d) H).degreeEquiv = AddEquiv.refl Γ := (rfl)

@[simp]
theorem refl_tangentEquiv : (refl (d := d) H).tangentEquiv = AddEquiv.refl Λ := (rfl)

@[simp]
theorem refl_lieEquiv : (refl (d := d) H).lieEquiv = LieEquiv.refl := (rfl)

@[simp]
theorem symm_degreeEquiv (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.degreeEquiv = E.degreeEquiv.symm := (rfl)

@[simp]
theorem symm_tangentEquiv (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.tangentEquiv = E.tangentEquiv.symm := (rfl)

@[simp]
theorem symm_lieEquiv (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.lieEquiv = E.lieEquiv.symm := (rfl)

@[simp]
theorem trans_degreeEquiv (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    (E.trans F).degreeEquiv = E.degreeEquiv.trans F.degreeEquiv := (rfl)

@[simp]
theorem trans_tangentEquiv (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    (E.trans F).tangentEquiv = E.tangentEquiv.trans F.tangentEquiv := (rfl)

@[simp]
theorem trans_lieEquiv (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    (E.trans F).lieEquiv = E.lieEquiv.trans F.lieEquiv := (rfl)

/-- Inversion twice recovers the coordinate change. -/
@[simp]
theorem symm_symm (E : CoordinateChange (d := d) (e := e) H H') : E.symm.symm = E := by
  apply ext <;> rfl

/-- Composing on the right with identity coordinates changes nothing. -/
@[simp]
theorem trans_refl (E : CoordinateChange (d := d) (e := e) H H') : E.trans (refl H') = E := by
  apply ext <;> ext x <;> rfl

/-- Composing on the left with identity coordinates changes nothing. -/
@[simp]
theorem refl_trans (E : CoordinateChange (d := d) (e := e) H H') : (refl H).trans E = E := by
  apply ext <;> ext x <;> rfl

/-- Composing a coordinate change with its inverse gives identity coordinates. -/
@[simp]
theorem self_trans_symm (E : CoordinateChange (d := d) (e := e) H H') :
    E.trans E.symm = refl H := by
  apply ext <;> ext x <;> simp

/-- The inverse coordinate change is also a left inverse. -/
@[simp]
theorem symm_trans_self (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.trans E = refl H' := by
  apply ext <;> ext x <;> simp

/-- The finite-maximum source cutoff of a coordinate change. -/
noncomputable def degreeMap (E : CoordinateChange (d := d) (e := e) H H') :
    PositiveDegreeMap d e :=
  .ofInjectiveOn E.degreeEquiv
    (fun n hn => (E.monoid_mem_iff n).mpr hn) E.degreeEquiv.injective.injOn

/-- The positive degree map has the original coordinate map as its underlying function. -/
@[simp]
theorem degreeMap_apply (E : CoordinateChange (d := d) (e := e) H H') (n : Γ) :
    E.degreeMap n = E.degreeEquiv n := by
  exact PositiveDegreeMap.ofInjectiveOn_apply _ _ _ n

/-- The modulus is the least source cutoff covering the inverse target cutoff. -/
theorem degreeMap_modulus_le_iff (E : CoordinateChange (d := d) (e := e) H H') (k l : ℕ) :
    E.degreeMap.modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree (E.degreeEquiv n) ≤ k → d.degree n ≤ l :=
  PositiveDegreeMap.ofInjectiveOn_modulus_le_iff _ _ _ k l

/-- The graded Lie map associated to a coordinate change, with its cutoff modulus. -/
noncomputable def gradedLieHom (E : CoordinateChange (d := d) (e := e) H H') :
    GradedLieHom E.degreeMap ℒ ℳ where
  toLieHom := E.lieEquiv.toLieHom
  map_mem hx := by simpa using (E.piece_mem_iff _ _).mpr hx

/-- The graded map acts by the original Lie equivalence. -/
@[simp]
theorem gradedLieHom_apply (E : CoordinateChange (d := d) (e := e) H H') (x : L) :
    E.gradedLieHom x = E.lieEquiv x := (rfl)

/-- The supported-ray comparison induced by the degree coordinate change. -/
def rayEquiv (E : CoordinateChange (d := d) (e := e) H H') :
    SupportedRay d ≃ SupportedRay e := SupportedRay.congr E.degreeEquiv E.monoid_mem_iff

/-- The target primitive generator is exactly the image of the source generator. -/
@[simp]
theorem rayEquiv_generator (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) : (E.rayEquiv w).generator = E.degreeEquiv w.generator :=
  SupportedRay.congr_generator _ _ w

/-- Coordinate changes identify the actual allowed degrees on each supported ray. -/
@[simp]
theorem mem_rayDegrees_rayEquiv (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (n : Γ) :
    E.degreeEquiv n ∈ (E.rayEquiv w).rayDegrees ↔ n ∈ w.rayDegrees :=
  SupportedRay.mem_rayDegrees_congr _ _ w n

/-- Identity coordinates fix supported rays. -/
@[simp]
theorem rayEquiv_refl : (refl (d := d) H).rayEquiv = Equiv.refl (SupportedRay d) :=
  SupportedRay.congr_refl

/-- The inverse coordinate change gives the inverse ray comparison. -/
@[simp]
theorem rayEquiv_symm (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.rayEquiv = E.rayEquiv.symm := by
  apply Equiv.ext
  intro w
  apply SupportedRay.ext
  simp [rayEquiv]

/-- Supported-ray comparisons respect composition of coordinate changes. -/
@[simp]
theorem rayEquiv_trans (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    (E.trans F).rayEquiv = E.rayEquiv.trans F.rayEquiv := by
  apply Equiv.ext
  intro w
  apply SupportedRay.ext
  simp

variable [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Γ'']
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading e ℳ] [IsPositiveGrading p ℋ]

/-- At finite order a coordinate change preserves the supported-ray Lie images,
using any source cutoff at least as large as its canonical modulus. -/
theorem truncatedMap_mem (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ) {a k : ℕ} (ha : E.degreeMap.modulus k ≤ a)
    {x : d.truncatedLie ℒ a} (hx : x ∈ H.truncatedRayLieSubalgebra w m a) :
    E.gradedLieHom.truncatedMap k ha x ∈ H'.truncatedRayLieSubalgebra
      (E.rayEquiv w) (m.comp E.tangentEquiv.symm) k :=
  E.gradedLieHom.truncatedMap_mem_truncatedRayLieSubalgebra
    (fun n hn => by simpa using (E.mem_rayDegrees_rayEquiv w n).mpr hn)
    (fun n _ x hx => by simpa using (E.wall_mem_iff n m x).mpr hx) ha hx

variable [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']

/-- The completed map of a coordinate change followed by its inverse is identity,
even though the two finite cutoff moduli need not be inverse functions. -/
private theorem completedMap_symm_comp (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.gradedLieHom.completedMap.comp E.gradedLieHom.completedMap =
      MonoidHom.id (d.completedBCHGroup ℒ) := by
  rw [← GradedLieHom.completedMap_comp]
  exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
    (by ext x; simp [symm])).trans GradedLieHom.completedMap_id

/-- Coordinate changes preserve and reflect completed wall-group membership. -/
theorem completedMap_mem_wallGroup_iff (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ) (g : d.completedBCHGroup ℒ) :
    E.gradedLieHom.completedMap g ∈ H'.wallGroup (E.rayEquiv w)
      (m.comp E.tangentEquiv.symm) ↔ g ∈ H.wallGroup w m := by
  constructor
  · intro hg
    have h := E.symm.gradedLieHom.completedMap_mem_wallGroup
      (w := E.rayEquiv w) (v := w)
      (fun n hn => by
        simpa [symm] using (E.mem_rayDegrees_rayEquiv w (E.degreeEquiv.symm n)).mp
          (by simpa using hn))
      (fun n _ x hx => by
        simp only [gradedLieHom_apply, degreeMap_apply]
        simpa [symm, AddMonoidHom.comp_assoc] using (E.symm.wall_mem_iff n _ x).mpr hx) hg
    have hinv := DFunLike.congr_fun E.completedMap_symm_comp g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hinv
    rw [hinv] at h
    simpa [symm, AddMonoidHom.comp_assoc] using h
  · exact E.gradedLieHom.completedMap_mem_wallGroup
      (fun n hn => by simpa using (E.mem_rayDegrees_rayEquiv w n).mpr hn)
      (fun n _ x hx => by simpa using (E.wall_mem_iff n m x).mpr hx)

/-- The ambient completed BCH groups are identified by a coordinate change.
The inverse uses the reverse finite-maximum cutoff comparison. -/
noncomputable def completedEquiv (E : CoordinateChange (d := d) (e := e) H H') :
    d.completedBCHGroup ℒ ≃* e.completedBCHGroup ℳ :=
  E.gradedLieHom.completedMap.toMulEquiv E.symm.gradedLieHom.completedMap
    E.completedMap_symm_comp (by
      have h := E.symm.completedMap_symm_comp
      rw [symm_symm] at h
      exact h)

/-- The coordinate comparison is the existing graded completed map. -/
@[simp]
theorem completedEquiv_apply (E : CoordinateChange (d := d) (e := e) H H')
    (g : d.completedBCHGroup ℒ) : E.completedEquiv g = E.gradedLieHom.completedMap g := (rfl)

/-- The inverse comparison is the graded completed map of the inverse coordinates. -/
@[simp]
theorem completedEquiv_symm_apply (E : CoordinateChange (d := d) (e := e) H H')
    (g : e.completedBCHGroup ℳ) :
    E.completedEquiv.symm g = E.symm.gradedLieHom.completedMap g := (rfl)

/-- Identity coordinates act identically on the completed BCH group. -/
@[simp]
theorem completedEquiv_refl : (refl (d := d) H).completedEquiv =
    MulEquiv.refl (d.completedBCHGroup ℒ) := by
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun
    ((GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
      (by ext x; simp)).trans GradedLieHom.completedMap_id) g

/-- Inverting coordinates inverts the completed comparison. -/
@[simp]
theorem completedEquiv_symm (E : CoordinateChange (d := d) (e := e) H H') :
    E.symm.completedEquiv = E.completedEquiv.symm := by
  apply MulEquiv.ext
  intro g
  rfl

/-- Successive coordinate comparisons compose, independently of the chosen cutoffs. -/
@[simp]
theorem completedEquiv_trans (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'') :
    (E.trans F).completedEquiv = E.completedEquiv.trans F.completedEquiv := by
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun
    ((GradedLieHom.completedMap_eq_of_toLieHom_eq (E.trans F).gradedLieHom
      (F.gradedLieHom.comp E.gradedLieHom) (by ext x; simp)).trans
        (GradedLieHom.completedMap_comp _ _)) g

/-- A coordinate change carries a wall group onto the group of the transported
primitive ray and inverse-dual normal. -/
@[simp]
theorem map_wallGroup (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    (H.wallGroup w m).map E.completedEquiv =
      H'.wallGroup (E.rayEquiv w) (m.comp E.tangentEquiv.symm) := by
  ext g
  rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map_equiv]
  simpa only [← completedEquiv_apply, MulEquiv.apply_symm_apply] using
    (E.completedMap_mem_wallGroup_iff w m (E.completedEquiv.symm g)).symm

/-- The induced isomorphism of completed wall groups, on their existing carriers. -/
noncomputable def wallGroupEquiv (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ) :
    H.wallGroup w m ≃*
      H'.wallGroup (E.rayEquiv w) (m.comp E.tangentEquiv.symm) :=
  (E.completedEquiv.subgroupMap (H.wallGroup w m)).trans
    (MulEquiv.subgroupCongr (E.map_wallGroup w m))

/-- The wall-group comparison is the restriction of the ambient completed map. -/
@[simp]
theorem coe_wallGroupEquiv_apply (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ) (g : H.wallGroup w m) :
    (E.wallGroupEquiv w m g : e.completedBCHGroup ℳ) = E.completedEquiv g := (rfl)

/-- The inverse wall-group comparison is the inverse ambient completed map. -/
@[simp]
theorem coe_wallGroupEquiv_symm_apply (E : CoordinateChange (d := d) (e := e) H H')
    (w : SupportedRay d) (m : Λ →+ ℤ)
    (g : H'.wallGroup (E.rayEquiv w) (m.comp E.tangentEquiv.symm)) :
    ((E.wallGroupEquiv w m).symm g : d.completedBCHGroup ℒ) = E.completedEquiv.symm g := by
  apply E.completedEquiv.injective
  rw [← coe_wallGroupEquiv_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- Transporting a wall label successively agrees with the composite coordinate
change, in the ambient completed group. -/
theorem coe_wallGroupEquiv_trans (E : CoordinateChange (d := d) (e := e) H H')
    (F : CoordinateChange (d := e) (e := p) H' H'')
    (w : SupportedRay d) (m : Λ →+ ℤ) (g : H.wallGroup w m) :
    ((E.trans F).wallGroupEquiv w m g : p.completedBCHGroup ℋ) =
      (F.wallGroupEquiv (E.rayEquiv w) (m.comp E.tangentEquiv.symm)
        (E.wallGroupEquiv w m g) : p.completedBCHGroup ℋ) := by
  simp only [coe_wallGroupEquiv_apply, completedEquiv_trans, MulEquiv.trans_apply]

end CoordinateChange
end Mei.DirectedWallSpaces
