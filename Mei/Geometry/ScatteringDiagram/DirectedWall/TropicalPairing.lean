/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.FiniteIndex
public import Mei.Algebra.PositiveDegrees.FiniteAlphabet
public import Mei.Geometry.ScatteringDiagram.DirectedWall.Pushforward
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.Pairing
public import Mei.Geometry.Toric.Algebraic.Lattice.FiniteIndex

/-!
# Pushing tropical vertex walls along tropical pairings

A tropical pairing `(T, S)` on all characters, together with a map `ν` of integral normals
compatible with `S` up to scalars and a spatial affine equivalence compatible with `T` and
`ν`, gives `DirectedWall.Pushforward` data between the tropical vertex wall spaces
(`DirectedWall.Pushforward.ofTropicalPairing`). Supported rays are reindexed by
`SupportedRay.map` along `T`. Hence walls and diagrams labelled in the tropical vertex
group are pushed forward with all the transport theorems of `DirectedWall.Pushforward` and
`DirectedDiagram.pushforward`: incomingness, outgoingness, path products, consistency,
equivalence and outgoing completions.

Two cases supply the spatial data.

* `DirectedWall.Pushforward.ofTropicalDegreeMap`: a positive degree map between two degree
  lattices projecting to a common tangent lattice, compatibly on allowed degrees. Normals and
  supports are unchanged. The finite alphabet lift `PositiveDegrees.finiteAlphabetLift` is
  such a map (`DirectedWall.Pushforward.ofFiniteAlphabetLift`): its walls are the same walls
  of the common spatial space.
* `DirectedWall.Pushforward.ofFiniteIndex`: an injective tangent map `t` with finite-index
  image and a positive degree map compatible with it. Characters move by the rational inverse
  dual, supports by the real extension of `t`
  (`TauCeti.Toric.IsIntegralLattice.extendContinuousAffineEquivOfFiniteIndex`), and an
  integral normal `m` by any integral normal `ν m` with `ν m ∘ t = q • m`, `q > 0` rational.
  The label of `z^n ∂_m` becomes `q⁻¹ • z^{T n} ∂_{ν m}`: the integral normal is kept and the
  denominator goes into the label (`DirectedWall.Pushforward.coe_ofFiniteIndex_lieHom_single`).
  The index multiple `m ∘ t.indexInverse` of the inverse dual is always such a normal, with
  `q` the index (`AddMonoidHom.comp_indexInverse_apply_map`).

Only the pushforward data are constructed here. Identifying the pushed walls with a given
input, for instance the image of the ray factors of a finite alphabet function wall, is not
done.

The tropical vertex group and its maps along pairings are those of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.DirectedWall.Pushforward

open LogarithmicVectorField TauCeti.Toric

universe u

variable {R Γ Λ Γ' Λ' : Type u} {V V' : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup Γ] [AddCommGroup Λ] [AddCommGroup Γ'] [AddCommGroup Λ'] [Module.Free ℤ Γ']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {i : Λ →+ V} {i' : Λ' →+ V'} {h : IsIntegralLattice i} {h' : IsIntegralLattice i'}

section OfTropicalPairing

variable (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') (⊤ : Submodule R (Λ →+ R)))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ))
  (hν : ∀ m, p.characterMap ⟨(Int.castAddHom R).comp m, Submodule.mem_top⟩ ∈
    R ∙ (Int.castAddHom R).comp (ν m))
  (A : V ≃ᴬ[ℝ] V')
  (hA : ∀ n ∈ d.monoid, i' (ρ' (p.degreeMap n)) = A.toAffineEquiv.linear (i (ρ n)))
  (hνA : ∀ m, ∃ r : ℚ, 0 < r ∧
    (h'.realCharacter (ν m)).comp A.toAffineEquiv.linear.toLinearMap = (r : ℝ) • h.realCharacter m)

/-- Pushforward data between tropical vertex wall spaces from a tropical pairing on all
characters, a compatible map of integral normals and a compatible spatial equivalence. -/
def ofTropicalPairing :
    Pushforward d e h h' (tropicalVertexWallSpaces (R := R) d ρ) (tropicalVertexWallSpaces e ρ')
    where
  degreeMap := p.degreeMap
  lieHom := p.tropicalVertexGradedLieHom
  rayMap w := w.map p.degreeMap.toAddMonoidHom (fun _ hn => p.degreeMap.map_mem hn)
    (fun _ hn h0 => p.degreeMap.map_ne_zero hn h0)
  mem_rayDegrees_rayMap w _ hn := w.map_mem_rayDegrees _ _ _ hn
  normalMap := ν
  wall_mem _ _ _ _ hx := p.tropicalVertexGradedLieHom_mem_wall ν hν hx
  spatialMap := A
  map_direction := hA
  realCharacter_normalMap := hνA

/-- The degree map is that of the pairing. -/
@[simp]
theorem ofTropicalPairing_degreeMap :
    (ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA).degreeMap = p.degreeMap := (rfl)

/-- The Lie map is that of the pairing on the full tropical vertex Lie algebra. -/
@[simp]
theorem ofTropicalPairing_lieHom_apply (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    (ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA).lieHom x =
      p.tropicalVertexGradedLieHom x := (rfl)

/-- Supported rays are reindexed along the degree map. -/
@[simp]
theorem ofTropicalPairing_rayMap (w : SupportedRay d) :
    (ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA).rayMap w =
      w.map p.degreeMap.toAddMonoidHom (fun _ hn => p.degreeMap.map_mem hn)
        (fun _ hn h0 => p.degreeMap.map_ne_zero hn h0) := (rfl)

/-- The normal map is the given map of integral normals. -/
@[simp]
theorem ofTropicalPairing_normalMap (m : Λ →+ ℤ) :
    (ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA).normalMap m = ν m := (rfl)

/-- The spatial map is the given affine equivalence. -/
@[simp]
theorem ofTropicalPairing_spatialMap :
    (ofTropicalPairing (h := h) (h' := h') p ν hν A hA hνA).spatialMap = A := (rfl)

end OfTropicalPairing

section OfTropicalDegreeMap

variable {ρ' : Γ' →+ Λ} (T : PositiveDegreeMap d e) (hT : ∀ n ∈ d.monoid, ρ' (T n) = ρ n)

/-- Pushforward data along a positive degree map between degree lattices projecting to a
common tangent lattice, compatibly on allowed degrees. Characters, normals and supports are
unchanged. -/
def ofTropicalDegreeMap :
    Pushforward d e h h (tropicalVertexWallSpaces (R := R) d ρ) (tropicalVertexWallSpaces e ρ') :=
  ofTropicalPairing (TropicalPairing.ofDegreeMap T hT ⊤) id
    (fun _ => by
      rw [TropicalPairing.ofDegreeMap_characterMap]
      exact Submodule.mem_span_singleton_self _)
    (ContinuousAffineEquiv.refl ℝ V)
    (fun n hn => by
      rw [ContinuousAffineEquiv.toAffineEquiv_refl, AffineEquiv.linear_refl, LinearEquiv.refl_apply,
        TropicalPairing.ofDegreeMap_degreeMap, hT n hn])
    (fun _ => ⟨1, one_pos, by ext; simp⟩)

/-- The degree map is the given positive degree map. -/
@[simp]
theorem ofTropicalDegreeMap_degreeMap :
    (ofTropicalDegreeMap (R := R) (h := h) T hT).degreeMap = T := by
  rw [ofTropicalDegreeMap, ofTropicalPairing_degreeMap, TropicalPairing.ofDegreeMap_degreeMap]

/-- The Lie map is that of the pairing `TropicalPairing.ofDegreeMap` on the full tropical vertex
Lie algebra. -/
@[simp]
theorem ofTropicalDegreeMap_lieHom_apply (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    (ofTropicalDegreeMap (h := h) T hT).lieHom x =
      (TropicalPairing.ofDegreeMap T hT ⊤).tropicalVertexGradedLieHom x := by
  rw [ofTropicalDegreeMap, ofTropicalPairing_lieHom_apply]

/-- On a homogeneous field `z^n ∂_m`, the Lie map gives `z^{T n} ∂_m`. -/
theorem coe_ofTropicalDegreeMap_lieHom_of_homogeneous {n : Γ}
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (m : Λ →+ R) (hm : single ρ n m = x.val) :
    ((ofTropicalDegreeMap (h := h) T hT).lieHom x).val = single ρ' (T n) m := by
  rw [ofTropicalDegreeMap, ofTropicalPairing_lieHom_apply,
    TropicalPairing.coe_tropicalVertexGradedLieHom_of_homogeneous _ x m hm,
    TropicalPairing.ofDegreeMap_degreeMap, TropicalPairing.ofDegreeMap_characterMap]

/-- Supported rays are reindexed along the positive degree map. -/
@[simp]
theorem ofTropicalDegreeMap_rayMap (w : SupportedRay d) :
    (ofTropicalDegreeMap (R := R) (h := h) T hT).rayMap w =
      w.map T.toAddMonoidHom (fun _ hn => T.map_mem hn) (fun _ hn h0 => T.map_ne_zero hn h0) := by
  simp only [ofTropicalDegreeMap, ofTropicalPairing_rayMap, TropicalPairing.ofDegreeMap_degreeMap]

/-- Normals are unchanged. -/
@[simp]
theorem ofTropicalDegreeMap_normalMap (m : Λ →+ ℤ) :
    (ofTropicalDegreeMap (R := R) (h := h) T hT).normalMap m = m := (rfl)

/-- Supports are unchanged. -/
@[simp]
theorem ofTropicalDegreeMap_spatialMap :
    (ofTropicalDegreeMap (R := R) (h := h) T hT).spatialMap = ContinuousAffineEquiv.refl ℝ V :=
  (rfl)

/-- The pushforward along a degree map over a common tangent lattice is the pushforward along
the pairing `TropicalPairing.ofDegreeMap` with the identity map of normals and the identity
spatial map. -/
theorem ofTropicalDegreeMap_eq_ofTropicalPairing :
    ofTropicalDegreeMap (R := R) (h := h) T hT =
      ofTropicalPairing (TropicalPairing.ofDegreeMap T hT ⊤) id
        (fun _ => by
          rw [TropicalPairing.ofDegreeMap_characterMap]
          exact Submodule.mem_span_singleton_self _)
        (ContinuousAffineEquiv.refl ℝ V)
        (fun n hn => by
          rw [ContinuousAffineEquiv.toAffineEquiv_refl, AffineEquiv.linear_refl,
            LinearEquiv.refl_apply, TropicalPairing.ofDegreeMap_degreeMap, hT n hn])
        (fun _ => ⟨1, one_pos, by ext; simp⟩) := by
  refine Pushforward.ext ?_ (fun x => ?_) (funext fun w => ?_) (funext fun m => ?_) ?_
  · simp
  · simp
  · simp
  · simp
  · simp

end OfTropicalDegreeMap

section OfFiniteIndex

variable (T : PositiveDegreeMap d e) (t : Λ →+ Λ') (ht : Function.Injective t)
  [t.range.FiniteIndex] (hρ : ∀ n ∈ d.monoid, ρ' (T n) = t (ρ n))
  (ν : (Λ →+ ℤ) → (Λ' →+ ℤ)) (q : (Λ →+ ℤ) → ℚ) (hq : ∀ m, 0 < q m)
  (hν : ∀ m x, (ν m (t x) : ℚ) = q m * m x)

/-- Pushforward data along a finite-index tangent embedding `t` with a compatible positive
degree map. Characters move by the rational inverse dual, supports by the real extension of
`t`, and a normal `m` by an integral normal `ν m` with `ν m ∘ t = q m • m`. -/
def ofFiniteIndex :
    Pushforward d e h h' (tropicalVertexWallSpaces (R := R) d ρ) (tropicalVertexWallSpaces e ρ') :=
  ofTropicalPairing (TropicalPairing.ofFiniteIndex T t ht hρ ⊤) ν
    (fun m => by
      rw [TropicalPairing.ofFiniteIndex_characterMap,
        t.rationalDualEquiv_intCast_comp ht (hq m).ne' (hν m), ← algebraMap_smul R]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    (h.extendContinuousAffineEquivOfFiniteIndex h' t ht)
    (fun n hn => by
      rw [TropicalPairing.ofFiniteIndex_degreeMap, hρ n hn,
        IsIntegralLattice.extendContinuousAffineEquivOfFiniteIndex_linear,
        IsIntegralLattice.coe_extendEquivOfFiniteIndex, IsIntegralLattice.extend_apply])
    (fun m => ⟨q m, hq m, by
      rw [IsIntegralLattice.extendContinuousAffineEquivOfFiniteIndex_linear,
        IsIntegralLattice.extendEquivOfFiniteIndex_toLinearMap]
      exact h.realCharacter_comp_extend h' t (hν m)⟩)

/-- The degree map is the given positive degree map. -/
@[simp]
theorem ofFiniteIndex_degreeMap :
    (ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν).degreeMap = T := by
  rw [ofFiniteIndex, ofTropicalPairing_degreeMap, TropicalPairing.ofFiniteIndex_degreeMap]

/-- Supported rays are reindexed along the positive degree map. -/
@[simp]
theorem ofFiniteIndex_rayMap (w : SupportedRay d) :
    (ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν).rayMap w =
      w.map T.toAddMonoidHom (fun _ hn => T.map_mem hn) (fun _ hn h0 => T.map_ne_zero hn h0) := by
  simp only [ofFiniteIndex, ofTropicalPairing_rayMap, TropicalPairing.ofFiniteIndex_degreeMap]

/-- The normal map is the given map of integral normals. -/
@[simp]
theorem ofFiniteIndex_normalMap (m : Λ →+ ℤ) :
    (ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν).normalMap m = ν m := (rfl)

/-- Supports move by the real extension of the tangent embedding. -/
@[simp]
theorem ofFiniteIndex_spatialMap :
    (ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν).spatialMap =
      h.extendContinuousAffineEquivOfFiniteIndex h' t ht := (rfl)

/-- On a homogeneous field `z^n ∂_m`, the Lie map gives `z^{T n} ∂_{m'}`, where `m'` is the
rational inverse dual of `m`. -/
theorem coe_ofFiniteIndex_lieHom_of_homogeneous {n : Γ}
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (m : Λ →+ R) (hm : single ρ n m = x.val) :
    ((ofFiniteIndex (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom x).val =
      single ρ' (T n) (t.rationalDualEquiv ht m) := by
  rw [ofFiniteIndex, ofTropicalPairing_lieHom_apply,
    TropicalPairing.coe_tropicalVertexGradedLieHom_of_homogeneous _ x m hm,
    TropicalPairing.ofFiniteIndex_characterMap, TropicalPairing.ofFiniteIndex_degreeMap]

/-- The field `z^n ∂_m` of an integral normal is sent to `q⁻¹ • z^{T n} ∂_{ν m}`: the
integral normal `ν m` is kept and the denominator goes into the label. -/
theorem coe_ofFiniteIndex_lieHom_single {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0)
    (m : Λ →+ ℤ) (hm : m (ρ n) = 0) :
    ((ofFiniteIndex (R := R) (h := h) (h' := h') T t ht hρ ν q hq hν).lieHom
        ⟨single ρ n ((Int.castAddHom R).comp m),
          single_mem_tropicalVertexLieAlgebra d ρ hn hne _ (by simp [hm])⟩).val =
      algebraMap ℚ R (q m)⁻¹ • single ρ' (T n) ((Int.castAddHom R).comp (ν m)) := by
  rw [coe_ofFiniteIndex_lieHom_of_homogeneous T t ht hρ ν q hq hν _ _ rfl,
    t.rationalDualEquiv_intCast_comp ht (hq m).ne' (hν m), ← algebraMap_smul R, map_smul]

end OfFiniteIndex

section OfFiniteAlphabetLift

variable {M E L : Type u} [AddCommGroup M] [Fintype E] [DecidableEq E] [AddCommGroup L]
  [Module.Free ℤ L] {m : E → M} {f : PositiveDegrees L} {τ : M × (E → ℤ) →+ L}
  (hτ : ∀ α, τ (PositiveDegrees.letter m α) ∈ f.monoid)
  (hτ0 : ∀ α, τ (PositiveDegrees.letter m α) ≠ 0)
  {π : L →+ M} (hπ : ∀ α, π (τ (PositiveDegrees.letter m α)) = m α)
  {j : M →+ V} {g : IsIntegralLattice j}

/-- Pushforward data along a finite alphabet lift `τ`, from the alphabet `M × (E → ℤ)`
projecting to `M` by the first coordinate to degrees `L` projecting to `M` by `π`. The walls
stay the same walls of the common spatial space of `M`. -/
def ofFiniteAlphabetLift :
    Pushforward (PositiveDegrees.finiteAlphabet m) f g g
      (tropicalVertexWallSpaces (R := R) (PositiveDegrees.finiteAlphabet m)
        (AddMonoidHom.fst M (E → ℤ)))
      (tropicalVertexWallSpaces f π) :=
  ofTropicalDegreeMap (PositiveDegrees.finiteAlphabetLift m hτ hτ0) (fun _ hx => by
    rw [PositiveDegrees.finiteAlphabetLift_apply]
    exact PositiveDegrees.eq_fst_of_eq_sum m (σ := π.comp τ) hπ
      ((PositiveDegrees.mem_finiteAlphabet_monoid m).mp hx).2)

/-- The degree map is the finite alphabet lift. -/
@[simp]
theorem ofFiniteAlphabetLift_degreeMap :
    (ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ).degreeMap =
      PositiveDegrees.finiteAlphabetLift m hτ hτ0 := by
  rw [ofFiniteAlphabetLift, ofTropicalDegreeMap_degreeMap]

/-- Supported rays are reindexed along the finite alphabet lift. -/
@[simp]
theorem ofFiniteAlphabetLift_rayMap (w : SupportedRay (PositiveDegrees.finiteAlphabet m)) :
    (ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ).rayMap w =
      w.map (PositiveDegrees.finiteAlphabetLift m hτ hτ0).toAddMonoidHom
        (fun _ hn => (PositiveDegrees.finiteAlphabetLift m hτ hτ0).map_mem hn)
        (fun _ hn h0 => (PositiveDegrees.finiteAlphabetLift m hτ hτ0).map_ne_zero hn h0) := by
  rw [ofFiniteAlphabetLift, ofTropicalDegreeMap_rayMap]

/-- Normals are unchanged. -/
@[simp]
theorem ofFiniteAlphabetLift_normalMap (μ : M →+ ℤ) :
    (ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ).normalMap μ = μ := by
  rw [ofFiniteAlphabetLift, ofTropicalDegreeMap_normalMap]

/-- Supports are unchanged. -/
@[simp]
theorem ofFiniteAlphabetLift_spatialMap :
    (ofFiniteAlphabetLift (R := R) (g := g) hτ hτ0 hπ).spatialMap =
      ContinuousAffineEquiv.refl ℝ V := by
  rw [ofFiniteAlphabetLift, ofTropicalDegreeMap_spatialMap]

/-- On a homogeneous field `z^x ∂_μ` of the alphabet, the Lie map gives `z^{τ x} ∂_μ`. -/
theorem coe_ofFiniteAlphabetLift_lieHom_of_homogeneous {x : M × (E → ℤ)}
    (y : tropicalVertexLieAlgebra (R := R) (PositiveDegrees.finiteAlphabet m)
      (AddMonoidHom.fst M (E → ℤ)))
    (μ : M →+ R) (hy : single (AddMonoidHom.fst M (E → ℤ)) x μ = y.val) :
    ((ofFiniteAlphabetLift (g := g) hτ hτ0 hπ).lieHom y).val = single π (τ x) μ := by
  rw [ofFiniteAlphabetLift, coe_ofTropicalDegreeMap_lieHom_of_homogeneous _ _ y μ hy,
    PositiveDegrees.finiteAlphabetLift_apply]

end OfFiniteAlphabetLift

end Mei.DirectedWall.Pushforward
