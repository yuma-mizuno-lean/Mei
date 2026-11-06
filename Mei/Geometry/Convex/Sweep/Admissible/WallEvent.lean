/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Admissible
public import Mei.Geometry.Convex.Polyhedron.CrossingEvents
public import Mei.Geometry.Convex.Polyhedron.WallEvent
public import Mei.Geometry.Convex.Polyhedron.SingularSupport

/-!
# Canonical signed events of admissible rays

Replace a ray's chosen representative wall at each encounter by the complete
set of incident indexed walls and the sign of its chosen normal on the prescribed
outgoing direction, which is the negative of forward velocity. The canonical
finite event alphabet distinguishes simultaneous encounters without losing
coincident wall indices. The path, every encounter parameter, local directions,
incoming source and singular avoidance are retained. Ordered crossing times of
an admissible segment determine the same kind of event, and distinct such times
have distinct canonical events. Finite sums over the event inventory therefore
reindex over the reversed crossing times, with coincident walls kept together.

At a regular encounter all incident walls have the same affine direction.
Consequently the normal chosen by the event remains transverse even when it
differs from the original representative. This construction uses
`AdmissibleRayRealization` and `WallEvent`; simultaneous incidence follows
`affineSpan_eq_of_notMem_singularSupport`. The geometric conventions
are those of Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, Definition 2.10 (arXiv:1503.06183v5).
-/

public noncomputable section

open Set

namespace Mei.Convex.AdmissibleRayRealization

variable {V ι K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {n : ℕ} {W : ι → Set V} {f : ι → V →L[ℝ] ℝ} {c : ι → ℝ}
  {a : Fin n → ι} {v : Fin (n + 1) → V} {S : K → Set V} {C : Set V} {Q : V}
  (r : AdmissibleRayRealization (fun j => f (a j)) (fun j => c (a j)) v
    (fun j => W (a j)) W S C Q)

open Classical in
/-- At each recorded encounter, retain every incident indexed wall and the sign
of its chosen normal on the prescribed outgoing direction `v j.castSucc`,
which is the negative of forward velocity on the outgoing segment. -/
def wallEvents (j : Fin n) : WallEvent ι := by
  let s := (Set.toFinite {b | r.ray (r.parameter j.succ) ∈ W b}).toFinset
  have hs : s.Nonempty := ⟨a j, by simpa [s] using r.incidence j⟩
  exact (⟨s, hs⟩, SignType.sign (f hs.choose (v j.castSucc)))

/-- The canonical event retains exactly all walls containing the encounter point. -/
@[simp]
theorem mem_wallEvents (j : Fin n) (b : ι) :
    b ∈ (r.wallEvents j).1.val ↔ r.ray (r.parameter j.succ) ∈ W b := by
  classical
  simp [wallEvents]

/-- The sign carried by a canonical event evaluates its chosen normal on the
prescribed outgoing direction, which is the negative of forward velocity. -/
@[simp↓]
theorem normal_sign_wallEvents (j : Fin n) :
    SignType.sign ((r.wallEvents j).normal f (v j.castSucc)) = (r.wallEvents j).2 := by
  simp [wallEvents]

/-- Canonical signed events do not depend on which incident representative wall
was originally recorded. Agreement of paths and encounter times suffices. -/
theorem wallEvents_eq_of_ray_eq_of_parameter_eq {a' : Fin n → ι}
    (s : AdmissibleRayRealization (fun j => f (a' j)) (fun j => c (a' j)) v
      (fun j => W (a' j)) W S C Q)
    (hr : r.ray = s.ray) (hp : r.parameter = s.parameter) : r.wallEvents = s.wallEvents := by
  funext j
  have hs : r.ray (r.parameter j.succ) ∈ (s.wallEvents j).support W := by
    rw [hr, hp]
    simp
  exact (r.wallEvents j).eq_of_mem_support_of_normal_sign_eq (s.wallEvents j) W f
    (v j.castSucc) (by simp) hs (r.normal_sign_wallEvents j) (s.normal_sign_wallEvents j)

variable (hker : ∀ b, (f b).toLinearMap.ker = (affineSpan ℝ (W b)).direction)
  (hregular : ∀ j : Fin n, r.ray (r.parameter j.succ) ∉ singularSupport W)

include hker hregular in
/-- Every incident wall is transverse at a regular recorded encounter, including
walls other than the original chosen representative. -/
theorem normal_ne_zero_of_mem_wallEvents (j : Fin n) {b : ι}
    (hb : b ∈ (r.wallEvents j).1.val) : f b (v j.castSucc) ≠ 0 := by
  have hb' := (r.mem_wallEvents j b).mp hb
  have hd : (affineSpan ℝ (W b)).direction = (affineSpan ℝ (W (a j))).direction :=
    congrArg AffineSubspace.direction
      (affineSpan_eq_of_notMem_singularSupport (hregular j) hb' (r.incidence j))
  intro hz
  apply r.transverse j
  have hm : v j.castSucc ∈ (affineSpan ℝ (W b)).direction := by
    rw [← hker b]
    exact LinearMap.mem_ker.mpr hz
  rwa [hd, ← hker (a j), LinearMap.mem_ker] at hm

variable (hW : ∀ b x, x ∈ W b → f b x = c b)

/-- Relabel all recorded encounters by their canonical signed simultaneous events.
The complete actual ray, parameter tuple, original obstacle family and source
conditions are preserved. -/
def withWallEvents :
    AdmissibleRayRealization (fun j => (r.wallEvents j).normal f)
      (fun j => (r.wallEvents j).offset c) v (fun j => (r.wallEvents j).support W)
      W S C Q where
  ray := r.ray
  parameter := r.parameter
  parameter_zero := r.parameter_zero
  strictAnti_parameter := r.strictAnti_parameter
  transverse j := (r.wallEvents j).normal_ne_zero_of_mem_support W f
    (by simp) (fun b hb => r.normal_ne_zero_of_mem_wallEvents hker hregular j
      ((r.mem_wallEvents j b).mpr hb))
  endpoint_eq := r.endpoint_eq
  directionAt_eq := r.directionAt_eq
  bends_recorded := r.bends_recorded
  height_eq j := (r.wallEvents j).normal_apply_of_mem_support W f c hW
    (by simp)
  incidence j := by simp
  avoids_walls := r.avoids_walls
  incoming := r.incoming
  avoids_singular := r.avoids_singular
  off_walls := r.off_walls

/-- Canonical event relabelling preserves the entire path and incoming tail. -/
@[simp]
theorem ray_withWallEvents : (r.withWallEvents hker hregular hW).ray = r.ray := (rfl)

/-- Canonical event relabelling preserves all encounter times and the endpoint time. -/
@[simp]
theorem parameter_withWallEvents :
    (r.withWallEvents hker hregular hW).parameter = r.parameter := (rfl)

end Mei.Convex.AdmissibleRayRealization

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y : WallComplement W}

/-- The simultaneous event at a genuine crossing time of an admissible segment.
Its incidence set contains all indexed walls through the event, and its sign is
computed on the backward displacement. -/
def crossingWallEvent (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y) (t : ℝ)
    (ht : t ∈ orderedCrossingTimes e) : WallEvent ι :=
  let s : {s : Finset ι // s.Nonempty} :=
    ⟨crossingWalls x y t, crossingWalls_nonempty e ht⟩
  (s, SignType.sign (f s.property.choose (x.val - y.val)))

/-- The incidence set of a crossing event is the indexed crossing set. -/
@[simp]
theorem crossingWallEvent_fst_val (f : ι → V →L[ℝ] ℝ)
    (e : x ⟶ y) (t : ℝ) (ht : t ∈ orderedCrossingTimes e) :
    (crossingWallEvent f e t ht).1.val = crossingWalls x y t := (rfl)

/-- The sign of a crossing event is computed by its chosen normal on the
backward displacement. -/
@[simp↓]
theorem normal_sign_crossingWallEvent (f : ι → V →L[ℝ] ℝ)
    (e : x ⟶ y) (t : ℝ) (ht : t ∈ orderedCrossingTimes e) :
    SignType.sign ((crossingWallEvent f e t ht).normal f (x.val - y.val)) =
      (crossingWallEvent f e t ht).2 := by
  simp [crossingWallEvent, WallEvent.normal_def]

/-- An indexed wall contains a crossing point exactly when it belongs to the
canonical event at that crossing. -/
theorem mem_crossingWallEvent (f : ι → V →L[ℝ] ℝ)
    (e : x ⟶ y) (t : ℝ) (ht : t ∈ orderedCrossingTimes e) (j : ι) :
    AffineMap.lineMap x.val y.val t ∈ W j ↔ j ∈ (crossingWallEvent f e t ht).1.val := by
  rw [crossingWallEvent_fst_val, mem_crossingWalls, mem_crossings]
  exact (and_iff_right (Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht))).symm

/-- Distinct genuine crossing times determine distinct canonical simultaneous
events, independently of the normals used to compute their signs. -/
theorem crossingWallEvent_injective (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    {s t : ℝ} (hs : s ∈ orderedCrossingTimes e) (ht : t ∈ orderedCrossingTimes e)
    (he : crossingWallEvent f e s hs = crossingWallEvent f e t ht) : s = t := by
  by_contra hne
  have hd := disjoint_crossingWalls e hne
  obtain ⟨b, hb⟩ := crossingWalls_nonempty e hs
  have hb' : b ∈ crossingWalls x y t := by
    have heq : crossingWalls x y s = crossingWalls x y t := by
      have hval := congrArg (fun z : WallEvent ι => z.1.val) he
      simpa only [crossingWallEvent_fst_val] using hval
    exact (Finset.ext_iff.mp heq b).mp hb
  exact (Finset.disjoint_left.mp hd hb) hb'


/-- The finite inventory of canonical simultaneous events on one admissible segment. -/
def segmentWallEvents (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y) : Finset (WallEvent ι) := by
  classical
  exact (orderedCrossingTimes e).toFinset.attach.image fun t =>
    crossingWallEvent f e t.val (List.mem_toFinset.mp t.property)

/-- A genuine segment crossing belongs to its finite simultaneous-event inventory. -/
@[simp]
theorem crossingWallEvent_mem_segmentWallEvents (f : ι → V →L[ℝ] ℝ)
    (e : x ⟶ y) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    crossingWallEvent f e t ht ∈ segmentWallEvents f e := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨t, List.mem_toFinset.mpr ht⟩, Finset.mem_attach _ _, rfl⟩

/-- The crossing point lies on the wall chosen as the normal representative of
its canonical simultaneous event. -/
theorem mem_chosenWall_crossingWallEvent (f : ι → V →L[ℝ] ℝ)
    (e : x ⟶ y) (t : ℝ) (ht : t ∈ orderedCrossingTimes e) :
    AffineMap.lineMap x.val y.val t ∈ W (crossingWallEvent f e t ht).1.property.choose := by
  have hs : AffineMap.lineMap x.val y.val t ∈ (crossingWallEvent f e t ht).support W := by
    exact (WallEvent.mem_support _ _ _).2 (fun j => mem_crossingWallEvent f e t ht j)
  exact (WallEvent.mem_support _ _ _).mp hs _ |>.mpr
    (crossingWallEvent f e t ht).1.property.choose_spec

/-- Inventory membership is exactly representation by a genuine crossing time. -/
theorem mem_segmentWallEvents_iff (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (b : WallEvent ι) :
    b ∈ segmentWallEvents f e ↔ ∃ t, ∃ ht : t ∈ orderedCrossingTimes e,
      b = crossingWallEvent f e t ht := by
  classical
  constructor
  · intro hb
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hb
    exact ⟨t.val, List.mem_toFinset.mp t.property, he.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact crossingWallEvent_mem_segmentWallEvents f e ht

/-- Summing over the genuine event inventory is summing once over each
crossing time, in reverse crossing order. The summands need only commute
additively; coincident indexed walls remain one event. -/
theorem sum_segmentWallEvents {A : Type*} [AddCommMonoid A]
    (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y) (g : WallEvent ι → A) :
    ∑ b ∈ segmentWallEvents f e, g b =
      ∑ t : Fin (orderedCrossingTimes e).length,
        g (crossingWallEvent f e
          ((orderedCrossingTimes e).reverse[t.val]'(by
            simpa only [List.length_reverse] using t.isLt))
          (List.mem_reverse.mp (List.getElem_mem (by
            simpa only [List.length_reverse] using t.isLt)))) := by
  classical
  symm
  refine Finset.sum_bij (fun t _ => crossingWallEvent f e
    ((orderedCrossingTimes e).reverse[t.val]'(by
      simpa only [List.length_reverse] using t.isLt))
    (List.mem_reverse.mp (List.getElem_mem (by
      simpa only [List.length_reverse] using t.isLt))))
    (fun _ _ => crossingWallEvent_mem_segmentWallEvents _ _ _) ?_ ?_ (fun _ _ => rfl)
  · intro t _ t' _ he
    apply Fin.ext
    exact ((List.nodup_reverse.mpr (pairwise_orderedCrossingTimes e).nodup).getElem_inj_iff).mp
      (crossingWallEvent_injective f e _ _ he)
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := (mem_segmentWallEvents_iff f e b).mp hb
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mpr ht)
    exact ⟨⟨j, by simpa only [List.length_reverse] using hj⟩,
      Finset.mem_univ _, by simp only [he]⟩

/-- The parameter of a segment event is its displacement to the specified ray's
starting scale. Events outside the genuine inventory have the default value zero. -/
noncomputable def segmentEventParameter (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (T : ℝ) (b : WallEvent ι) : ℝ := by
  classical
  exact if hb : b ∈ segmentWallEvents f e then
    T * (1 - ((mem_segmentWallEvents_iff f e b).mp hb).choose)
  else 0

/-- An event's ray parameter is the terminal displacement at its genuine
crossing time, computed from the unique crossing-time witness. -/
@[simp]
theorem segmentEventParameter_of_mem (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (T : ℝ) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    segmentEventParameter f e T (crossingWallEvent f e t ht) = T * (1 - t) := by
  classical
  have hb := crossingWallEvent_mem_segmentWallEvents f e ht
  rw [segmentEventParameter, dite_eq_left hb]
  congr 2
  apply crossingWallEvent_injective f e
    ((mem_segmentWallEvents_iff f e
      (crossingWallEvent f e t ht)).mp hb).choose_spec.choose ht
  exact ((mem_segmentWallEvents_iff f e
    (crossingWallEvent f e t ht)).mp hb).choose_spec.choose_spec.symm

/-- The ray parameter vanishes for an event outside the genuine inventory. -/
@[simp]
theorem segmentEventParameter_of_not_mem (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (T : ℝ) {b : WallEvent ι} (hb : b ∉ segmentWallEvents f e) :
    segmentEventParameter f e T b = 0 := by
  classical
  rw [segmentEventParameter, dite_eq_right hb]

/-- A genuine event has positive parameter for a positively scaled ray. -/
theorem segmentEventParameter_pos (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (T : ℝ) (hT : 0 < T) {t : ℝ} (ht : t ∈ orderedCrossingTimes e) :
    0 < segmentEventParameter f e T (crossingWallEvent f e t ht) := by
  rw [segmentEventParameter_of_mem]
  exact mul_pos hT (sub_pos.mpr (mem_Ioo_of_mem_orderedCrossingTimes e ht).2)

/-- Event parameters are injective on the genuine inventory for a positively
scaled ray. -/
theorem segmentEventParameter_injOn (f : ι → V →L[ℝ] ℝ) (e : x ⟶ y)
    (T : ℝ) (hT : 0 < T) : Set.InjOn (segmentEventParameter f e T) (segmentWallEvents f e) := by
  intro b hb b' hb' he
  obtain ⟨t, ht, rfl⟩ := (mem_segmentWallEvents_iff f e b).mp hb
  obtain ⟨t', ht', rfl⟩ := (mem_segmentWallEvents_iff f e b').mp hb'
  rw [segmentEventParameter_of_mem, segmentEventParameter_of_mem] at he
  have htt : t = t' := by
    apply (mul_left_cancel₀ (ne_of_gt hT))
    linarith
  subst t'
  rfl

end Mei.Convex.WallComplement
