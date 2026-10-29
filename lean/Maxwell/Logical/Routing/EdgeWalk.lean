import Maxwell.Logical.Routing.Walk

/-! Chronological simple unit-edge paths for every original graph edge. -/

namespace Maxwell.Logical.Routing.EdgeWalk

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Schedule
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.Terminals
open Maxwell.Logical.Routing.Gluing
open Maxwell.Logical.Routing.Walk

/-- Change proved endpoint names while preserving the actual samples. -/
def reanchor {a b c d : Point} (walk : LatticeWalk a b) (ha : a = c) (hb : b = d) : LatticeWalk c d where
  length := walk.length
  point := walk.point
  first := walk.first.trans ha
  last := walk.last.trans hb
  step := walk.step

noncomputable def bottomWalk {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    LatticeWalk (vertexPoint data (data.endpoint i.1 i.2)) (gridPort (token data i) 0) where
  length := correctedArmLength (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
  point t := translate (tileTranslation data (data.endpoint i.1 i.2))
    (correctedArmPoint (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2) t)
  first := by rw [correctedArm_start]; rfl
  last := bottomSample_end data _ _
  step t ht := (translate_unit_adjacent _ _ _).mpr
    (correctedArm_steps _ _ ⟨t, ht⟩)

theorem bottomWalk_simple {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    Simple (bottomWalk data i) := by
  intro s t hs ht he
  have hh := correctedArm_injective (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
    (a₁ := ⟨s, by change s ≤ correctedArmLength _ _ at hs; omega⟩)
    (a₂ := ⟨t, by change t ≤ correctedArmLength _ _ at ht; omega⟩)
    (translate_injective _ he)
  exact congrArg Fin.val hh

theorem bottomWalk_height {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (t : ℕ) (ht : t ≤ (bottomWalk data i).length) :
    -16 ≤ ((bottomWalk data i).point t).2.2 ∧ ((bottomWalk data i).point t).2.2 ≤ 0 := by
  have hb := correctedArm_bounds (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
    ⟨t, by change t ≤ correctedArmLength _ _ at ht; omega⟩
  simpa only [bottomWalk, correctedArm, translate, tileTranslation, zero_add] using hb.2.2.2.2

theorem bottomWalk_face {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (t : ℕ) (ht : t ≤ (bottomWalk data i).length) :
    ((bottomWalk data i).point t).2.2 = 0 ↔ t = (bottomWalk data i).length := by
  have hb := correctedArm_face (data.part (data.endpoint i.1 i.2)) (data.arm i.1 i.2)
    ⟨t, by change t ≤ correctedArmLength _ _ at ht; omega⟩
  simpa only [bottomWalk, correctedArm, translate, tileTranslation, zero_add] using hb

/-- The actual flat network walk ending at its proved adjacent pairing port. -/
noncomputable def routedWalk {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    LatticeWalk (gridPort (token data i) 0) (gridPort (pairPort (data.pair i.1) i.2) (96 * (2 * half))) :=
  reanchor (networkWalk (permutationSchedule data.colors) (6 * (2 * half)) (token data i)) rfl (by
    rw [permutationSchedule_routes_target]
    change gridPort (data.target (tilePort _ _)) _ = _
    rw [data.target_incidence]
    congr 1
    push_cast
    ring)

/-- Complete incidence leg from its original graph vertex to its top port. -/
noncomputable def leg {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) :
    LatticeWalk (vertexPoint data (data.endpoint i.1 i.2))
      (gridPort (pairPort (data.pair i.1) i.2) (96 * (2 * half))) :=
  append (bottomWalk data i) (routedWalk data i)

theorem routedWalk_height {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (t : ℕ) (ht : t ≤ (routedWalk data i).length) :
    0 ≤ ((routedWalk data i).point t).2.2 ∧ ((routedWalk data i).point t).2.2 ≤ 96 * (2 * half) := by
  have hh := networkWalk_height (permutationSchedule data.colors) (6 * (2 * half)) (token data i) t ht
  have he : (16 : ℤ) * (6 * (2 * half) : ℕ) = 96 * (2 * half) := by push_cast; ring
  change 0 ≤ ((routedWalk data i).point t).2.2 ∧
    ((routedWalk data i).point t).2.2 ≤ 16 * (6 * (2 * half) : ℕ) at hh
  rw [he] at hh
  exact hh

theorem routedWalk_faces {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (t : ℕ) (ht : t ≤ (routedWalk data i).length) :
    ((((routedWalk data i).point t).2.2 = 0) ↔ t = 0) ∧
    ((((routedWalk data i).point t).2.2 = 96 * (2 * half)) ↔ t = (routedWalk data i).length) := by
  have hh := networkWalk_faces (permutationSchedule data.colors) (6 * (2 * half)) (token data i) t ht
  have he : (16 : ℤ) * (6 * (2 * half) : ℕ) = 96 * (2 * half) := by push_cast; ring
  change ((((routedWalk data i).point t).2.2 = 0) ↔ t = 0) ∧
    ((((routedWalk data i).point t).2.2 = 16 * (6 * (2 * half) : ℕ)) ↔
      t = (routedWalk data i).length) at hh
  rw [he] at hh
  exact hh

/-- Bottom and network pieces meet exactly at the matching incidence port. -/
theorem bottom_network_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (a b : Incidence E) (s t : ℕ) (hs : s ≤ (bottomWalk data a).length)
    (ht : t ≤ (routedWalk data b).length)
    (he : (bottomWalk data a).point s = (routedWalk data b).point t) :
    a = b ∧ s = (bottomWalk data a).length ∧ t = 0 := by
  have hb := bottomWalk_height data a s hs
  have hn := routedWalk_height data b t ht
  have hz := congrArg (fun p : Point => p.2.2) he
  have hse := (bottomWalk_face data a s hs).mp (by omega)
  have hte := (routedWalk_faces data b t ht).1.mp (by omega)
  rw [hse, hte, (bottomWalk data a).last, (routedWalk data b).first] at he
  exact ⟨token_injective data (gridPort_injective _ 0 he), hse, hte⟩

theorem leg_simple {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E) : Simple (leg data i) := by
  apply append_simple _ _ (bottomWalk_simple data i)
    (networkWalk_simple (permutationSchedule data.colors) _ _)
  intro s t hs ht he
  exact (bottom_network_intersection data i i s t hs ht he).2

/-- Distinct incidence legs can meet only at their common original graph vertex. -/
theorem leg_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (a b : Incidence E) (s t : ℕ) (hs : s ≤ (leg data a).length)
    (ht : t ≤ (leg data b).length) (he : (leg data a).point s = (leg data b).point t) :
    a = b ∨ (s = 0 ∧ t = 0 ∧ data.endpoint a.1 a.2 = data.endpoint b.1 b.2) := by
  rcases append_sample (bottomWalk data a) (routedWalk data a) s hs with ha | ha
  · rcases append_sample (bottomWalk data b) (routedWalk data b) t ht with hb | hb
    · change (append _ _).point s = (append _ _).point t at he
      rw [ha.2, hb.2] at he
      have hh := bottomSample_intersection data (data.endpoint a.1 a.2) (data.endpoint b.1 b.2)
        (data.arm a.1 a.2) (data.arm b.1 b.2)
        ⟨s, by have h := ha.1; change s ≤ correctedArmLength _ _ at h; omega⟩
        ⟨t, by have h := hb.1; change t ≤ correctedArmLength _ _ at h; omega⟩ he
      rcases hh.2 with h | h
      · exact Or.inl (data.incidence_injective (Prod.ext hh.1 h.1))
      · exact Or.inr ⟨h.1, h.2, hh.1⟩
    · change (append _ _).point s = (append _ _).point t at he
      rw [ha.2, hb.2.2] at he
      exact Or.inl (bottom_network_intersection data a b s _ ha.1 hb.2.1 he).1
  · rcases append_sample (bottomWalk data b) (routedWalk data b) t ht with hb | hb
    · change (append _ _).point s = (append _ _).point t at he
      rw [ha.2.2, hb.2] at he
      exact Or.inl (bottom_network_intersection data b a t _ hb.1 ha.2.1 he.symm).1.symm
    · change (append _ _).point s = (append _ _).point t at he
      rw [ha.2.2, hb.2.2] at he
      exact Or.inl (token_injective data (networkWalk_intersection _ _ _ _ _ _ ha.2.1 hb.2.1 he))

noncomputable def topWalk {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    LatticeWalk (gridPort (pairPort (data.pair e) false) (96 * (2 * half)))
      (gridPort (pairPort (data.pair e) true) (96 * (2 * half))) where
  length := 48
  point t := translate (32 * (data.pair e).1.val, 16 * (data.pair e).2.val, 96 * (2 * half)) (topPoint t)
  first := by simp [topPoint, translate, gridPort, pairPort]; ring
  last := by simp [topPoint, translate, gridPort, pairPort]; ring_nf
  step t ht := (translate_unit_adjacent _ _ _).mpr (topBridge_steps ⟨t, ht⟩)

theorem topWalk_simple {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) : Simple (topWalk data e) := by
  intro i j hi hj he
  have hh := topBridge_injective
    (a₁ := ⟨i, by change i ≤ 48 at hi; omega⟩)
    (a₂ := ⟨j, by change j ≤ 48 at hj; omega⟩) (translate_injective _ he)
  exact congrArg Fin.val hh

theorem topWalk_height {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t ≤ (topWalk data e).length) :
    96 * (2 * half) ≤ ((topWalk data e).point t).2.2 ∧
      ((topWalk data e).point t).2.2 ≤ 96 * (2 * half) + 16 := by
  have hh := topBridge_bounds ⟨t, by change t ≤ 48 at ht; omega⟩
  simp only [topWalk, translate]
  simp only [topBridge] at hh
  omega

theorem topWalk_faces {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t ≤ (topWalk data e).length) :
    ((topWalk data e).point t).2.2 = 96 * (2 * half) ↔ t = 0 ∨ t = 48 := by
  have hh := topBridge_faces ⟨t, by change t ≤ 48 at ht; omega⟩
  simpa only [topWalk, translate, topBridge, add_eq_left] using hh

theorem half_pos {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) : 0 < half := by
  have hh := (data.tile (data.endpoint e false)).1.isLt
  omega

/-- A leg meets a top connector only at its designated endpoint on its own edge. -/
theorem leg_top_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (a : Incidence E) (e : E) (s t : ℕ) (hs : s ≤ (leg data a).length)
    (ht : t ≤ (topWalk data e).length)
    (he : (leg data a).point s = (topWalk data e).point t) :
    a.1 = e ∧ s = (leg data a).length ∧ t = if a.2 then 48 else 0 := by
  have hp := half_pos data e
  have htop := topWalk_height data e t ht
  rcases append_sample (bottomWalk data a) (routedWalk data a) s hs with ha | ha
  · change (append _ _).point s = _ at he
    rw [ha.2] at he
    have hbot := bottomWalk_height data a s ha.1
    have hz := congrArg (fun p : Point => p.2.2) he
    omega
  · change (append _ _).point s = _ at he
    rw [ha.2.2] at he
    have hn := routedWalk_height data a _ ha.2.1
    have hz := congrArg (fun p : Point => p.2.2) he
    have hse := (routedWalk_faces data a _ ha.2.1).2.mp (by omega)
    have hte := (topWalk_faces data e t ht).mp (by omega)
    have hslen : s = (leg data a).length := by
      change s = (bottomWalk data a).length + (routedWalk data a).length
      omega
    rw [hse, (routedWalk data a).last] at he
    rcases hte with hzero | hlast
    · rw [hzero, (topWalk data e).first] at he
      have hports := gridPort_injective (2 * half) (96 * (2 * half)) he
      have hh := @pairPort_injective half (data.pair a.1, a.2) (data.pair e, false) hports
      have hside : a.2 = false := congrArg (fun x : (Fin half × Fin (2 * half)) × Bool => x.2) hh
      exact ⟨data.pair_injective (congrArg Prod.fst hh), hslen, by simp only [hzero, hside, Bool.false_eq_true, ↓reduceIte]⟩
    · have hlast' : t = (topWalk data e).length := hlast
      rw [hlast', (topWalk data e).last] at he
      have hports := gridPort_injective (2 * half) (96 * (2 * half)) he
      have hh := @pairPort_injective half (data.pair a.1, a.2) (data.pair e, true) hports
      have hside : a.2 = true := congrArg (fun x : (Fin half × Fin (2 * half)) × Bool => x.2) hh
      exact ⟨data.pair_injective (congrArg Prod.fst hh), hslen, by simp only [hlast, hside, ↓reduceIte]⟩

/-- The actual unit-edge walk of an original graph edge, with its second leg reversed. -/
noncomputable def edgeWalk {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    LatticeWalk (vertexPoint data (data.endpoint e false)) (vertexPoint data (data.endpoint e true)) :=
  append (append (leg data (e, false)) (topWalk data e)) (reverse (leg data (e, true)))

theorem endpoint_distinct {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    data.endpoint e false ≠ data.endpoint e true := by
  intro he
  have hh := congrArg data.part he
  rw [data.endpoint_part, data.endpoint_part] at hh
  contradiction

/-- Every complete corrected original-edge walk is simple. -/
theorem edgeWalk_simple {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) : Simple (edgeWalk data e) := by
  have hleft : Simple (append (leg data (e, false)) (topWalk data e)) := by
    apply append_simple _ _ (leg_simple data _) (topWalk_simple data e)
    intro i j hi hj he
    have hh := leg_top_intersection data (e, false) e i j hi hj he
    exact ⟨hh.2.1, hh.2.2⟩
  apply append_simple _ _ hleft (reverse_simple _ (leg_simple data _))
  intro i j hi hj he
  have hj' : j ≤ (leg data (e, true)).length := hj
  change (append (leg data (e, false)) (topWalk data e)).point i =
    (leg data (e, true)).point ((leg data (e, true)).length - j) at he
  rcases append_sample (leg data (e, false)) (topWalk data e) i hi with hh | hh
  · rw [hh.2] at he
    have hx := leg_intersection data (e, false) (e, true) i _ hh.1 (by omega) he
    rcases hx with hx | hx
    · exact False.elim (Bool.false_ne_true (congrArg Prod.snd hx))
    · exact False.elim (endpoint_distinct data e hx.2.2)
  · rw [hh.2.2] at he
    have hx := leg_top_intersection data (e, true) e
      ((leg data (e, true)).length - j) (i - (leg data (e, false)).length)
      (by omega) hh.2.1 he.symm
    have hx' : i - (leg data (e, false)).length = 48 := hx.2.2
    constructor
    · change i = (leg data (e, false)).length + 48
      omega
    · omega

/-- The flat path's counted edges equal the previously bounded constructive length. -/
theorem edgeWalk_length {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    (edgeWalk data e).length = edgeLength data.colors (data.arm e false) (data.arm e true)
      (token data (e, false)) (token data (e, true)) := by
  simp only [edgeWalk, append_length, leg, reverse, bottomWalk, routedWalk, reanchor,
    topWalk, networkWalk_length, edgeLength, data.endpoint_part]
  omega

theorem edgeWalk_wire_form {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    ∃ j : ℕ, (edgeWalk data e).length = 4 * j + 1 := by
  rw [edgeWalk_length]
  exact edgeLength_wire_form _ _ _ _ _

theorem edgeWalk_length_bound {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    (edgeWalk data e).length ≤ 1024 * (2 * half) := by
  rw [edgeWalk_length]
  have hh := edgeLength_bound data.colors (data.arm e false) (data.arm e true)
    (token data (e, false)) (token data (e, true))
  have hp := half_pos data e
  omega

/-- Every full-edge sample belongs to one of its two legs or its top connector. -/
theorem edgeWalk_sample {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t ≤ (edgeWalk data e).length) :
    (∃ side : Bool, ∃ s : ℕ, s ≤ (leg data (e, side)).length ∧
      (edgeWalk data e).point t = (leg data (e, side)).point s) ∨
    (∃ s : ℕ, s ≤ (topWalk data e).length ∧ (edgeWalk data e).point t = (topWalk data e).point s) := by
  rcases append_sample (append (leg data (e, false)) (topWalk data e))
    (reverse (leg data (e, true))) t ht with h | h
  · rcases append_sample (leg data (e, false)) (topWalk data e) t h.1 with h' | h'
    · exact Or.inl ⟨false, t, h'.1, h.2.trans h'.2⟩
    · exact Or.inr ⟨_, h'.2.1, h.2.trans h'.2.2⟩
  · refine Or.inl ⟨true, (leg data (e, true)).length -
      (t - (append (leg data (e, false)) (topWalk data e)).length), by omega, ?_⟩
    exact h.2.2

theorem topWalk_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (e f : E) (s t : ℕ) (hs : s ≤ (topWalk data e).length) (ht : t ≤ (topWalk data f).length)
    (he : (topWalk data e).point s = (topWalk data f).point t) : e = f := by
  by_contra hn
  have hp : data.pair e ≠ data.pair f := fun h => hn (data.pair_injective h)
  have hsep : ((data.pair e).1.val : ℤ) ≠ (data.pair f).1.val ∨
      ((data.pair e).2.val : ℤ) ≠ (data.pair f).2.val := by
    by_contra h
    push Not at h
    apply hp
    apply Prod.ext <;> apply Fin.ext <;> omega
  exact placedTopBridge_disjoint _ _ _ _ _ hsep
    ⟨s, by change s ≤ 48 at hs; omega⟩ ⟨t, by change t ≤ 48 at ht; omega⟩ he

/-- Distinct graph edges can meet only at a shared original endpoint. -/
theorem edgeWalk_intersection {V E : Type*} {half : ℕ} (data : Data V E half)
    (e f : E) (hne : e ≠ f) (s t : ℕ) (hs : s ≤ (edgeWalk data e).length)
    (ht : t ≤ (edgeWalk data f).length)
    (he : (edgeWalk data e).point s = (edgeWalk data f).point t) :
    ∃ a b : Bool, (edgeWalk data e).point s = vertexPoint data (data.endpoint e a) ∧
      data.endpoint e a = data.endpoint f b := by
  rcases edgeWalk_sample data e s hs with hl | htop
  · obtain ⟨a, i, hi, hsi⟩ := hl
    rcases edgeWalk_sample data f t ht with hr | htop
    · obtain ⟨b, j, hj, htj⟩ := hr
      rw [hsi, htj] at he
      rcases leg_intersection data (e, a) (f, b) i j hi hj he with hh | hh
      · exact False.elim (hne (congrArg Prod.fst hh))
      · refine ⟨a, b, ?_, hh.2.2⟩
        rw [hsi, hh.1, (leg data (e, a)).first]
    · obtain ⟨j, hj, htj⟩ := htop
      rw [hsi, htj] at he
      exact False.elim (hne (leg_top_intersection data (e, a) f i j hi hj he).1)
  · obtain ⟨i, hi, hsi⟩ := htop
    rcases edgeWalk_sample data f t ht with hr | htop
    · obtain ⟨b, j, hj, htj⟩ := hr
      rw [hsi, htj] at he
      exact False.elim (hne (leg_top_intersection data (f, b) e j i hj hi he.symm).1.symm)
    · obtain ⟨j, hj, htj⟩ := htop
      rw [hsi, htj] at he
      exact False.elim (hne (topWalk_intersection data e f i j hi hj he))

theorem vertexPoint_negative {V E : Type*} {half : ℕ} (data : Data V E half) (v : V) :
    (vertexPoint data v).2.2 < 0 := (bottomPoint_height data (Sum.inl v)).2

/-- An incidence leg encounters an original graph vertex only at its own start. -/
theorem leg_meets_vertex {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (v : V) (t : ℕ) (ht : t ≤ (leg data i).length)
    (he : (leg data i).point t = vertexPoint data v) : t = 0 ∧ data.endpoint i.1 i.2 = v := by
  rcases append_sample (bottomWalk data i) (routedWalk data i) t ht with h | h
  · change (append _ _).point t = _ at he
    rw [h.2, ← bottomSample_start data v 0] at he
    have hh := bottomSample_intersection data (data.endpoint i.1 i.2) v (data.arm i.1 i.2) 0
      ⟨t, by have h' := h.1; change t ≤ correctedArmLength _ _ at h'; omega⟩ ⟨0, by omega⟩ he
    rcases hh.2 with hh' | hh'
    · exact ⟨hh'.2, hh.1⟩
    · exact ⟨hh'.1, hh.1⟩
  · change (append _ _).point t = _ at he
    rw [h.2.2] at he
    have hn := routedWalk_height data i _ h.2.1
    have hv := vertexPoint_negative data v
    have hz := congrArg (fun p : Point => p.2.2) he
    omega

theorem edgeWalk_endpoint_index {V E : Type*} {half : ℕ} (data : Data V E half)
    (e : E) (side : Bool) (t : ℕ) (ht : t ≤ (edgeWalk data e).length)
    (he : (edgeWalk data e).point t = vertexPoint data (data.endpoint e side)) :
    t = if side then (edgeWalk data e).length else 0 := by
  cases side
  · exact edgeWalk_simple data e t 0 ht (Nat.zero_le _) (he.trans (edgeWalk data e).first.symm)
  · exact edgeWalk_simple data e t _ ht le_rfl (he.trans (edgeWalk data e).last.symm)

/-- A complete edge never passes through another original graph vertex. -/
theorem edgeWalk_meets_vertex {V E : Type*} {half : ℕ} (data : Data V E half)
    (e : E) (v : V) (t : ℕ) (ht : t ≤ (edgeWalk data e).length)
    (he : (edgeWalk data e).point t = vertexPoint data v) :
    ∃ side : Bool, data.endpoint e side = v ∧
      t = if side then (edgeWalk data e).length else 0 := by
  rcases edgeWalk_sample data e t ht with hl | htop
  · obtain ⟨side, s, hs, heq⟩ := hl
    have hh := leg_meets_vertex data (e, side) v s hs (heq.symm.trans he)
    refine ⟨side, hh.2, edgeWalk_endpoint_index data e side t ht ?_⟩
    simpa only [hh.2] using he
  · obtain ⟨s, hs, heq⟩ := htop
    have hh := topWalk_height data e s hs
    have hv := vertexPoint_negative data v
    have hz := congrArg (fun p : Point => p.2.2) (heq.symm.trans he)
    omega

theorem networkWalk_horizontal_bounds {q : ℕ} (schedule : ℕ → CubicLayer q)
    (hbox : ∀ level p t, InHorizontalBox q ((schedule level).point p t))
    (layers : ℕ) (token : Port q) (t : ℕ) (ht : t ≤ (networkWalk schedule layers token).length) :
    InHorizontalBox q ((networkWalk schedule layers token).point t) := by
  induction layers with
  | zero =>
    have hx := token.1.isLt
    have hy := token.2.isLt
    simp only [networkWalk, Walk.singleton, gridPort, InHorizontalBox]
    omega
  | succ level ih =>
    rcases append_sample (networkWalk schedule level token) (slabWalk schedule level token) t ht with h | h
    · rw [networkWalk, h.2]
      exact ih h.1
    · rw [networkWalk, h.2.2]
      simpa only [slabWalk, translate, InHorizontalBox, zero_add] using
        hbox level (placement schedule level token) (t - (networkWalk schedule level token).length)

theorem leg_box {V E : Type*} {half : ℕ} (data : Data V E half) (i : Incidence E)
    (t : ℕ) (ht : t ≤ (leg data i).length) :
    InHorizontalBox (2 * half) ((leg data i).point t) ∧
      -16 ≤ ((leg data i).point t).2.2 ∧ ((leg data i).point t).2.2 ≤ 96 * (2 * half) := by
  rcases append_sample (bottomWalk data i) (routedWalk data i) t ht with h | h
  · simp only [leg]
    rw [h.2]
    have hb := bottomWalk_height data i t h.1
    have hh := bottomSample_horizontal_bounds data (data.endpoint i.1 i.2) (data.arm i.1 i.2)
      ⟨t, by have h' := h.1; change t ≤ correctedArmLength _ _ at h'; omega⟩
    exact ⟨hh, hb.1, by omega⟩
  · simp only [leg]
    rw [h.2.2]
    have hb := routedWalk_height data i _ h.2.1
    have hh := networkWalk_horizontal_bounds (permutationSchedule data.colors)
      (permutationSchedule_horizontal_bounds data.colors) _ (token data i) _ h.2.1
    exact ⟨hh, by omega, hb.2⟩

theorem topWalk_box {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t ≤ (topWalk data e).length) :
    InHorizontalBox (2 * half) ((topWalk data e).point t) := by
  have hb := topBridge_bounds ⟨t, by change t ≤ 48 at ht; omega⟩
  have hx := (data.pair e).1.isLt
  have hy := (data.pair e).2.isLt
  simp only [topBridge] at hb
  simp only [InHorizontalBox, topWalk, translate]
  push_cast
  omega

/-- Every chronological sample of every original-edge path lies in the full
ambient box, including both endpoint vertices and all parity detours. -/
theorem edgeWalk_box {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : ℕ) (ht : t ≤ (edgeWalk data e).length) :
    InHorizontalBox (2 * half) ((edgeWalk data e).point t) ∧
      -16 ≤ ((edgeWalk data e).point t).2.2 ∧ ((edgeWalk data e).point t).2.2 ≤ 96 * (2 * half) + 16 := by
  rcases edgeWalk_sample data e t ht with hl | htop
  · obtain ⟨side, s, hs, heq⟩ := hl
    rw [heq]
    have hh := leg_box data (e, side) s hs
    exact ⟨hh.1, hh.2.1, by omega⟩
  · obtain ⟨s, hs, heq⟩ := htop
    rw [heq]
    have hh := topWalk_height data e s hs
    exact ⟨topWalk_box data e s hs, by omega, hh.2⟩

end Maxwell.Logical.Routing.EdgeWalk
