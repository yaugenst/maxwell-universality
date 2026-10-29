import Maxwell.Logical.Routing.Gluing

/-! Flat chronological unit-edge walks for the constructed routing. -/

namespace Maxwell.Logical.Routing.Walk

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Schedule

structure LatticeWalk (start finish : Point) where
  length : ℕ
  point : ℕ → Point
  first : point 0 = start
  last : point length = finish
  step : ∀ t < length, UnitAdjacent (point t) (point (t + 1))

def Simple {a b : Point} (walk : LatticeWalk a b) : Prop :=
  ∀ i j, i ≤ walk.length → j ≤ walk.length → walk.point i = walk.point j → i = j

def singleton (p : Point) : LatticeWalk p p where
  length := 0
  point _ := p
  first := rfl
  last := rfl
  step t ht := by omega

/-- Append adjacent walks and store the joint only once. -/
def append {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c) : LatticeWalk a c where
  length := left.length + right.length
  point t := if t ≤ left.length then left.point t else right.point (t - left.length)
  first := by simp only [Nat.zero_le, ↓reduceIte, left.first]
  last := by
    by_cases hr : right.length = 0
    · simp only [hr, Nat.add_zero, le_refl, ↓reduceIte, left.last]
      exact right.first.symm.trans (by simpa only [hr] using right.last)
    · simp only [show ¬left.length + right.length ≤ left.length by omega,
        ↓reduceIte, Nat.add_sub_cancel_left, right.last]
  step t ht := by
    by_cases hl : t + 1 ≤ left.length
    · have hl' : t ≤ left.length := by omega
      simp only [hl, hl', ↓reduceIte]
      exact left.step t (by omega)
    · by_cases ht' : t ≤ left.length
      · have he : t = left.length := by omega
        subst t
        simp only [le_refl, hl, ↓reduceIte, Nat.add_sub_cancel_left, left.last]
        simpa only [right.first] using right.step 0 (by omega)
      · simp only [hl, ht', ↓reduceIte]
        have he : t + 1 - left.length = (t - left.length) + 1 := by omega
        rw [he]
        exact right.step _ (by omega)

@[simp] theorem append_length {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c) :
    (append left right).length = left.length + right.length := rfl

/-- Any append sample comes from one of its two actual constituent walks. -/
theorem append_sample {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c)
    (t : ℕ) (ht : t ≤ (append left right).length) :
    (t ≤ left.length ∧ (append left right).point t = left.point t) ∨
      (left.length < t ∧ t - left.length ≤ right.length ∧
        (append left right).point t = right.point (t - left.length)) := by
  by_cases h : t ≤ left.length
  · exact Or.inl ⟨h, by simp only [append, h, ↓reduceIte]⟩
  · exact Or.inr ⟨by omega, by simp only [append_length] at ht; omega,
      by simp only [append, h, ↓reduceIte]⟩

/-- Local simplicity and a unique common joint prove concatenated simplicity. -/
theorem append_simple {a b c : Point} (left : LatticeWalk a b) (right : LatticeWalk b c)
    (hl : Simple left) (hr : Simple right)
    (hj : ∀ i j, i ≤ left.length → j ≤ right.length →
      left.point i = right.point j → i = left.length ∧ j = 0) : Simple (append left right) := by
  intro i j hi hj' he
  rcases append_sample left right i hi with hil | hir
  · rcases append_sample left right j hj' with hjl | hjr
    · rw [hil.2, hjl.2] at he
      exact hl i j hil.1 hjl.1 he
    · rw [hil.2, hjr.2.2] at he
      have hh := hj i (j - left.length) hil.1 hjr.2.1 he
      omega
  · rcases append_sample left right j hj' with hjl | hjr
    · rw [hir.2.2, hjl.2] at he
      have hh := hj j (i - left.length) hjl.1 hir.2.1 he.symm
      omega
    · rw [hir.2.2, hjr.2.2] at he
      have hh := hr _ _ hir.2.1 hjr.2.1 he
      omega

theorem unitAdjacent_symm (a b : Point) : UnitAdjacent a b ↔ UnitAdjacent b a := by
  simp only [UnitAdjacent, abs_sub_comm]

def reverse {a b : Point} (walk : LatticeWalk a b) : LatticeWalk b a where
  length := walk.length
  point t := walk.point (walk.length - t)
  first := by simp only [Nat.sub_zero, walk.last]
  last := by simp only [Nat.sub_self, walk.first]
  step t ht := by
    have he : walk.length - t = (walk.length - (t + 1)) + 1 := by omega
    rw [he]
    exact (unitAdjacent_symm _ _).mpr (walk.step _ (by omega))

theorem reverse_simple {a b : Point} (walk : LatticeWalk a b) (hs : Simple walk) : Simple (reverse walk) := by
  intro i j hi hj he
  have hh := hs (walk.length - i) (walk.length - j) (by omega) (by omega) he
  change i ≤ walk.length at hi
  change j ≤ walk.length at hj
  omega

/-- The actual translated slab traversed by a given token. -/
noncomputable def slabWalk {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ) (token : Port q) :
    LatticeWalk (gridPort (placement schedule level token) (16 * level))
      (gridPort (placement schedule (level + 1) token) (16 * (level + 1 : ℕ))) where
  length := (schedule level).length (placement schedule level token)
  point t := translate (0, 0, 16 * level) ((schedule level).point (placement schedule level token) t)
  first := by rw [(schedule level).first]; simp only [translate, gridPort, zero_add, add_zero]
  last := by
    rw [(schedule level).last]
    simp only [placement, Equiv.trans_apply, translate, gridPort, zero_add]
    push_cast
    ring_nf
  step t ht := (translate_unit_adjacent _ _ _).mpr ((schedule level).step _ t ht)

/-- A flat chronological walk through all computed slabs. -/
noncomputable def networkWalk {q : ℕ} (schedule : ℕ → CubicLayer q) : (layers : ℕ) → (token : Port q) →
    LatticeWalk (gridPort token 0) (gridPort (placement schedule layers token) (16 * layers))
  | 0, token => singleton (gridPort token 0)
  | t + 1, token => append (networkWalk schedule t token) (slabWalk schedule t token)

theorem networkWalk_length {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q) :
    (networkWalk schedule layers token).length = trajectoryLength schedule layers token := by
  induction layers with
  | zero => simp [networkWalk, singleton, trajectoryLength]
  | succ t ih =>
    simp only [networkWalk, append_length, ih, slabWalk, trajectoryLength, Fin.sum_univ_castSucc]
    rfl

/-- All samples lie within the actual slab height interval. -/
theorem slabWalk_height {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ) (token : Port q)
    (t : ℕ) (ht : t ≤ (slabWalk schedule level token).length) :
    16 * (level : ℤ) ≤ ((slabWalk schedule level token).point t).2.2 ∧
      ((slabWalk schedule level token).point t).2.2 ≤ 16 * (level + 1 : ℕ) := by
  have hh := (schedule level).slab (placement schedule level token) t ht
  simp only [slabWalk, translate]
  push_cast
  omega

theorem networkWalk_height {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q)
    (t : ℕ) (ht : t ≤ (networkWalk schedule layers token).length) :
    0 ≤ ((networkWalk schedule layers token).point t).2.2 ∧
      ((networkWalk schedule layers token).point t).2.2 ≤ 16 * (layers : ℤ) := by
  induction layers with
  | zero => simp only [networkWalk, singleton, gridPort]; omega
  | succ level ih =>
    rcases append_sample (networkWalk schedule level token) (slabWalk schedule level token) t ht with h | h
    · rw [networkWalk, h.2]
      have hh := ih h.1
      push_cast
      omega
    · rw [networkWalk, h.2.2]
      have hh := slabWalk_height schedule level token _ h.2.1
      push_cast at hh ⊢
      omega

theorem layer_length_pos {q : ℕ} (layer : CubicLayer q) (p : Port q) : 0 < layer.length p := by
  by_contra h
  have he : layer.length p = 0 := by omega
  have hh := (layer.first p).symm.trans (by simpa only [he] using layer.last p)
  have hz := congrArg (fun p : Point => p.2.2) hh
  change (0 : ℤ) = 16 at hz
  omega

theorem slabWalk_faces {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ) (token : Port q)
    (t : ℕ) (ht : t ≤ (slabWalk schedule level token).length) :
    ((((slabWalk schedule level token).point t).2.2 = 16 * (level : ℤ)) ↔ t = 0) ∧
    ((((slabWalk schedule level token).point t).2.2 = 16 * (level + 1 : ℕ)) ↔
      t = (slabWalk schedule level token).length) := by
  have hh := (schedule level).faces (placement schedule level token) t ht
  simp only [slabWalk, translate]
  push_cast
  constructor <;> constructor <;> intro he
  · exact hh.1.mp (by omega)
  · have hz := hh.1.mpr he
    omega
  · exact hh.2.mp (by omega)
  · have hz := hh.2.mpr he
    omega

theorem networkWalk_faces {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q)
    (t : ℕ) (ht : t ≤ (networkWalk schedule layers token).length) :
    ((((networkWalk schedule layers token).point t).2.2 = 0) ↔ t = 0) ∧
    ((((networkWalk schedule layers token).point t).2.2 = 16 * (layers : ℤ)) ↔
      t = (networkWalk schedule layers token).length) := by
  induction layers with
  | zero =>
    have he : t = 0 := by simpa only [networkWalk, singleton, Nat.le_zero] using ht
    simp only [he, networkWalk, singleton, gridPort, Nat.cast_zero, mul_zero]
    exact ⟨trivial, trivial⟩
  | succ level ih =>
    have hp := layer_length_pos (schedule level) (placement schedule level token)
    rcases append_sample (networkWalk schedule level token) (slabWalk schedule level token) t ht with h | h
    · have hf := ih h.1
      have hb := networkWalk_height schedule level token t h.1
      rw [networkWalk, h.2, append_length]
      have hp' : 0 < (slabWalk schedule level token).length := hp
      constructor
      · exact hf.1
      · push_cast
        constructor <;> intro he <;> omega
    · have hf := slabWalk_faces schedule level token (t - (networkWalk schedule level token).length) h.2.1
      have hb := slabWalk_height schedule level token (t - (networkWalk schedule level token).length) h.2.1
      have hlocal := (schedule level).slab (placement schedule level token)
        (t - (networkWalk schedule level token).length) h.2.1
      rw [networkWalk, h.2.2, append_length]
      constructor
      · constructor
        · intro hz
          have hz' : ((slabWalk schedule level token).point
              (t - (networkWalk schedule level token).length)).2.2 = 16 * (level : ℤ) := by omega
          have he := hf.1.mp hz'
          omega
        · intro he
          omega
      · constructor
        · intro hz
          have he := hf.2.mp hz
          omega
        · intro he
          exact hf.2.mpr (by omega)

theorem slabWalk_simple {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ) (token : Port q) :
    Simple (slabWalk schedule level token) := by
  intro i j hi hj he
  exact ((schedule level).injective _ _ i j hi hj (translate_injective _ he)).2

/-- The flat chronological network walks are simple for every computed schedule. -/
theorem networkWalk_simple {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ) (token : Port q) :
    Simple (networkWalk schedule layers token) := by
  induction layers with
  | zero => intro i j hi hj; simp only [networkWalk, singleton] at hi hj; omega
  | succ level ih =>
    apply append_simple _ _ ih (slabWalk_simple schedule level token)
    intro i j hi hj he
    have hl := networkWalk_height schedule level token i hi
    have hr := slabWalk_height schedule level token j hj
    have hlf := networkWalk_faces schedule level token i hi
    have hrf := slabWalk_faces schedule level token j hj
    have hz := congrArg (fun p : Point => p.2.2) he
    exact ⟨hlf.2.mp (by omega), hrf.1.mp (by omega)⟩

theorem network_slab_intersection {q : ℕ} (schedule : ℕ → CubicLayer q) (level : ℕ)
    (a b : Port q) (i j : ℕ) (hi : i ≤ (networkWalk schedule level a).length)
    (hj : j ≤ (slabWalk schedule level b).length)
    (he : (networkWalk schedule level a).point i = (slabWalk schedule level b).point j) :
    a = b ∧ i = (networkWalk schedule level a).length ∧ j = 0 := by
  have hl := networkWalk_height schedule level a i hi
  have hr := slabWalk_height schedule level b j hj
  have hlf := networkWalk_faces schedule level a i hi
  have hrf := slabWalk_faces schedule level b j hj
  have hz := congrArg (fun p : Point => p.2.2) he
  have hie := hlf.2.mp (by omega)
  have hje := hrf.1.mp (by omega)
  rw [hie, hje, (networkWalk schedule level a).last, (slabWalk schedule level b).first] at he
  exact ⟨(placement schedule level).injective (gridPort_injective q (16 * level) he), hie, hje⟩

/-- Distinct input tokens have disjoint flat chronological network walks. -/
theorem networkWalk_intersection {q : ℕ} (schedule : ℕ → CubicLayer q) (layers : ℕ)
    (a b : Port q) (i j : ℕ) (hi : i ≤ (networkWalk schedule layers a).length)
    (hj : j ≤ (networkWalk schedule layers b).length)
    (he : (networkWalk schedule layers a).point i = (networkWalk schedule layers b).point j) : a = b := by
  induction layers generalizing i j with
  | zero => exact gridPort_injective q 0 he
  | succ level ih =>
    rcases append_sample (networkWalk schedule level a) (slabWalk schedule level a) i hi with ha | ha
    · rcases append_sample (networkWalk schedule level b) (slabWalk schedule level b) j hj with hb | hb
      · change (append _ _).point i = (append _ _).point j at he
        rw [ha.2, hb.2] at he
        exact ih i j ha.1 hb.1 he
      · change (append _ _).point i = (append _ _).point j at he
        rw [ha.2, hb.2.2] at he
        exact (network_slab_intersection schedule level a b i _ ha.1 hb.2.1 he).1
    · rcases append_sample (networkWalk schedule level b) (slabWalk schedule level b) j hj with hb | hb
      · change (append _ _).point i = (append _ _).point j at he
        rw [ha.2.2, hb.2] at he
        exact (network_slab_intersection schedule level b a j _ hb.1 ha.2.1 he.symm).1.symm
      · change (append _ _).point i = (append _ _).point j at he
        rw [ha.2.2, hb.2.2] at he
        have hh := (schedule level).injective (placement schedule level a) (placement schedule level b)
          (i - (networkWalk schedule level a).length) (j - (networkWalk schedule level b).length)
          ha.2.1 hb.2.1 (translate_injective _ he)
        exact (placement schedule level).injective hh.1

end Maxwell.Logical.Routing.Walk
