import Maxwell.Cost.CalibrationMatrix.Horner.Store
import Maxwell.Cost.WordSwap

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

def mutableTapes : List ℕ :=
  [37,102,103,104,106,108,109,112,113,114,115,120,121,122,123,128,129,132,133,140]

def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ∉ mutableTapes → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
    fun i hi hj hk => (k.2.2.2.1 i hi hj hk).trans (h.2.2.2.1 i hi hj hk),
    fun i hi a b c d e f => (k.2.2.2.2 i hi a b c d e f).trans (h.2.2.2.2 i hi a b c d e f)⟩

theorem Frame.of_power {s t : BitRAMState} (h : CalibrationMatrix.PowerFrame s t) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,h.2.2.2.2⟩
  intro i hi hj hk
  simp only [mutableTapes,List.mem_cons,not_or] at hk
  apply h.2.2.2.1 i hi hj <;> omega

theorem Frame.of_swap {left right temp : ℕ} {s t : BitRAMState}
    (hl : left ∈ mutableTapes) (hr : right ∈ mutableTapes) (ht : temp ∈ mutableTapes)
    (h : WordSwap.Frame left right temp s t) : Frame s t :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i _ _ hi => h.2.2.2.2.2.1 i (fun he => hi (he ▸ hl))
      (fun he => hi (he ▸ hr)) (fun he => hi (he ▸ ht)),
    fun i _ h24 h25 h26 h27 _ _ => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

def Outside {n : ℕ} (d : Data n) (s t : BitRAMState) : Prop :=
  ∀ a, (∀ i, a < addressValue (d.bases i) ∨ addressValue (d.bases i)+n*addressValue d.width ≤ a) →
    t.memory a = s.memory a

theorem Outside.refl {n : ℕ} (d : Data n) (s : BitRAMState) : Outside d s s := fun _ _ => rfl

theorem Outside.trans {n : ℕ} {d : Data n} {s t u : BitRAMState}
    (h : Outside d s t) (k : Outside d t u) : Outside d s u := fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_memory {n : ℕ} {d : Data n} {s t : BitRAMState} (h : t.memory = s.memory) : Outside d s t := by
  intro a _;rw [h]

theorem Outside.of_output {n : ℕ} {d : Data n} {s t : BitRAMState} {p q : Fin 12}
    (h : OutputOutside ⟨d.bases p,d.bases q⟩ n (addressValue d.width) s t) : Outside d s t :=
  fun a ha => h a (ha p) (ha q)

def Data.permute {n : ℕ} (d : Data n) (e : Equiv.Perm (Fin 12)) : Data n :=
  {d with bases := fun i => d.bases (e i)
          separated := fun _i _j h => d.separated _ _ (fun he => h (e.injective he))
          matrixPositive_separated := fun i => d.matrixPositive_separated (e i)
          matrixNegative_separated := fun i => d.matrixNegative_separated (e i)}

theorem Data.Sized.permute {n B : ℕ} {d : Data n} (h : d.Sized B) (e : Equiv.Perm (Fin 12)) :
    (d.permute e).Sized B :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i => h.2.2.2.2.1 (e i),h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem Outside.permute {n : ℕ} {d : Data n} {s t : BitRAMState} (e : Equiv.Perm (Fin 12)) :
    Outside (d.permute e) s t ↔ Outside d s t := by
  constructor
  · intro h a ha
    exact h a (fun i => ha (e i))
  · intro h a ha
    exact h a (fun i => by simpa only [Data.permute,Equiv.apply_symm_apply] using ha (e.symm i))

end Maxwell.Cost.CalibrationMatrix.Horner
