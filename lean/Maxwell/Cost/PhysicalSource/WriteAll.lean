import Maxwell.Cost.PhysicalSource.Footprint

/-! One finite seed-record write updates the three separated dense arrays. -/
namespace Maxwell.Cost.PhysicalSource.Overlay
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

def written {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    (i : Fin n) (v : Fin 3→ℕ) : Fin 3→Vector (List Bool) n :=
  fun port => (words port).set i (FixedWidth.bits (addressValue l.width) (v port).bits)

def writeAllCode : Code := .seq (writeCode 0) (.seq (writeCode 1) (writeCode 2))

def writeMemory {n : ℕ} (l : Layout n) (memory : ℕ→Bool) (i : Fin n) (v : Fin 3→ℕ) : ℕ→Bool :=
  let first := MemoryWord.writeBits memory (addressValue (l.bases 0)+i.val*addressValue l.width)
    (FixedWidth.bits (addressValue l.width) (v 0).bits)
  let second := MemoryWord.writeBits first (addressValue (l.bases 1)+i.val*addressValue l.width)
    (FixedWidth.bits (addressValue l.width) (v 1).bits)
  MemoryWord.writeBits second (addressValue (l.bases 2)+i.val*addressValue l.width)
    (FixedWidth.bits (addressValue l.width) (v 2).bits)

private theorem frame_trans {s t u : BitRAMState} (h : BankArray.FrameExcept 37 s t)
    (k : BankArray.FrameExcept 37 t u) : BankArray.FrameExcept 37 s u :=
  ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
    fun i hi hn => (k.2.2.2.1 i hi hn).trans (h.2.2.2.1 i hi hn),
    fun i hi h24 h25 h26 h27 h28 h29 => (k.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
      (h.2.2.2.2 i hi h24 h25 h26 h27 h28 h29)⟩

private theorem keep_value {s t : BitRAMState} (h : BankArray.FrameExcept 37 s t)
    (v : Fin 3→ℕ) (hv : ∀ port, Word s (valueTape port) (v port)) :
    ∀ port, Word t (valueTape port) (v port) := by
  intro port
  exact word_of_eq (h.2.2.2.1 (valueTape port)
    (by right; dsimp [valueTape]; omega) (by dsimp [valueTape]; omega)) (hv port)

/-- Every array readout of the written slot equals the supplied exact seed
pair; all three addressed writes and fixed-width packing are executed. -/
theorem write_all {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    (i : Fin n) (v : Fin 3→ℕ) (B : ℕ) (hl : l.Sized B)
    (hfit : ∀ port, (v port).bits.length≤addressValue l.width)
    (input : List Bool) (tape : ℕ→Bool) (index : List Bool)
    (hi : addressValue index=i.val) (hil : index.length≤B) (s : Store)
    (hs : Ready s.val) (h37 : Blank s.val 37) (hd : Stored l words s.val)
    (hindex : BankArray.Word s.val 333 index) (hv : ∀ port, Word s.val (valueTape port) (v port)) :
    ∃ cost t, cost≤120000*(B+2)^2 ∧ Executes input tape writeAllCode cost s t ∧
      Ready t.val ∧ Blank t.val 37 ∧ Stored l (written l words i v) t.val ∧
      t.val.memory=writeMemory l s.val.memory i v ∧ BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨c0,a,h0,e0,ar,a37,ad,am,af⟩ := write l words 0 i (v 0) B hl (hfit 0)
    input tape index hi hil s hs h37 hd hindex (hv 0)
  obtain ⟨c1,b,h1,e1,br,b37,bd,bm,bf⟩ := write l _ 1 i (v 1) B hl (hfit 1)
    input tape index hi hil a ar a37 ad
    (BankArray.word_of_eq (af.2.2.2.1 333 (by decide) (by decide)) hindex) (keep_value af v hv 1)
  have ab := frame_trans af bf
  obtain ⟨c2,t,h2,e2,tr,t37,td,tm,tf⟩ := write l _ 2 i (v 2) B hl (hfit 2)
    input tape index hi hil b br b37 bd
    (BankArray.word_of_eq (ab.2.2.2.1 333 (by decide) (by decide)) hindex) (keep_value ab v hv 2)
  refine ⟨c0+(c1+c2),t,by omega,e0.seq (e1.seq e2),tr,t37,?_,?_,frame_trans ab tf⟩
  · convert td using 1
    funext port
    fin_cases port <;> simp [written,Function.update]
  · rw [tm,bm,am]
    rfl

theorem written_value {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    (i : Fin n) (v : Fin 3→ℕ) (hfit : ∀ port, (v port).bits.length≤addressValue l.width) :
    value (written l words i v) i = ((v 0:ℚ)-v 1)/v 2 := by
  have hw (port : Fin 3) : (written l words i v port).get i =
      FixedWidth.bits (addressValue l.width) (v port).bits := by
    simp [written,Vector.get,Fin.cast]
  rw [value,hw,hw,hw]
  rw [FixedWidth.bits_value _ _ (hfit 0),FixedWidth.bits_value _ _ (hfit 1),
    FixedWidth.bits_value _ _ (hfit 2)]
  simp only [addressValue_bits]

theorem written_value_function {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    (i : Fin n) (v : Fin 3→ℕ) (hfit : ∀ port, (v port).bits.length≤addressValue l.width) :
    value (written l words i v)=Function.update (value words) i (((v 0:ℚ)-v 1)/v 2) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp only [Function.update_self,written_value l words i v hfit]
  · rw [Function.update_of_ne hj]
    have hw (port : Fin 3) : (written l words i v port).get j = (words port).get j := by
      simp [written,Vector.get,Fin.cast,Ne.symm (Fin.val_ne_of_ne hj)]
    rw [value,hw,hw,hw,value]

/-- The three writes preserve every memory location outside their allocated
arrays, so retained calibration and routing arrays can be reused. -/
theorem writeMemory_outside {n : ℕ} (l : Layout n) (memory : ℕ→Bool)
    (i : Fin n) (v : Fin 3→ℕ) (p : ℕ)
    (hp : ∀ port, p<addressValue (l.bases port) ∨
      addressValue (l.bases port)+n*addressValue l.width≤p) :
    writeMemory l memory i v p=memory p := by
  have outside (port : Fin 3) : p<addressValue (l.bases port)+i.val*addressValue l.width ∨
      addressValue (l.bases port)+i.val*addressValue l.width+
        (FixedWidth.bits (addressValue l.width) (v port).bits).length≤p := by
    rw [FixedWidth.bits_length]
    rcases hp port with h|h
    · left; omega
    · right
      have hi := Nat.mul_le_mul_right (addressValue l.width) (show i.val+1≤n by omega)
      nlinarith only [h,hi]
  unfold writeMemory
  rw [MemoryWord.writeBits_outside _ _ _ _ (outside 2),
    MemoryWord.writeBits_outside _ _ _ _ (outside 1),
    MemoryWord.writeBits_outside _ _ _ _ (outside 0)]

theorem Outside.of_write_all {n : ℕ} (l : Layout n) (i : Fin n) (v : Fin 3→ℕ)
    {s t : BitRAMState} (hm : t.memory=writeMemory l s.memory i v) : Outside l s t := by
  intro p hp
  rw [hm]
  exact writeMemory_outside l s.memory i v p hp

end Maxwell.Cost.PhysicalSource.Overlay
