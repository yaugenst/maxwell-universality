import Maxwell.Cost.PositiveGraph.Initialize.Step

namespace Maxwell.Cost.PositiveGraph.Initialize
open Structured
open RationalAccumulator (Blank)
open CalibrationMatrix (fillPrefix)

theorem ready_transfer (p : Ports) (width base clock : List Bool) (value : ℕ)
    (s t : BitRAMState) (h : Ready p width base clock value s)
    (hk : ∀ i, i ≠ 160 → i ≠ 161 → t.tapes i=s.tapes i) : Ready p width base clock value t := by
  have hw := p.valid p.width (by simp)
  have hb := p.valid p.base (by simp)
  have hc := p.valid p.clock (by simp)
  obtain ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩ := h.scratch
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (hk 0 (by omega) (by omega)) h0
  · exact RationalAccumulator.blank_of_eq (hk 1 (by omega) (by omega)) h1
  · exact RationalAccumulator.blank_of_eq (hk 2 (by omega) (by omega)) h2
  · exact RationalAccumulator.blank_of_eq (hk 3 (by omega) (by omega)) h3
  · exact RationalAccumulator.blank_of_eq (hk 5 (by omega) (by omega)) h5
  · exact RationalAccumulator.blank_of_eq (hk 6 (by omega) (by omega)) h6
  · exact RationalAccumulator.blank_of_eq (hk 8 (by omega) (by omega)) h8
  · exact RationalAccumulator.blank_of_eq (hk 9 (by omega) (by omega)) h9
  · exact RationalAccumulator.blank_of_eq (hk 7 (by omega) (by omega)) h.seven
  · exact RationalAccumulator.blank_of_eq (hk 37 (by omega) (by omega)) h.temporary
  · exact BankArray.word_of_eq (hk p.width (by omega) (by omega)) h.widthWord
  · exact BankArray.word_of_eq (hk p.base (by omega) (by omega)) h.baseWord
  · exact BankArray.word_of_eq (hk p.clock (by omega) (by omega)) h.clockWord
  · exact RationalAccumulator.word_of_eq (hk 162 (by omega) (by omega)) h.valueWord

private theorem frame_counter {s t : Store} (h : CountedShifted.Frame 161 s t) : Frame s.val t.val :=
  ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,
    fun i _ _ _ hi _ => h.2.2.2.2.2.1 i hi,
    fun i hi h24 h25 _ _ _ h29 => h.2.2.2.2.2.2 i (by omega) h24 h25 h29⟩

def Invariant {n : ℕ} (p : Ports) (width base clock : List Bool) (value B : ℕ)
    (initialWords : Vector (List Bool) n) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool, addressValue index=n-remaining ∧ index.length ≤ B ∧
    BankArray.Word s.val 160 index ∧ Ready p width base clock value s.val ∧
    BitArray.Represents s.val.memory (addressValue base) (addressValue width)
      (fillPrefix initialWords (fun _ => FixedWidth.bits (addressValue width) value.bits) (n-remaining)) ∧
    Outside (addressValue base) (addressValue width) n initial s.val ∧ Frame initial s.val

private theorem invariant_stable {n : ℕ} (p : Ports) (width base clock : List Bool) (value B : ℕ)
    (initialWords : Vector (List Bool) n) (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (h : CountedShifted.Frame 161 s t) (hs : Invariant p width base clock value B initialWords initial remaining s) :
    Invariant p width base clock value B initialWords initial remaining t := by
  obtain ⟨hr,i,hi,hil,hw,hready,ha,ho,hf⟩ := hs
  refine ⟨hr,i,hi,hil,BankArray.word_of_eq (h.2.2.2.2.2.1 160 (by omega)) hw,
    ready_transfer p width base clock value s.val t.val hready (fun j _ hj => h.2.2.2.2.2.1 j hj),
    ?_,ho.trans (Outside.of_memory h.2.2.1),hf.trans (frame_counter h)⟩
  simpa only [h.2.2.1] using ha

def loopCode (p : Ports) : Code := .seq (CountedShifted.code 161 (rowCode p))
  (.seq (.call (TapeOps.clear 161)) (.call (TapeOps.clear 160)))

def loopCost (n B : ℕ) : ℕ := (n+1)*(13*B+15)+n*(20000*(B+2)^2)+12*B+8

theorem loop_executes {n : ℕ} (p : Ports) (width base clock index count : List Bool) (value B : ℕ)
    (words : Vector (List Bool) n) (hw : width.length ≤ B) (hb : base.length ≤ B)
    (hi : index.length ≤ B) (hcount : count.length ≤ B)
    (hwp : 0<width.length) (hvp : 0<addressValue width) (hv : addressValue width ≤ B)
    (hc : clock.length=addressValue width) (hfit : value.bits.length ≤ addressValue width)
    (hn : n<2^B) (hindex : addressValue index=0) (hcountval : addressValue count=n)
    (input : List Bool) (tape : ℕ → Bool) (origin : ℤ) (s : Store)
    (hr : Ready p width base clock value s.val) (h160 : BankArray.Word s.val 160 index)
    (h161 : s.val.tapes 161=BitTape.shifted count origin)
    (harray : BitArray.Represents s.val.memory (addressValue base) (addressValue width) words) :
    ∃ cost t, cost ≤ loopCost n B ∧ Executes input tape (loopCode p) cost s t ∧
      Ready p width base clock value t.val ∧ Blank t.val 160 ∧ Blank t.val 161 ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        (Vector.ofFn fun _ : Fin n => FixedWidth.bits (addressValue width) value.bits) ∧
      Outside (addressValue base) (addressValue width) n s.val t.val ∧ Frame s.val t.val := by
  let inv := Invariant p width base clock value B words s.val
  have stable := invariant_stable p width base clock value B words s.val
  have body : ∀ r xs u, inv (r+1) u → u.val.tapes 161=BitTape.shifted xs origin → addressValue xs=r →
      ∃ steps t, Executes input tape (rowCode p) steps u t ∧ inv r t ∧
        t.val.tapes 161=BitTape.shifted xs origin ∧ steps ≤ 20000*(B+2)^2 := by
    intro r xs u hu hword _
    obtain ⟨hrem,idx,hidx,hidxl,hui,hur,hua,huo,huf⟩ := hu
    let i : Fin n := ⟨n-(r+1),by omega⟩
    obtain ⟨steps,t,hsteps,he,htr,hti,htil,hta,hto,htf,htc⟩ := row p width base clock idx value B
      (fillPrefix words (fun _ => FixedWidth.bits (addressValue width) value.bits) (n-(r+1))) i
      hw hb hidxl hwp hvp hv hc hfit hn hidx input tape u hur hui hua
    have hnext : n-r=i.val+1 := by dsimp [i]; omega
    refine ⟨steps,t,he,⟨by omega,Increment.bits idx,?_,htil,hti,htr,?_,huo.trans hto,huf.trans htf⟩,
      htc.trans hword,hsteps⟩
    · rw [Increment.bits_value,hidx]
      omega
    · rw [hnext]
      change BitArray.Represents t.val.memory (addressValue base) (addressValue width)
        ((fillPrefix words (fun _ => FixedWidth.bits (addressValue width) value.bits) i.val).set i
          (FixedWidth.bits (addressValue width) value.bits)) at hta
      rwa [CalibrationMatrix.fillPrefix_step] at hta
  have hstart : inv n s := by
    refine ⟨le_rfl,index,by simpa using hindex,hi,h160,hr,?_,Outside.refl _ _ _ _,Frame.refl _⟩
    simpa using harray
  obtain ⟨steps,a,last,ea,haInv,haCount,haLen,_haTest,haCost⟩ :=
    CountedShifted.executes 161 origin (rowCode p) input tape inv (fun _ => 20000*(B+2)^2)
      stable body n count s hcountval h161 hstart
  obtain ⟨_,idx,_hidx,hidxl,hai,har,haa,hao,haf⟩ := haInv
  obtain ⟨b,eb,bt,bf⟩ := WordCall.clear 161 input tape last origin a haCount
  obtain ⟨io,hiword⟩ := hai
  have bi : b.val.tapes 160=BitTape.shifted idx io := by simpa [bt] using hiword
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 160 input tape idx io b bi
  have keep (j : ℕ) (hj160 : j ≠ 160) (hj161 : j ≠ 161) : t.val.tapes j=a.val.tapes j := by
    simp [tt,bt,hj160,hj161]
  have tm : t.val.memory=a.val.memory := tf.2.2.1.trans bf.2.2.1
  have fab : Frame a.val b.val := ⟨bf.2.1,bf.2.2.2.1,bf.2.2.2.2.1,
    fun j _ _ _ hj _ => by simp [bt,hj],fun j _ _ _ h26 h27 _ _ => bf.2.2.2.2.2.2 j h26 h27⟩
  have fbt : Frame b.val t.val := ⟨tf.2.1,tf.2.2.2.1,tf.2.2.2.2.1,
    fun j _ _ hj _ _ => by simp [tt,hj],fun j _ _ _ h26 h27 _ _ => tf.2.2.2.2.2.2 j h26 h27⟩
  refine ⟨steps+(6*last.length+4+(6*idx.length+4)),t,?_,ea.seq (eb.seq et),
    ready_transfer p width base clock value a.val t.val har keep,⟨io+idx.length,by simp [tt]⟩,
    ⟨origin+last.length,by simp [tt,bt]⟩,?_,hao.trans (Outside.of_memory tm),haf.trans (fab.trans fbt)⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at haCost
    have hl : last.length ≤ B := haLen.trans_le hcount
    have hh : (n+1)*(13*count.length+15) ≤ (n+1)*(13*B+15) := by gcongr
    dsimp [loopCost]
    omega
  · simpa only [tm,Nat.sub_zero,CalibrationMatrix.fillPrefix_full] using haa

end Maxwell.Cost.PositiveGraph.Initialize
