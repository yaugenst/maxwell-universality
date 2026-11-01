import Maxwell.Cost.Structured.Footprint
import Maxwell.Continuum.CalibrationInverseOutputIndex

/-! The rational readout uses an address computed from the retained inverse
countdown. Its state permits repeated reads without assuming new blank words. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputPoint
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure State {n : ℕ} (a : Snapshot n) (D : ℕ) (v : ℕ→ℕ) (s : BitRAMState) : Prop where
  stored : Horner.Stored a.data a.words s
  ports : Horner.Ports a.data 10 11 5 4 s
  scratch : BankArray.Scratch s
  seven : RationalAccumulator.Blank s 7
  bank : NatAssign.Bank OutputRead.ids v s
  denominator : RationalAccumulator.Word s 532 D

theorem initial {n D : ℕ} {a : Snapshot n} {s : BitRAMState} (h : OutputPrepare.Ready a D s) :
    State a D (fun _=>0) s := ⟨h.stored,h.ports,h.scratch,h.seven,h.bank,h.denominator⟩

theorem entry_width {n D B : ℕ} {a : Snapshot n} {s : BitRAMState}
    (stored : Horner.Stored a.data a.words s) (size:a.data.Sized B) (denWidth:D.bits.length≤B)
    (i : Fin n) : (OutputRead.entryParts a D i).Width B := by
  have entry (k : Fin 12) : (addressValue ((a.words k).get i)).bits.length≤B := by
    have h:(addressValue ((a.words k).get i)).bits.length≤((a.words k).get i).length:=by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length _)
    rw [(stored.arrays k).length i] at h
    exact h.trans size.2.1
  exact ⟨entry 10,entry 11,denWidth⟩

theorem State.index_frame {n D : ℕ} {a : Snapshot n} {v : ℕ→ℕ} {s t : BitRAMState}
    (h : State a D v s) (f : BinaryPrecision.Frame OutputIndex.changed s t)
    (zero : NatAssign.Scratch t) : State a D v t := by
  have keep (k : ℕ) (hk:4≤k) (ho:k≠140 ∧ k≠530 ∧ k≠531 ∧ k≠533 ∧ k≠534) : t.tapes k=s.tapes k := by
    apply f.tapes
    simp only [OutputIndex.changed,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨h.stored.of_memory_tapes f.memory ?_,?_,?_,
    RationalAccumulator.blank_of_eq (keep 7 (by decide) (by decide)) h.seven,?_,
    RationalAccumulator.word_of_eq (keep 532 (by decide) (by decide)) h.denominator⟩
  · intro k hk
    simp only [Horner.Metadata] at hk
    exact keep k (by omega) (by omega)
  · exact ⟨BankArray.word_of_eq (keep 112 (by decide) (by decide)) h.ports.inputPositive,
      BankArray.word_of_eq (keep 113 (by decide) (by decide)) h.ports.inputNegative,
      BankArray.word_of_eq (keep 114 (by decide) (by decide)) h.ports.outputPositive,
      BankArray.word_of_eq (keep 115 (by decide) (by decide)) h.ports.outputNegative⟩
  · exact ⟨zero 0 (by decide),zero 1 (by decide),zero 2 (by decide),zero 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) h.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) h.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  · intro k hk
    have bounds:30≤k ∧ k≤32:=by
      simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact RationalAccumulator.word_of_eq (keep k (by omega) (by omega)) (h.bank k hk)

def code (ν : Alias) (j : Fin 3) : Code := .seq (OutputIndex.code ν j) OutputRead.code
def readWidth (A B : ℕ) : ℕ := 2^19*(A+1)+B
def costBound (A B : ℕ) : ℕ := 3000*8^19*(A+2)^2+2^20*(readWidth A B+5)^2
def coldIds : Finset ℕ := {33,34,35,36,102,103,104,105,106}

theorem executes (N D A B : ℕ) (ν : Alias) (bounds:∀j,|ν j|≤2) (j : Fin 3)
    (a : Snapshot (aliasArraySize (N+3))) (n v : ℕ→ℕ)
    (hA:3≤A) (size:a.data.Sized B) (denWidth:D.bits.length≤B)
    (indexWidth:∀k∈OutputPrepare.indexIds,(n k).bits.length≤A)
    (valueWidth:∀k∈OutputRead.ids,(v k).bits.length≤B) (count:n 304=N)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state : State a D v s.val) (indexBank : NatAssign.Bank OutputPrepare.indexIds n s.val) :
    let i:=OutputIndex.index N ν bounds j
    let nf:=NatAssign.values (OutputIndex.plan ν j) n
    let vf:=OutputRead.values a D i v
    ∃cost t, Executes input tape (code ν j) cost s t ∧ cost≤costBound A B ∧
      State a D vf t.val ∧ NatAssign.Bank OutputPrepare.indexIds nf t.val ∧
      (∀k∈OutputPrepare.indexIds,(nf k).bits.length≤2^19*(A+1)) ∧
      (∀k∈OutputRead.ids,(vf k).bits.length≤B) ∧
      (OutputRead.entryParts a D i).value=extendAliasArray (N+3)
        (Vector.ofFn (fun k=>((Horner.channels a.words 10 11).value k:ℚ)/(D:ℚ))) ν j ∧
      t.val.memory=s.val.memory ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀k,600≤k→t.val.tapes k=s.val.tapes k) ∧
      (∀k∈coldIds,t.val.tapes k=s.val.tapes k) ∧
      (∀k,(k=4 ∨ k=37 ∨ 107 ≤ k)→k<1000→k≠140→(k<530 ∨ 534<k)→t.val.tapes k=s.val.tapes k) := by
  dsimp only
  have zero : NatAssign.Scratch s.val := by
    intro k hk
    interval_cases k
    · exact state.scratch.1
    · exact state.scratch.2.1
    · exact state.scratch.2.2.1
    · exact state.scratch.2.2.2.1
  obtain ⟨c0,u,e0,bound0,nb,z,iw,ww,frame⟩:=
    OutputIndex.executes ν bounds j n A hA indexWidth input tape s indexBank zero
  have state1:=state.index_frame frame z
  have sz:a.data.Sized (readWidth A B):=by
    rcases size with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1.trans (by unfold readWidth;omega),h2.trans (by unfold readWidth;omega),
      h3.trans (by unfold readWidth;omega),h4.trans (by unfold readWidth;omega),
      fun k=>(h5 k).trans (by unfold readWidth;omega),h6.trans (by unfold readWidth;omega),
      h7.trans (by unfold readWidth;omega)⟩
  have ilen:(OutputIndex.index N ν bounds j).val.bits.length≤readWidth A B:=by
    have w:=ww 140 (by decide)
    rw [OutputIndex.value,count,←OutputIndex.index_value] at w
    exact w.trans (by unfold readWidth;omega)
  obtain ⟨c1,t,e1,bound1,bank1,scratch1,seven1,stored1,ports1,readFrame⟩:=
    OutputRead.executes a D (readWidth A B) (OutputIndex.index N ν bounds j) sz
      (denWidth.trans (by unfold readWidth;omega)) v
      (fun k hk=>(valueWidth k hk).trans (by unfold readWidth;omega))
      input tape (OutputIndex.index N ν bounds j).val.bits (addressValue_bits _) ilen u
      state1.stored state1.ports state1.scratch state1.seven state1.bank
      (by simpa only [RationalAccumulator.Word,BankArray.Word,OutputIndex.index_value,count] using iw) state1.denominator
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add bound0 bound1,
    ⟨stored1,ports1,scratch1,seven1,bank1,?_,⟩,?_,ww,?_,?_,readFrame.memory.trans frame.memory,
    readFrame.inputHead.trans frame.inputHead,readFrame.randomCursor.trans frame.randomCursor,
    readFrame.output.trans frame.output,?_,?_,?_⟩
  · exact RationalAccumulator.word_of_eq (readFrame.tapes 532 (by decide) (by decide)) state1.denominator
  · intro k hk
    have external:k∉OutputRead.ids:=by
      simp only [OutputPrepare.indexIds,Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton]
      omega
    have lo:10≤k:=by
      simp only [OutputPrepare.indexIds,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    exact RationalAccumulator.word_of_eq (readFrame.tapes k lo external) (nb k hk)
  · intro k hk
    have ew:=entry_width state.stored size denWidth (OutputIndex.index N ν bounds j)
    simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl
    · simpa only [OutputRead.values,Function.update_of_ne (by decide : (30:ℕ)≠32),
        Function.update_of_ne (by decide : (30:ℕ)≠31),Function.update_self] using ew.1
    · simpa only [OutputRead.values,Function.update_of_ne (by decide : (31:ℕ)≠32),Function.update_self] using ew.2.1
    · simpa only [OutputRead.values,Function.update_self] using denWidth
  · rw [OutputRead.entryParts_value]
    simp only [extendAliasArray,OutputIndex.in_cube N ν bounds,↓reduceDIte,vector_get_ofFn,
      OutputIndex.index]
  · intro k hk
    have hi:k∉OutputRead.ids:=by simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton];omega
    have hc:k∉OutputIndex.changed:=by
      simp only [OutputIndex.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (readFrame.tapes k (by omega) hi).trans (frame.tapes k hc)
  · intro k hk
    simp only [coldIds,Finset.mem_insert,Finset.mem_singleton] at hk
    apply (readFrame.tapes k (by omega) ?_).trans (frame.tapes k ?_)
    · simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton];omega
    · simp only [OutputIndex.changed,Finset.mem_insert,Finset.mem_singleton];omega

  · intro k lo hi ne outside
    have after : t.val.tapes k=u.val.tapes k := by
      by_cases four:k=4
      · subst k;exact e1.protectsTape 4 (by decide)
      · apply readFrame.tapes k (by omega)
        simp only [OutputRead.ids,Finset.mem_insert,Finset.mem_singleton];omega
    apply after.trans (frame.tapes k ?_)
    simp only [OutputIndex.changed,Finset.mem_insert,Finset.mem_singleton];omega

#print axioms executes
end Maxwell.Continuum.Calibration.NeumannMachine.OutputPoint
