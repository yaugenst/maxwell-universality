import Maxwell.Cost.RationalCanonical.Quotient
import Maxwell.Cost.RationalCanonical.Value

set_option maxHeartbeats 800000
namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

/-- Persistent fraction inputs228/229; canonical outputs230/231. -/
def normalizeCode : Code :=
  .seq (.call (WordTransfer.clone 228 220)) <|
  .seq (.call (WordTransfer.clone 229 221)) <|
  .seq gcdCode <|
  .seq (.call (WordTransfer.move 220 221)) <|
  .seq (quotientCode 228 230) <|
  .seq (quotientCode 229 231) (.call (TapeOps.clear 221))

structure NormalizeReady (s : BitRAMState) (a b : ℕ) : Prop where
  numerator : Word s 228 a
  denominator : Word s 229 b
  work : Ready s 0 0
  outputNumerator : Blank s 230
  outputDenominator : Blank s 231

structure NormalizeDone (s : BitRAMState) (a b : ℕ) : Prop where
  numerator : Word s 228 a
  denominator : Word s 229 b
  work : Ready s 0 0

structure NormalizeFrame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ ({0,1,2,3,4,220,221,222,223,228,229,230,231} : Finset ℕ) →
    t.tapes i = s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 →
    i ≠ 80 → i ≠ 81 → t.registers i = s.registers i

theorem NormalizeFrame.trans {s t u : BitRAMState} (h : NormalizeFrame s t)
    (k : NormalizeFrame t u) : NormalizeFrame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi),
    fun i hi h24 h25 h26 h27 h80 h81 => (k.registers i hi h24 h25 h26 h27 h80 h81).trans
      (h.registers i hi h24 h25 h26 h27 h80 h81)⟩

theorem NormalizeFrame.ofDivision {s t : BitRAMState} {changed : Finset ℕ}
    (h : DivisionFrame changed s t)
    (hc : changed ⊆ {0,1,2,3,4,220,221,222,223,228,229,230,231}) : NormalizeFrame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,
    fun i hi => h.tapes i (fun hm => hi (hc hm)),
    fun i hi h24 h25 h26 h27 _ _ => h.registers i hi h24 h25 h26 h27⟩

theorem NormalizeFrame.ofGCD {s t : BitRAMState} (h : GCDFrame s t) : NormalizeFrame s t := by
  refine ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,?_,h.registers⟩
  intro i hi
  apply h.tapes i
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi ⊢
  tauto

theorem GCDFrame.word {s t : BitRAMState} (h : GCDFrame s t) {i a : ℕ}
    (hi : i ∉ ({0,1,2,3,4,220,221,222,223} : Finset ℕ)) (hw : Word s i a) : Word t i a :=
  word_of_eq (h.tapes i hi) hw

theorem GCDFrame.blank {s t : BitRAMState} (h : GCDFrame s t) {i : ℕ}
    (hi : i ∉ ({0,1,2,3,4,220,221,222,223} : Finset ℕ)) (hw : Blank s i) : Blank t i :=
  blank_of_eq (h.tapes i hi) hw

def normalizeBudget (a b : ℕ) : ℕ :=
  4+2*b.size*(2000*(2*(a.size+b.size)+2)^2+4) +
    4000*(2*(a.size+b.size)+2)^2+100*(a.size+b.size+2)

theorem normalize (input : List Bool) (tape : ℕ → Bool) (a b : ℕ) (hb : 0 < b)
    (s : Store) (hs : NormalizeReady s.val a b) :
    ∃ cost t, cost ≤ normalizeBudget a b ∧ Executes input tape normalizeCode cost s t ∧
      Word t.val 230 (a/Nat.gcd a b) ∧ Word t.val 231 (b/Nat.gcd a b) ∧
      NormalizeDone t.val a b ∧ NormalizeFrame s.val t.val := by
  obtain ⟨u,e1,a1,w1,f1⟩ := clone_word 228 220 a (by decide) input tape s hs.numerator hs.work.first
  have F1 := transferFrame 228 220 f1
  obtain ⟨v,e2,b2,w2,f2⟩ := clone_word 229 221 b (by decide) input tape u
    (F1.word (by decide) hs.denominator) (F1.word (by decide) hs.work.second)
  have F2 := transferFrame 229 221 f2
  have fv := F1.trans F2
  have hv : Ready v.val a b := ⟨F2.word (by decide) w1,w2,
    fv.blank (by decide) hs.work.quotient,fv.blank (by decide) hs.work.remainder,
    fun i hi => fv.blank (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)
      (hs.work.scratch i hi)⟩
  obtain ⟨gc,w,hgc,e3,hw,f3⟩ := gcd input tape a b v hv
  obtain ⟨x,e4,z4,g4,f4⟩ := move_word 220 221 (Nat.gcd a b) (by decide) input tape w hw.first hw.second
  have F4 := transferFrame 220 221 f4
  have hx : Ready x.val 0 (Nat.gcd a b) := ⟨z4,g4,F4.blank (by decide) hw.quotient,
    F4.blank (by decide) hw.remainder,
    fun i hi => F4.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) (hw.scratch i hi)⟩
  have ga := Nat.gcd_pos_of_pos_right a hb
  obtain ⟨nc,y,hnc,e5,ny,ay,hy,f5⟩ := quotient 228 230 a (Nat.gcd a b)
    (by decide) (by decide) (by decide) ga (Nat.gcd_dvd_left a b) input tape x
    (F4.word (by decide) (f3.word (by decide) (F2.word (by decide) a1))) hx
    (F4.blank (by decide) (f3.blank (by decide) (fv.blank (by decide) hs.outputNumerator)))
  obtain ⟨dc,z,hdc,e6,dz,bz,hz,f6⟩ := quotient 229 231 b (Nat.gcd a b)
    (by decide) (by decide) (by decide) ga (Nat.gcd_dvd_right a b) input tape y
    (f5.word (by decide) (F4.word (by decide) (f3.word (by decide) b2))) hy
    (f5.blank (by decide) (F4.blank (by decide) (f3.blank (by decide)
      (fv.blank (by decide) hs.outputDenominator))))
  obtain ⟨t,e7,z7,f7⟩ := clear_word 221 (Nat.gcd a b) input tape z hz.second
  have F7 := transferFrame 221 221 f7
  have ff : NormalizeFrame s.val t.val := by
    apply (NormalizeFrame.ofDivision fv (by decide)).trans
    apply (NormalizeFrame.ofGCD f3).trans
    exact NormalizeFrame.ofDivision (F4.trans (f5.trans (f6.trans F7))) (by decide)
  refine ⟨(15*a.bits.length+17)+((15*b.bits.length+17)+(gc+((12*(Nat.gcd a b).bits.length+11)+
    (nc+(dc+(6*(Nat.gcd a b).bits.length+4)))))),t,?_,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7))))),
    (f6.trans F7).word (by decide) ny,F7.word (by decide) dz,?_,ff⟩
  · have hg : (Nat.gcd a b).size ≤ b.size := Nat.size_le_size (Nat.gcd_le_right a hb)
    have hn : a.bits.length+(Nat.gcd a b).bits.length+2 ≤ 2*(a.size+b.size)+2 := by
      simp only [Nat.size_eq_bits_len]; omega
    have hd : b.bits.length+(Nat.gcd a b).bits.length+2 ≤ 2*(a.size+b.size)+2 := by
      simp only [Nat.size_eq_bits_len]; omega
    have hn2 := Nat.pow_le_pow_left hn 2
    have hd2 := Nat.pow_le_pow_left hd 2
    simp only [Nat.size_eq_bits_len] at *
    unfold normalizeBudget
    nlinarith
  · refine ⟨(f6.trans F7).word (by decide) ay,F7.word (by decide) bz,
      ⟨F7.word (by decide) hz.first,z7,F7.blank (by decide) hz.quotient,
       F7.blank (by decide) hz.remainder,
       fun i hi => F7.blank (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega) (hz.scratch i hi)⟩⟩

end Maxwell.Cost.RationalCanonical
