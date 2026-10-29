import Maxwell.Cost.RationalCanonical.Emit

namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

def signCode : Code :=
  .seq (.atom (.readTape 228 80 81)) (.atom (.bitAnd 23 23 81))

def signedState (s : Store) : Store :=
  let t := Store.ofState (readTapeState s.val 228 80 81)
  Store.ofState (t.val.setRegister 23 (t.val.registers 23 && t.val.registers 81))

theorem sign (input : List Bool) (tape : ℕ → Bool) (negative : Bool) (a b : ℕ)
    (s : Store) (hs : NormalizeReady s.val a b) (hsgn : s.val.registers 23 = negative) :
    Executes input tape signCode 5 s (signedState s) ∧
      NormalizeReady (signedState s).val a b ∧
      (signedState s).val.registers 23 = (negative && decide (a ≠ 0)) ∧
      (signedState s).val.output = s.val.output ∧ EmitFrame s.val (signedState s).val := by
  have hr : Executes input tape (.atom (.readTape 228 80 81)) 3 s
      (Store.ofState (readTapeState s.val 228 80 81)) := by
    apply Executes.atom (extra := 1)
    · simp [BitRAM.next,s.property,readTapeState]
    · simp [readTapeState,s.property]
  refine ⟨hr.seq (Executes.bitAnd input tape _ 23 23 81),
    ⟨hs.numerator,hs.denominator,
      ⟨hs.work.first,hs.work.second,hs.work.quotient,hs.work.remainder,hs.work.scratch⟩,
      hs.outputNumerator,hs.outputDenominator⟩,?_,rfl,
    ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl,?_⟩⟩
  · obtain ⟨origin,ho⟩ := hs.numerator
    have hh : a.bits.head?.isSome = decide (a ≠ 0) := by
      by_cases ha : a = 0
      · simp [ha]
      · cases he : a.bits with
        | nil =>
          have hv := address_bits a
          simp [he,addressValue] at hv
          exact False.elim (ha hv.symm)
        | cons bit tail => simp [ha]
    simpa [signedState,Store.ofState,readTapeState,BitRAMState.setRegister,ho,hsgn] using
      congrArg (fun b => negative && b) hh
  · intro i _ h23 _ _ _ _ _ h80 h81
    simp [signedState,Store.ofState,readTapeState,BitRAMState.setRegister,h23,h80,h81]

/-- Fixed finite gcd, exact division, sign normalization, and serialization. -/
def code : Code := .seq signCode (.seq normalizeCode emitCode)
def program : BitRAM := code.compile

def costBound (a b : ℕ) : ℕ := normalizeBudget a b + 26*(a.size+b.size)+63

theorem executes (input : List Bool) (tape : ℕ → Bool) (negative : Bool) (a b : ℕ)
    (hb : 0 < b) (s : Store) (hs : NormalizeReady s.val a b)
    (hsgn : s.val.registers 23 = negative) :
    ∃ cost t, cost ≤ costBound a b ∧ Executes input tape code cost s t ∧
      t.val.output = (Codec.rat (value negative a b)).reverse ++ s.val.output ∧
      NormalizeReady t.val a b ∧ EmitFrame s.val t.val := by
  obtain ⟨e1,s1,g1,o1,f1⟩ := sign input tape negative a b s hs hsgn
  obtain ⟨c,u,hc,e2,n2,d2,s2,f2⟩ := normalize input tape a b hb (signedState s) s1
  have hg2 : u.val.registers 23 = decide ((value negative a b).num < 0) := by
    rw [f2.registers 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),g1]
    exact (value_sign negative a b hb).symm
  obtain ⟨t,e3,o3,s3,f3⟩ := emit input tape (value negative a b) a b u
    (by simpa only [value_num_natAbs negative a b hb] using n2)
    (by simpa only [value_den negative a b hb] using d2) hg2 s2
  refine ⟨5+(c+(26*((value negative a b).num.natAbs.bits.length+
      (value negative a b).den.bits.length)+58)),t,?_,e1.seq (e2.seq e3),?_,s3,
      f1.trans ((EmitFrame.ofNormalize f2).trans f3)⟩
  · rw [value_num_natAbs negative a b hb,value_den negative a b hb]
    have hn := Nat.size_le_size (Nat.div_le_self a (Nat.gcd a b))
    have hd := Nat.size_le_size (Nat.div_le_self b (Nat.gcd a b))
    simp only [Nat.size_eq_bits_len]
    unfold costBound
    omega
  · rw [o3,f2.output,o1]

theorem costBound_polynomial (a b : ℕ) :
    costBound a b ≤ 100000*(a.size+b.size+2)^3 := by
  let B := a.size+b.size
  have hb : b.size ≤ B := by omega
  have hm := Nat.mul_le_mul_right (2000*(2*B+2)^2+4) (Nat.mul_le_mul_left 2 hb)
  unfold costBound normalizeBudget
  change 4+2*b.size*(2000*(2*B+2)^2+4)+4000*(2*B+2)^2+100*(B+2)+26*B+63 ≤ _
  change 4+2*b.size*(2000*(2*B+2)^2+4)+4000*(2*B+2)^2+100*(B+2)+26*B+63 ≤ 100000*(B+2)^3
  nlinarith [Nat.zero_le (B^3),Nat.zero_le (B^2)]

theorem run (input : List Bool) (tape : ℕ → Bool) (negative : Bool) (a b : ℕ)
    (hb : 0 < b) (s : Store) (hs : NormalizeReady s.val a b)
    (hsgn : s.val.registers 23 = negative) :
    ∃ t, (runPriced (program.next input tape) (costBound a b+1) s.val).finished = some t ∧
      t.output = (Codec.rat (value negative a b)).reverse ++ s.val.output ∧
      NormalizeReady t a b ∧ EmitFrame s.val t := by
  obtain ⟨c,t,hc,he,ho,hr,hf⟩ := executes input tape negative a b hb s hs hsgn
  have er := he.compiled_run (costBound a b+1) (by omega)
  exact ⟨t.place code.size,er.1,ho,
    ⟨hr.numerator,hr.denominator,
      ⟨hr.work.first,hr.work.second,hr.work.quotient,hr.work.remainder,hr.work.scratch⟩,
      hr.outputNumerator,hr.outputDenominator⟩,
    ⟨hf.address,hf.memory,hf.inputHead,hf.randomCursor,hf.tapes,hf.registers⟩⟩

end Maxwell.Cost.RationalCanonical
