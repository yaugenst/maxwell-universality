import Maxwell.Cost.RationalCanonical.Normalize
import Maxwell.Cost.EmitNatural

namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

/-- Output changes are specified by the exact byte equation, independently
of the preserved input, random, memory, and persistent tape channels. -/
structure EmitFrame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i, i ∉ ({0,1,2,3,4,220,221,222,223,228,229,230,231} : Finset ℕ) →
    t.tapes i = s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 →
    i ≠ 80 → i ≠ 81 → t.registers i = s.registers i

theorem EmitFrame.trans {s t u : BitRAMState} (h : EmitFrame s t) (k : EmitFrame t u) :
    EmitFrame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi),
    fun i hi h23 h24 h25 h26 h27 h28 h80 h81 =>
      (k.registers i hi h23 h24 h25 h26 h27 h28 h80 h81).trans
      (h.registers i hi h23 h24 h25 h26 h27 h28 h80 h81)⟩

theorem EmitFrame.ofNormalize {s t : BitRAMState} (h : NormalizeFrame s t) : EmitFrame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.tapes,
    fun i hi _ h24 h25 h26 h27 _ h80 h81 => h.registers i hi h24 h25 h26 h27 h80 h81⟩

def emitCode : Code :=
  .seq (.atom (.output 23)) <|
  .seq (EmitNatural.code 230) <|
  .seq (EmitNatural.code 231) <|
  .seq (.call (TapeOps.clear 230)) (.call (TapeOps.clear 231))

/-- The rational-pair serializer consumes actual canonical numerator and
denominator words and clears both output banks for its next invocation. -/
theorem emit (input : List Bool) (tape : ℕ → Bool) (q : ℚ) (a b : ℕ) (s : Store)
    (hnum : Word s.val 230 q.num.natAbs) (hden : Word s.val 231 q.den)
    (hsign : s.val.registers 23 = decide (q.num < 0)) (hs : NormalizeDone s.val a b) :
    ∃ t, Executes input tape emitCode (26*(q.num.natAbs.bits.length+q.den.bits.length)+58) s t ∧
      t.val.output = (Codec.rat q).reverse ++ s.val.output ∧
      NormalizeReady t.val a b ∧ EmitFrame s.val t.val := by
  let u : Store := Store.ofState {s.val with pc := 1,output := s.val.registers 23 :: s.val.output}
  have e1 : Executes input tape (.atom (.output 23)) 2 s u := Executes.output input tape s 23
  obtain ⟨no,hn⟩ := hnum
  obtain ⟨do_,hd⟩ := hden
  obtain ⟨v,e2,o2,f2,r2⟩ := EmitNatural.executes_with_registers 230 q.num.natAbs no input tape u hn
  obtain ⟨w,e3,o3,f3,r3⟩ := EmitNatural.executes_with_registers 231 q.den do_ input tape v
    ((congrFun f2.2.2.2.2 231).trans hd)
  have htapes : w.val.tapes = s.val.tapes := f3.2.2.2.2.trans f2.2.2.2.2
  obtain ⟨x,e4,z4,f4⟩ := clear_word 230 q.num.natAbs input tape w
    (word_of_eq (congrFun htapes 230) ⟨no,hn⟩)
  have F4 := transferFrame 230 230 f4
  obtain ⟨t,e5,z5,f5⟩ := clear_word 231 q.den input tape x
    (F4.word (by decide) (word_of_eq (congrFun htapes 231) ⟨do_,hd⟩))
  have F5 := transferFrame 231 231 f5
  have ff := F4.trans F5
  have fbefore : EmitFrame s.val w.val := by
    refine ⟨f3.1.trans f2.1,f3.2.2.1.trans f2.2.2.1,f3.2.1.trans f2.2.1,
      f3.2.2.2.1.trans f2.2.2.2.1,fun i _ => congrFun htapes i,?_⟩
    intro i _ _ h24 h25 h26 h27 h28 _ _
    exact (r3 i h24 h25 h26 h27 h28).trans (r2 i h24 h25 h26 h27 h28)
  refine ⟨t,?_,?_,?_,fbefore.trans (EmitFrame.ofNormalize (NormalizeFrame.ofDivision ff (by decide)))⟩
  · convert e1.seq (e2.seq (e3.seq (e4.seq e5))) using 1 <;> first | rfl | omega
  · rw [ff.output,o3,o2]
    simp only [u,Store.ofState,hsign,Codec.rat,Codec.int,List.reverse_append,List.reverse_cons]
    simp only [List.append_assoc,List.singleton_append]
  · refine ⟨ff.word (by decide) (word_of_eq (congrFun htapes 228) hs.numerator),
      ff.word (by decide) (word_of_eq (congrFun htapes 229) hs.denominator),
      ⟨ff.word (by decide) (word_of_eq (congrFun htapes 220) hs.work.first),
       ff.word (by decide) (word_of_eq (congrFun htapes 221) hs.work.second),
       ff.blank (by decide) (blank_of_eq (congrFun htapes 222) hs.work.quotient),
       ff.blank (by decide) (blank_of_eq (congrFun htapes 223) hs.work.remainder),?_⟩,
      F5.blank (by decide) ((zero_word_iff_blank _ _).mp z4),
      (zero_word_iff_blank _ _).mp z5⟩
    intro i hi
    exact ff.blank (by simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]; omega)
      (blank_of_eq (congrFun htapes i) (hs.work.scratch i hi))

end Maxwell.Cost.RationalCanonical
